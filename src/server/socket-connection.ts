import { Socket } from 'socket.io';
import * as db from './db';
import Container, { ContainerExitNotification } from './container';
import {
    ContainerInfo,
    ResizeEventBody,
    RunEventBody,
    DebugNextBody,
    DebugProceedBody,
    DebugRemoveBreakpointBody,
    DebugSetBreakpointBody,
    DebugStepInBody,
    DebugStepOutBody,
} from '../common/communication';
import {
    SUPPORTED_VERSIONS,
    FLAG_WHITELIST,
    DEFAULT_VERSION,
    Compiler,
} from '../common/constants';
import { ClientValidationError, DebugStateError } from './error';
import { getSourceIpFromSocket, getUserAgentFromSocket } from './util';

async function getRunParams(request: RunEventBody): Promise<{
    compiler: Compiler;
    cflags: string;
    code: string;
    argsStr: string;
    includeFileId: string | null;
    includeFileData: Buffer | null;
    debug: boolean;
    breakpoints: number[];
}> {
    const lang = SUPPORTED_VERSIONS.includes(request.language)
        ? request.language : DEFAULT_VERSION;
    const compiler = ['C99', 'C11'].indexOf(lang) > -1
        ? 'gcc' : 'g++';

    const suppliedCflags = (Array.isArray(request.flags) ? request.flags : []).filter(
        (flag: string) => FLAG_WHITELIST.includes(flag),
    );
    if (suppliedCflags.length !== (request.flags || []).length) {
        console.warn(`Warning: someone passed non-whitelisted flags! ${
            request.flags}`);
    }
    const cflags = (`-std=${lang.toLowerCase()} ${suppliedCflags.join(' ')}`).trim();
    if (cflags.length > db.CFLAGS_MAX_LEN) {
        throw new ClientValidationError('Submitted cflags exceeds max length!');
    }

    const code = request.code || '';
    if (code.length > db.CODE_MAX_LEN) {
        throw new ClientValidationError('Submitted code exceeds max length!');
    }

    const argsStr = request.args || '';
    if (argsStr.length > db.ARGS_MAX_LEN) {
        throw new ClientValidationError('Submitted args exceed max length!');
    }

    const includeFileData = request.includeFileId
        ? await db.getFileContents(request.includeFileId)
        : null;
    if (request.includeFileId && includeFileData === null) {
        throw new ClientValidationError('includeFileId is invalid');
    }
    const includeFileId = includeFileData === null ? null : request.includeFileId;

    const breakpoints = Array.isArray(request.breakpoints) ? request.breakpoints : [];
    const debug = Boolean(request.debug);
    if (!debug && breakpoints.length > 0) {
        throw new ClientValidationError(
            'Breakpoints are specified even though debugging is not enabled',
        );
    }

    return {
        compiler, cflags, code, argsStr, includeFileId, includeFileData, debug, breakpoints,
    };
}

export default class SocketConnection {
    private readonly sourceIP: string;
    private readonly sourceUA: string;
    private readonly logPrefix: string;

    private readonly socket: Socket;
    private container: Container | null = null;
    private runId: number;

    constructor(socket: Socket, logPrefix: string) {
        this.sourceIP = getSourceIpFromSocket(socket);
        this.sourceUA = getUserAgentFromSocket(socket);
        this.logPrefix = logPrefix;
        this.socket = socket;

        console.info(`${this.logPrefix}Websocket connection received from ${this.sourceIP}`);

        // Forward input from websocket to container stdin
        socket.on('data', this.onStdinReceived);
        socket.on('run', this.startContainer);
        socket.on('resize', this.onTerminalResize);
        socket.on('disconnect', this.onSocketDisconnect);

        // Handle debug commands
        socket.on('debugSetBreakpoint', this.makeDebugHandler(
            (data: DebugSetBreakpointBody) => this.container.gdbSetBreakpoint(data.line),
        ));
        socket.on('debugRemoveBreakpoint', this.makeDebugHandler(
            (data: DebugRemoveBreakpointBody) => this.container.gdbRemoveBreakpoint(data.line),
        ));
        socket.on('debugProceed', this.makeDebugHandler(
            (data: DebugProceedBody) => this.container.gdbProceed(data.threadId),
        ));
        socket.on('debugStepIn', this.makeDebugHandler(
            (data: DebugStepInBody) => this.container.gdbStepIn(data.threadId),
        ));
        socket.on('debugStepOut', this.makeDebugHandler(
            (data: DebugStepOutBody) => this.container.gdbStepOut(data.threadId),
        ));
        socket.on('debugNext', this.makeDebugHandler(
            (data: DebugNextBody) => this.container.gdbNext(data.threadId),
        ));
    }

    private startContainer = async (request: RunEventBody): Promise<void> => {
        if (this.container) {
            console.warn(`${this.logPrefix}Got run command even though we `
                + 'already have a container running');
            return;
        }
        const rows = request.rows || 24;
        const cols = request.cols || 80;

        // Parse info from run request
        let compiler: Compiler;
        let cflags: string;
        let code: string;
        let argsStr: string;
        let includeFileId: string;
        let includeFileData: Buffer;
        let debug: boolean;
        let breakpoints: number[];
        try {
            ({
                compiler, cflags, code, argsStr, includeFileId, includeFileData, debug, breakpoints,
            } = await getRunParams(request));
        } catch (e) {
            console.error(`${this.logPrefix}Failed to get valid run params!`);
            console.error(e);
            // TODO: send client an explanation
            // Hang up:
            this.socket.disconnect();
            return;
        }

        // Log to db and start running the container
        db.insertProgram(
            compiler, cflags, code, argsStr, includeFileId, this.sourceIP, this.sourceUA,
        ).then((row) => {
            console.log(`${this.logPrefix}Program is at alias ${row.alias}`);
            return Promise.all([row.alias, db.createRun(row.id, this.sourceIP, this.sourceUA)]);
        }).then(([alias, runId]) => {
            this.runId = runId;
            console.log(`${this.logPrefix}Run logged with ID ${this.runId}`);
            this.socket.emit('saved', alias);
            this.container = new Container(
                this.logPrefix, code, includeFileData, compiler, cflags, argsStr, rows, cols,
                debug, breakpoints,
                this.onContainerOutput, this.onContainerExit, this.onDebugInfo,
            );
        });
    };

    private onStdinReceived = (data: string): void => {
        // Forward input from websocket to container stdin
        if (this.container) {
            this.container.onInput(data);
        }
    };

    private onContainerOutput = (data: string): void => {
        this.socket.emit('data', Buffer.from(data));
    };

    private onDebugInfo = (data: ContainerInfo): void => {
        this.socket.emit('debug', data);
    };

    private onTerminalResize = (data: ResizeEventBody): void => {
        console.log(`${this.logPrefix}Resize info received: ${data.rows}x${data.cols}`);
        if (this.container) {
            this.container.resize(data.rows, data.cols);
        }
    };

    private onSocketDisconnect = (): void => {
        console.info(`${this.logPrefix}Client disconnected`);
        if (this.container) {
            this.container.shutdown();
        }
    };

    private onContainerExit = (data: ContainerExitNotification): void => {
        if (this.socket.connected) {
            console.log(`${this.logPrefix}Sending client exit info`);
            this.socket.emit('exit', { code: data.exitStatus, signal: data.signal });
            console.log(`${this.logPrefix}Closing socket`);
            this.socket.disconnect();
        }

        // Log the running time and output
        db.updateRun(this.runId, data.runtimeMs, data.exitStatus, data.output);
        this.container = null;
    };

    private makeDebugHandler = <T>(executeCommand: (data: T) => void): ((data: T) => void) => (
        (data: T): void => {
            if (!this.container) {
                this.socket.emit('cplaygroundError', {
                    error: 'No program is currently running.',
                });
            } else {
                try {
                    executeCommand(data);
                } catch (e) {
                    if (e instanceof DebugStateError) {
                        this.socket.emit('cplaygroundError', {
                            error: e.message,
                        });
                    }
                }
            }
        }
    );
}
