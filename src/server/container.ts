import * as path from 'path';
import * as fs from 'fs';
import * as net from 'net';
import * as os from 'os';
import * as childProcess from 'child_process';
import * as stringArgv from 'string-argv';
import uuidv4 from 'uuid/v4';
import * as ptylib from 'node-pty';
import semver from 'semver';
import * as readline from 'readline';
import { GDB, Breakpoint, Thread, ThreadGroup } from 'gdb-js';
// Import regeneratorRuntime as a global to fix errors in gdb-js:
// eslint-disable-next-line import/extensions
import 'regenerator-runtime/runtime.js';

import * as db from './db';
import * as debugging from './debugging';
import { ContainerInfo } from '../common/communication';
import { Compiler } from '../common/constants';
import { getPathFromRoot } from './util';
import { DebugStateError, SystemConfigurationError } from './error';

// eslint-disable-next-line no-undef
import Timeout = NodeJS.Timeout;

// How long should a program run for?
const DEFAULT_TIMEOUT = 90000;
// A program's timeout timer can be reset by I/O (e.g. so that if you're testing
// a shell, it doesn't get killed after only a minute), but can't exceed this time
const HARD_TIMEOUT = 480000;
// Prevent forkbombs and bitcoin mining:
const MAX_CPU_TIME = 15000;

const OUTPUT_BUFFER_MAX_LEN = db.OUTPUT_MAX_LEN;

export type ContainerExitNotification = {
    runtimeMs: number;
    exitStatus: number;
    signal: number;
    output: string;
}

export default class Container {
    private readonly logPrefix: string;

    private readonly containerName = uuidv4();
    private containerId: string | null = null;
    private containerPid: number | null = null;
    private readonly startTime = process.hrtime();
    private pty: ptylib.IPty | null = null;
    private exited = false;
    private terminalWidth: number = null;

    private readonly dataHostPath = getPathFromRoot('data');
    private readonly codeHostPath = path.join(this.dataHostPath, this.containerName);
    private readonly includeFileHostPath = path.join(this.dataHostPath, `${this.containerName}-include.zip`);
    private readonly codeContainerPath: string;

    private gdbSocketPath: string | null = null;
    private gdbMiServer: net.Server | null = null;
    private gdb: GDB | null = null;

    private readonly initialBreakpoints: number[];
    private breakpoints: {[line: number]: Breakpoint} = {};
    private threads: {[threadId: number]: Thread} = {};
    private processes: {[inferiorId: number]: ThreadGroup} = {};

    private readonly externalOutputCallback: (data: string) => void;
    private readonly externalExitCallback: (data: ContainerExitNotification) => void;
    private readonly externalDebugCallback: (data: ContainerInfo) => void;

    private runTimeoutTimer: Timeout | null = null;
    private cpuQuotaMonitor: Timeout | null = null;
    private debuggingMonitor: Timeout | null = null;

    // Save container output to a buffer that can later be committed to the database
    private outputBuf = '';
    private warnOutputMaxSizeExceeded = true;

    constructor(
        logPrefix: string,
        code: string,
        includeFileData: Buffer | null,
        compiler: Compiler,
        cflags: string,
        argsStr: string,
        rows: number,
        cols: number,
        enableDebugging: boolean,
        breakpoints: number[],
        onOutput: (data: string) => void,
        onExit: (data: ContainerExitNotification) => void,
        onDebugInfo: (data: ContainerInfo) => void,
    ) {
        // Validate debug config. (NOTE: make sure all validation is done before
        // this.saveCodeFiles, so that we don't leak resources on exception.)
        if (!enableDebugging && breakpoints.length > 0) {
            throw new DebugStateError('Debugging is not enabled, yet breakpoints are specified');
        }

        this.logPrefix = logPrefix;
        this.terminalWidth = cols;
        this.externalOutputCallback = onOutput;
        this.externalExitCallback = onExit;
        this.externalDebugCallback = onDebugInfo;
        this.initialBreakpoints = breakpoints;

        // Save the code to disk so that the files can be mounted into the container
        this.saveCodeFiles(code, includeFileData);

        const fileExtension = compiler === 'gcc' ? '.c' : '.cpp';
        this.codeContainerPath = `/cplayground/code${fileExtension}`;

        // Add -g flag to compiler if debugging is enabled. (Otherwise, the compiler won't
        // generate a symbol table for the debugger to use.)
        const debugAwareCflags = enableDebugging ? `-g ${cflags}` : cflags;
        // Set up debug socket, if applicable; then, start the container
        (enableDebugging ? this.initializeDebugSocket() : Promise.resolve()).then(() => {
            this.startContainer(compiler, debugAwareCflags, argsStr, rows, cols, enableDebugging)
                .then();
        });
    }

    private saveCodeFiles = (code: string, includeFileData: Buffer | null): void => {
        // Create data directory and save code from request
        console.log(`${this.logPrefix}Saving code to ${this.codeHostPath}`);
        fs.access(this.dataHostPath, fs.constants.F_OK, (errPathExists) => {
            if (errPathExists) {
                fs.mkdir(this.dataHostPath, (err) => { if (err) throw err; });
            }
        });
        fs.writeFile(this.codeHostPath, code, (err) => {
            if (err) throw err;
            console.log(`${this.logPrefix}Saved file to ${this.codeHostPath}`);
        });
        if (includeFileData) {
            console.log(`${this.logPrefix}Writing include file to ${this.includeFileHostPath}`);
            fs.writeFile(this.includeFileHostPath, includeFileData, (err) => {
                if (err) throw err;
                console.log(`${this.logPrefix}Saved file to ${this.includeFileHostPath}`);
            });
        }
    };

    /**
     * Set up Unix domain socket that can be bind-mounted into the container, so that we can
     * communicate with gdb (running inside the container)
     */
    private initializeDebugSocket = (): Promise<void> => {
        this.gdbSocketPath = path.join(this.dataHostPath, `${this.containerName}-gdb.sock`);
        this.gdbMiServer = net.createServer(this.onGdbSocketConnection);
        return new Promise((resolve) => {
            this.gdbMiServer.listen(this.gdbSocketPath, () => {
                resolve();
            });
        }).then(
            // TODO: figure out a way to allow access from the container's user (uid 999)
            //  without allowing access to *all* users. Keep in mind that we don't know what the
            //  host's uid is at compile time.
            () => fs.promises.chmod(this.gdbSocketPath, '777'),
        ).then(() => {
            console.log(`${this.logPrefix}Successfully created gdb socket at ${
                this.gdbSocketPath}`);
        });
    };

    private generateDockerRunArgs = async (
        compiler: Compiler, cflags: string, argsStr: string,
    ): Promise<string[]> => {
        const runArgs = [
            '-it', '--name', this.containerName,
            // Make the entire FS read-only, except for the home directory
            // /cplayground, which we impose a 32MB storage quota on.
            // NOTE: In the future, it may be easier to impose a disk quota
            // using the --storage-opt flag. However, this currently requires
            // use of a specific storage driver and backing filesystem, and
            // it's too complicated to set up on the host. Links for future
            // reference:
            // https://forums.docker.com/t/./37653
            // https://github.com/machinelabs/machinelabs/issues/703
            '--read-only',
            '--tmpfs', '/cplayground:mode=0777,size=32m,exec',
            // Add the code to the container and set options
            '-v', `${this.codeHostPath}:${this.codeContainerPath}:ro`,
            '-v', `${this.includeFileHostPath}:/cplayground/include.zip:ro`,
            '-e', `COMPILER=${compiler}`,
            '-e', `CFLAGS=${cflags}`,
            '-e', `SRCPATH=${this.codeContainerPath}`,
            // Drop all capabilities. (We add back the ptrace capability if debugging is enabled)
            '--cap-drop=all',
            // Set more resource limits and disable networking
            '--memory', '96mb',
            '--memory-swap', '128mb',
            '--memory-reservation', '32mb',
            '--cpu-shares', '512',
            '--pids-limit', '16',
            '--ulimit', 'cpu=10:11',
            '--ulimit', 'nofile=64',
            '--network', 'none',
        ];
        // If debugging is enabled, set up for gdb
        if (this.gdbSocketPath) {
            // Bind mount the gdb socket so that we can communicate with gdb
            runArgs.push('-v', `${this.gdbSocketPath}:/gdb.sock`);
            // Make sure it's safe to use ptrace
            if (os.platform() !== 'linux' || semver.lt(semver.coerce(os.release()), '4.8.0')) {
                throw new SystemConfigurationError('ptrace is not safe to use on linux versions '
                    + 'older than 4.8, as it can be used to bypass seccomp.');
            }
            // Docker itself runs the above check too, and grants the ptrace syscall in its seccomp
            // profile (without granting the dangerous CAP_SYS_PTRACE) on kernel versions past 4.8,
            // meaning we need not do anything to give gdb the perms it needs

            // Tell run.py to run in debug mode
            runArgs.push('-e', 'CPLAYGROUND_DEBUG=1');
        }

        return ['run',
            ...runArgs,
            'cplayground', '/run.py',
        ].concat(
            // Safely parse argument string from user
            stringArgv.parseArgsStringToArgv(argsStr),
        );
    };

    private startContainer = async (
        compiler: Compiler, cflags: string, argsStr: string, rows: number, cols: number,
        enableDebugging: boolean,
    ): Promise<void> => {
        // Start the container
        // TODO: clean up container/files even if the server crashes
        const dockerRunArgs = await this.generateDockerRunArgs(compiler, cflags, argsStr);
        console.log(`${this.logPrefix}Starting container: docker ${dockerRunArgs.join(' ')}`);
        console.log(`${this.logPrefix}Initial terminal size ${rows}x${cols}`);
        this.pty = ptylib.spawn('docker', dockerRunArgs, {
            name: 'xterm-color',
            rows,
            cols,
        });
        this.pty.onData(this.onOutput);
        this.pty.onExit(this.onExit);

        // Start resource limit timers
        this.setRunTimeoutMonitor();
        this.setCpuQuotaMonitor();
        if (enableDebugging) {
            this.setDebuggingMonitor();
        } else {
            console.info(
                `${this.logPrefix}Debugging is disabled. "debug" events will not be sent to the client.`,
            );
        }
    };

    private trySettingContainerId = async (): Promise<void> => new Promise((resolve) => (
        childProcess.execFile('docker',
            ['ps', '--no-trunc', '-aqf', `name=${this.containerName}`],
            (err, out) => {
                if (err) throw err;
                this.containerId = out.trim();
                console.log(`${this.logPrefix}Container id: ${this.containerId}`);
                resolve();
            })
    ));

    private setContainerPid = async (): Promise<void> => {
        if (!this.containerId) {
            await this.trySettingContainerId();
        }
        const pidFile = `/sys/fs/cgroup/pids/docker/${this.containerId}/cgroup.procs`;
        console.log(`${this.logPrefix}Looking up container pid`);

        const stream = fs.createReadStream(pidFile);
        stream.on('error', (err) => {
            if (err.code === 'ENOENT') {
                console.log(`Note: file ${pidFile} has disappeared. This is probably `
                    + 'okay; the container probably just exited.');
            } else {
                console.error(`Unexpected error reading ${pidFile}:`, err);
            }
        });
        const rl = readline.createInterface({
            input: stream,
        });
        for await (const line of rl) {
            this.containerPid = parseInt(line, 10);
            rl.close();
            break;
        }
        console.log(`${this.logPrefix}Container pid set: ${this.containerPid}`);
    };

    private onOutput = async (data: string): Promise<void> => {
        // Get container ID. This is jank, but this is the best way to set the container ID
        // that I could come up with. ptylib.spawn() above initiates the container launch, but
        // there's no way to tell that docker has actually finished creating the container until
        // the container starts printing stuff. So, if we get here, we know it's safe to query
        // the container ID.
        if (!this.containerId) {
            this.trySettingContainerId();
        }

        // Store output
        if (this.outputBuf.length + data.length < OUTPUT_BUFFER_MAX_LEN) {
            this.outputBuf += data;
        } else if (this.warnOutputMaxSizeExceeded) {
            console.warn(`${this.logPrefix}Program output exceeded max length for db storage!`);
            this.warnOutputMaxSizeExceeded = false;
        }

        // Report outputted data
        this.externalOutputCallback(data);
    };

    private onExit = ({ exitCode, signal }: {exitCode: number; signal: number}): void => {
        this.exited = true;
        const runtime = this.getContainerRunTimeMs();
        console.info(`${this.logPrefix}Container exited! Status ${exitCode}, signal ${signal}, `
            + `node-side runtime measured at ${runtime}ms`);

        clearTimeout(this.runTimeoutTimer);
        clearInterval(this.cpuQuotaMonitor);
        clearInterval(this.debuggingMonitor);
        // Remove uploaded file. We don't care about errors, in case the file
        // was already removed (or was never successfully created to begin
        // with)
        fs.unlink(this.codeHostPath, () => {
            console.log(`${this.logPrefix}Deleted ${this.codeHostPath}`);
        });
        fs.unlink(this.includeFileHostPath, () => {
            console.log(`${this.logPrefix}Deleted ${this.includeFileHostPath}`);
        });
        // Shut down gdb server, if it's running
        if (this.gdbMiServer) {
            this.gdbMiServer.close();
        }

        this.externalExitCallback({
            runtimeMs: runtime,
            exitStatus: exitCode,
            signal,
            output: this.outputBuf,
        });
    };

    private showErrorBanner = (text: string): void => {
        // Note: if you modify these constants, be sure to update run.py to
        // match
        const fg = '\x1b[91m'; // red
        const bg = '\x1b[100m'; // light gray

        const bannerWidth = Math.max(this.terminalWidth, text.length);
        const lpad = ' '.repeat(Math.floor((bannerWidth - text.length) / 2));
        const rpad = ' '.repeat(Math.ceil((bannerWidth - text.length) / 2));
        this.externalOutputCallback(`${fg + bg + lpad + text + rpad}\x1b[0m`);
    };

    private getContainerRunTimeMs = (): number => {
        const runtimeHt = process.hrtime(this.startTime);
        return runtimeHt[0] * 1000 + runtimeHt[1] / 1000000;
    };

    private onGdbSocketConnection = async (sock: net.Socket): Promise<void> => {
        console.log(`${this.logPrefix}Received connection on gdb socket`);
        this.gdb = new GDB({
            stdin: sock,
            stdout: sock,
            stderr: sock,
        });
        // gdb-js adds an error listener that terminates our node server if an error occurs on
        // the socket. This is obviously bad... Let's replace it
        sock.removeAllListeners('error');
        sock.on('error', (err) => {
            console.warn('Error on gdb socket: ', err);
            sock.destroy();
            sock.unref();
        });
        this.gdb.on('notify', async (e) => {
            console.debug(`${this.logPrefix}[gdb] event: notify`, e);
            // Quit gdb once thread 1 exits. (We do this since cplayground terminates the
            // container after the main process exits when running in non-debug mode.)
            if (e.state === 'thread-group-exited' && e.data.id === 'i1') {
                // Inferior 1 has exited
                if (e.data['exit-code'] !== undefined) {
                    // Process exited normally
                    await this.gdb.execCLI(`quit ${e.data['exit-code']}`);
                } else {
                    // If the exit code is undefined, we assume the process was signalled.
                    // Unfortunately, gdb doesn't provide the signal in the thread-group-exited
                    // event (it appears in the stopped event but it's kind of complicated to get),
                    // so we rely on the gdb $_exitsignal variable. This could cause a race
                    // condition if a second inferior were to be killed after the delivery of
                    // this event but before we send the quit command (since $_exitsignal would
                    // contain that inferior's signal), but the likelihood of this is small
                    // enough that we won't worry about it for now.
                    await this.gdb.execCLI('quit 128 + $_exitsignal');
                }
            }
        });
        this.gdb.on('exec', (e) => {
            console.debug(`${this.logPrefix}[gdb] event: exec`, e);
        });
        this.gdb.on('stopped', (e) => {
            console.debug(`${this.logPrefix}[gdb] event: stopped`, e);
            // Update thread status and frame. We don't replace the whole thread object because
            // the thread group isn't included in the thread info for these events, so if we do
            // that, we would lose track of which threads below to which processes.
            if (e.thread) {
                this.threads[e.thread.id].status = e.thread.status;
                this.threads[e.thread.id].frame = e.thread.frame;
            }
            // Send the client an update. (Reset the debugging monitor so that we don't
            // inadvertently send two updates in quick succession, which is unnecessary.)
            this.reportDebugInfo().then(this.setDebuggingMonitor);
        });
        this.gdb.on('running', (e) => {
            console.debug(`${this.logPrefix}[gdb] event: running`, e);
            // Update thread status and frame
            if (e.thread) {
                this.threads[e.thread.id].status = e.thread.status;
                this.threads[e.thread.id].frame = e.thread.frame;
            }
            // Send the client an update. (Reset the debugging monitor so that we don't
            // inadvertently send two updates in quick succession, which is unnecessary.)
            this.reportDebugInfo().then(this.setDebuggingMonitor);
        });
        this.gdb.on('thread-created', (thread: Thread) => {
            console.debug(`${this.logPrefix}[gdb] event: thread-created`, thread);
            this.threads[thread.id] = thread;
        });
        this.gdb.on('thread-exited', (thread: Thread) => {
            console.debug(`${this.logPrefix}[gdb] event: thread-exited`, thread);
            delete this.threads[thread.id];
        });
        this.gdb.on('thread-group-started', (group: ThreadGroup) => {
            console.debug(`${this.logPrefix}[gdb] event: thread-group-started`, group);
            this.processes[group.id] = group;
        });
        this.gdb.on('thread-group-exited', (group: ThreadGroup) => {
            console.debug(`${this.logPrefix}[gdb] event: thread-group-exited`, group);
            delete this.processes[group.id];
        });
        this.gdb.logStream.on('data', (e) => {
            console.debug(`${this.logPrefix}[gdb] log message`, e);
        });
        await this.gdb.init();
        await this.gdb.enableAsync();
        await this.gdb.attachOnFork();

        // Set and save initial breakpoints
        const initialBreakpointObjs = await Promise.all(this.initialBreakpoints.map(
            (lineno) => this.gdb.addBreak(this.codeContainerPath, lineno),
        ));
        initialBreakpointObjs.forEach((bp) => { this.breakpoints[bp.line] = bp; });
        console.debug(`${this.logPrefix}Set ${initialBreakpointObjs.length} initial breakpoints`,
            initialBreakpointObjs);

        // Go!
        console.debug(`${this.logPrefix}Issuing run command!`);
        await this.gdb.run();
    };

    /**
     * Kill the container if it doesn't finish running within DEFAULT_TIMEOUT ms
     */
    private setRunTimeoutMonitor = (): void => {
        // If there is already a timer running, stop it so we can reset it
        if (this.runTimeoutTimer !== null) {
            clearTimeout(this.runTimeoutTimer);
        }
        // Set the execution timeout timer to DEFAULT_TIMEOUT ms. If doing so would exceed the
        // HARD_TIMEOUT limit, then reset it to as long as we can without exceeding HARD_TIMEOUT.
        this.runTimeoutTimer = setTimeout(() => {
            console.warn(`${this.logPrefix}Container ${this.containerName} hasn't finished `
                + 'running in time! Killing container');
            childProcess.execFile('docker', ['kill', this.containerName]);
            this.showErrorBanner('The program took too long to run.');
        }, Math.min(HARD_TIMEOUT - this.getContainerRunTimeMs(), DEFAULT_TIMEOUT));
    };

    /**
     * Every second, check if this container has exceeded the max amount of CPU time. (I did a
     * lot of research, and at least at the time I'm writing this, there's no way to set a max
     * cpu limit on an entire cgroup. You can set a max cpu time on individual processes, but
     * that doesn't help when mitigating forkbombs.
     */
    private setCpuQuotaMonitor = (): void => {
        // If there is already a timer running, stop it so we can reset it
        if (this.cpuQuotaMonitor !== null) {
            clearInterval(this.cpuQuotaMonitor);
        }
        // Set timer
        this.cpuQuotaMonitor = setInterval(() => {
            // If we don't have the containerId yet, the container might not
            // have started yet, and there's not much we can do
            if (!this.containerId) return;

            fs.readFile(
                `/sys/fs/cgroup/cpu/docker/${this.containerId}/cpuacct.usage`,
                (err, data) => {
                    if (err) {
                        console.warn(`${this.logPrefix}Error loading cgroup CPU usage!`, err);
                        return;
                    }

                    const cpuUsageNs = parseInt(data.toString(), 10);
                    const cpuUsageMs = cpuUsageNs / 1000000;
                    console.debug(`${this.logPrefix}Current CPU time used: ${cpuUsageMs}ms`);
                    if (cpuUsageMs > MAX_CPU_TIME) {
                        console.warn(`${this.logPrefix}Container ${this.containerName} exceeded its CPU `
                            + 'quota! Killing container');
                        childProcess.execFile('docker', ['kill', this.containerName]);
                        this.showErrorBanner('The program exceeded its CPU quota.');
                    }
                },
            );
        }, 1000);
    };

    private reportDebugInfo = async (): Promise<void> => {
        if (!this.containerId) {
            // If the container ID hasn't been set yet, there isn't much we can do
            return;
        }
        if (!this.containerPid) {
            await this.setContainerPid();
        }
        const info = await debugging.getContainerInfo(
            this.containerPid, Object.values(this.processes), Object.values(this.threads),
        );
        if (info) {
            this.externalDebugCallback(info);
        } else {
            console.warn(
                `${this.logPrefix}Container is running but has no debugging info available`,
            );
        }
    };

    private setDebuggingMonitor = (): void => {
        // If there is already a timer running, stop it so we can reset it
        if (this.debuggingMonitor !== null) {
            clearInterval(this.debuggingMonitor);
        }
        // If the container already finished running, no reason to start another timer
        if (this.exited) {
            return;
        }
        // Every second, get info about the container's processes and send to the client.
        this.debuggingMonitor = setInterval(this.reportDebugInfo, 1000);
    };

    onInput = (data: string): void => {
        // Reset the timeout monitor. (We extend the timeout on input for people testing things
        // like games or shells.)
        this.setRunTimeoutMonitor();
        // Send input to container
        if (this.pty) {
            this.pty.write(data);
        }
    };

    resize = (rows: number, cols: number): void => {
        if (this.pty) {
            this.pty.resize(cols, rows);
        }
    };

    shutdown = (): void => {
        console.log(`${this.logPrefix}Stopping container...`);
        childProcess.execFile('docker', ['stop', '-t', '2', this.containerName], {},
            () => childProcess.execFile('docker', ['rm', this.containerName]));
    };

    gdbSetBreakpoint = async (line: number): Promise<void> => {
        if (!this.gdbSocketPath) {
            throw new DebugStateError('Debugging is not enabled');
        }
        console.log(`${this.logPrefix} got debugging command: set breakpoint`, line);
        const breakpoint = await this.gdb.addBreak(this.codeContainerPath, line);
        this.breakpoints[line] = breakpoint;

        // Extend run timeout for people in debugging sessions
        this.setRunTimeoutMonitor();
    };

    gdbRemoveBreakpoint = async (line: number): Promise<void> => {
        if (!this.gdbSocketPath) {
            throw new DebugStateError('Debugging is not enabled');
        }
        if (this.breakpoints[line] === undefined) {
            throw new DebugStateError(`No known breakpoint at ${line}`);
        }
        console.log(`${this.logPrefix} got debugging command: remove breakpoint`, line);
        await this.gdb.removeBreak(this.breakpoints[line]);
        delete this.breakpoints[line];

        // Extend run timeout for people in debugging sessions
        this.setRunTimeoutMonitor();
    };

    gdbProceed = async (threadId: number): Promise<void> => {
        if (!this.gdbSocketPath) {
            throw new DebugStateError('Debugging is not enabled');
        }
        if (this.threads[threadId] === undefined) {
            throw new DebugStateError(`No known thread with id ${threadId}`);
        }
        console.log(`${this.logPrefix} got debugging command: proceed`, threadId);
        await this.gdb.proceed(this.threads[threadId]);

        // Extend run timeout for people in debugging sessions
        this.setRunTimeoutMonitor();
    };

    gdbStepIn = async (threadId: number): Promise<void> => {
        if (!this.gdbSocketPath) {
            throw new DebugStateError('Debugging is not enabled');
        }
        if (this.threads[threadId] === undefined) {
            throw new DebugStateError(`No known thread with id ${threadId}`);
        }
        console.log(`${this.logPrefix} got debugging command: step in`, threadId);
        await this.gdb.stepIn(this.threads[threadId]);

        // Extend run timeout for people in debugging sessions
        this.setRunTimeoutMonitor();
    };

    gdbNext = async (threadId: number): Promise<void> => {
        if (!this.gdbSocketPath) {
            throw new DebugStateError('Debugging is not enabled');
        }
        if (this.threads[threadId] === undefined) {
            throw new DebugStateError(`No known thread with id ${threadId}`);
        }
        console.log(`${this.logPrefix} got debugging command: next`, threadId);
        await this.gdb.next(this.threads[threadId]);

        // Extend run timeout for people in debugging sessions
        this.setRunTimeoutMonitor();
    };
}
