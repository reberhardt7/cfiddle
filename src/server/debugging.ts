import fs from 'fs';
import readline from 'readline';

import {
    FileDescriptorTable, ContainerInfo, Process, OpenFileTable, VnodeTable,
} from '../common/communication';
import { DebugDataError } from './error';

const CPLAYGROUND_PROCFILE = '/proc/cplayground';
const USE_MOCK_DATA = Boolean(process.env.CP_MOCK_DEBUGGER);
export const ENABLE_DEBUGGING = USE_MOCK_DATA || fs.existsSync(CPLAYGROUND_PROCFILE);

const FILE_FLAGS = {
    // Open flags:
    O_RDONLY: 0o0,
    O_WRONLY: 0o1,
    O_RDWR: 0o2,
    O_APPEND: 0o2000,
    O_NONBLOCK: 0o4000,
    O_NDELAY: 0o4000,
    O_SYNC: 0o4010000,
    O_ASYNC: 0o20000,
    O_DSYNC: 0o10000,
    O_NOATIME: 0o1000000,
    O_CLOEXEC: 0o2000000,
    // File type:
    S_IFIFO: 0o010000, // named pipe (fifo)
    S_IFCHR: 0o020000, // character special
    S_IFDIR: 0o040000, // directory
    S_IFBLK: 0o060000, // block special
    S_IFREG: 0o100000, // regular
    S_IFLNK: 0o120000, // symbolic link
    S_IFSOCK: 0o140000, // socket
};
type FileFlag = keyof typeof FILE_FLAGS;

type RawFileInfo = {
    fd: number;
    closeOnExec: boolean;
    openFileID: string;
    pos: number;
    flags: FileFlag[];
    vnodeName: string;
}

type RawProcessInfo = {
    namespaceID: string;
    globalPID: number;
    containerPID: number;
    containerPPID: number;
    containerPGID: number;
    command: string;
    files: {
        [key: number]: RawFileInfo;
    };
}

type RawContainerInfo = {
    [containerPID: string]: RawProcessInfo;
}

type RawInfoByNamespace = {
    [namespaceId: string]: RawContainerInfo;
}

type CleanedInfoByNamespace = {
    [globalPID: number]: ContainerInfo;
}

const MOCK_DATA = {
    processes: [{
        pid: 20,
        ppid: 1,
        pgid: 1,
        command: 'output',
        fds: {
            0: {
                file: '6d2b62b056631445f3a906498f0ab45fea4c4e68a198af6f268a34269fb30caa',
                closeOnExec: false,
            },
            1: {
                file: '6d2b62b056631445f3a906498f0ab45fea4c4e68a198af6f268a34269fb30caa',
                closeOnExec: false,
            },
            2: {
                file: '6d2b62b056631445f3a906498f0ab45fea4c4e68a198af6f268a34269fb30caa',
                closeOnExec: false,
            },
            3: {
                file: '4877eb7123020cbb048bec0564324a4f2dcdc4c6d98c4b925da38f6d978fd24e',
                closeOnExec: false,
            },
        },
    }, {
        pid: 21,
        ppid: 20,
        pgid: 1,
        command: 'output',
        fds: {
            0: {
                file: '6d2b62b056631445f3a906498f0ab45fea4c4e68a198af6f268a34269fb30caa',
                closeOnExec: false,
            },
            1: {
                file: '2d7ed44fbc12ed3c63692795dd3fdbf0fb038841fcce65a20419938d04bae623',
                closeOnExec: false,
            },
            2: {
                file: '6d2b62b056631445f3a906498f0ab45fea4c4e68a198af6f268a34269fb30caa',
                closeOnExec: false,
            },
        },
    }],
    openFiles: {
        '6d2b62b056631445f3a906498f0ab45fea4c4e68a198af6f268a34269fb30caa': {
            position: 0,
            flags: [
                'O_RDWR',
                'S_IFREG',
            ],
            refcount: 5,
            vnode: '/dev/pts/0',
        },
        '4877eb7123020cbb048bec0564324a4f2dcdc4c6d98c4b925da38f6d978fd24e': {
            position: 0,
            flags: [
                'O_RDONLY',
            ],
            refcount: 1,
            vnode: 'pipe:[116131]',
        },
        '2d7ed44fbc12ed3c63692795dd3fdbf0fb038841fcce65a20419938d04bae623': {
            position: 0,
            flags: [
                'O_WRONLY',
            ],
            refcount: 1,
            vnode: 'pipe:[116131]',
        },
    },
    vnodes: {
        '/dev/pts/0': {
            name: '/dev/pts/0',
            refcount: 1,
        },
        'pipe:[116131]': {
            name: 'pipe:[116131]',
            refcount: 2,
        },
    },
};

/**
 * Given an octal string, returns an array of flag names
 */
function readFlags(octalStr: string): FileFlag[] {
    let octal = parseInt(octalStr, 8);
    const flags: FileFlag[] = [];
    Object.keys(FILE_FLAGS).forEach((flag: FileFlag) => {
        // eslint-disable-next-line no-bitwise
        if ((octal & FILE_FLAGS[flag]) === FILE_FLAGS[flag]) {
            flags.push(flag);
        }
    });
    // Edge case: if O_WRONLY or O_RDWR are set, remove O_RDONLY. (The flags
    // are mutually exclusive, and O_RDONLY is defined as 0 so it is
    // technically included in all possible modes.)
    if (flags.includes('O_WRONLY') || flags.includes('O_RDWR')) {
        flags.splice(flags.indexOf('O_RDONLY'), 1);
    }
    // Make sure there are no flags we might be missing
    Object.keys(FILE_FLAGS).forEach((flag: FileFlag) => {
        // eslint-disable-next-line no-bitwise
        if ((octal & FILE_FLAGS[flag]) === FILE_FLAGS[flag]) {
            // eslint-disable-next-line no-bitwise
            octal &= ~FILE_FLAGS[flag];
        }
    });
    if (octal) {
        console.warn(`Tried to determine all the flags that are included in ${octalStr}, `
            + 'but there are some unknown ones remaining. Remaining value: '
            + `0${octal.toString(8)}`, flags);
    }
    return flags;
}

/**
 * Reads a line (corresponding to process info) from the kernel module output
 */
function readProcessLine(line: string): RawProcessInfo {
    const [
        namespaceID, // hash of pid_namespace pointer
        globalPID, // actual PID of process
        containerPID, // PID of process as it appears within the container
        containerPPID,
        containerPGID,
        command,
    ] = line.split('\t');
    return {
        namespaceID,
        globalPID: Number(globalPID),
        containerPID: Number(containerPID),
        containerPPID: Number(containerPPID),
        containerPGID: Number(containerPGID),
        command,
        files: {},
    };
}

/**
 * Reads a line (corresponding to a file descriptor's info) from the kernel
 * module's output
 */
function readFileLine(line: string): RawFileInfo {
    const [
        fd, // fd number
        closeOnExec, // true/false
        openFileID, // hash of `struct file` pointer
        pos, // byte offset
        flags, // octal string
        vnodeName, // e.g. "/dev/pts/0" or "pipe:[90222668]"
    ] = line.split('\t');
    return {
        fd: Number(fd),
        closeOnExec: Boolean(Number(closeOnExec)),
        openFileID,
        pos: Number(pos),
        flags: readFlags(flags),
        vnodeName,
    };
}

/**
 * Reads /proc/cplayground and stores the information from that file in a more
 * readily analyzed data structure:
 *
 * {
 *     namespace ID (hash of pid_namespace pointer): {
 *         container PID of process in namespace: {
 *             ... info about process and open files
 *         }
 *         ... other containers
 *     }
 *     ... other namespaces
 * }
 */
async function loadRawProcessInfo(): Promise<RawInfoByNamespace> {
    const rl = readline.createInterface({
        input: fs.createReadStream(CPLAYGROUND_PROCFILE),
    });
    const namespaces: RawInfoByNamespace = {};
    let readingProcessLine = true;
    let currProcess;
    for await (const line of rl) {
        if (readingProcessLine) {
            currProcess = readProcessLine(line);
            if (namespaces[currProcess.namespaceID] === undefined) {
                namespaces[currProcess.namespaceID] = {};
            }
            const { namespaceID, globalPID, containerPID } = currProcess;
            if (namespaces[namespaceID][containerPID]) {
                console.warn(`Warning: container PID ${containerPID} appears `
                    + `multiple times in namespace ${namespaceID}! This `
                    + 'should never happen.', namespaces, currProcess);
            }
            if (Object.values(namespaces[namespaceID])
                .filter((p) => p.globalPID === globalPID).length) {
                console.warn(`Warning: global PID ${globalPID} appears `
                    + `multiple times in namespace ${namespaceID}! This `
                    + 'should never happen.', namespaces, currProcess);
            }
            namespaces[namespaceID][containerPID] = currProcess;
            readingProcessLine = false;
        } else if (line === '') {
            readingProcessLine = true;
        } else {
            const file = readFileLine(line);
            if (currProcess.files[file.fd]) {
                console.warn(`Warning: fd ${file.fd} appears multiple times! `
                    + 'This should never happen.', namespaces, currProcess);
            }
            currProcess.files[file.fd] = readFileLine(line);
        }
    }
    return namespaces;
}

// eslint-disable-next-line @typescript-eslint/no-explicit-any
function deepCompare(obj1: any, obj2: any): boolean {
    // TODO: come up with less hacky way to do this
    return JSON.stringify(obj1) === JSON.stringify(obj2);
}

function populateProcessTable(rawProcesses: RawProcessInfo[]): Process[] {
    const processes: Process[] = [];

    for (const proc of rawProcesses) {
        const fds: FileDescriptorTable = {};
        for (const fd of Object.values(proc.files)) {
            fds[fd.fd] = { file: fd.openFileID, closeOnExec: fd.closeOnExec };
        }
        processes.push({
            pid: proc.containerPID,
            ppid: proc.containerPPID,
            pgid: proc.containerPGID,
            command: proc.command,
            fds,
        });
    }

    return processes;
}

function populateOpenFileTable(rawFiles: RawFileInfo[]): OpenFileTable {
    const openFiles: OpenFileTable = {};

    for (const file of rawFiles) {
        const openFileEntry = {
            position: file.pos,
            flags: file.flags,
            refcount: 1,
            vnode: file.vnodeName,
        };
        if (openFiles[file.openFileID] === undefined) {
            openFiles[file.openFileID] = openFileEntry;
        } else if (deepCompare({ ...openFileEntry, refcount: undefined },
            { ...openFiles[file.openFileID], refcount: undefined })) {
            openFiles[file.openFileID].refcount += 1;
        } else {
            throw new DebugDataError(`There is already an open file ${file.openFileID} with different `
                + 'info compared to this open file entry!\n'
                + `New entry: ${JSON.stringify(openFileEntry)}\n`
                + `Existing entry: ${JSON.stringify(openFiles[file.openFileID])}`);
        }
    }

    return openFiles;
}

function populateVnodeTable(rawFiles: RawFileInfo[], openFiles: OpenFileTable): VnodeTable {
    const vnodes: VnodeTable = {};

    for (const file of rawFiles) {
        const vnodeEntry = {
            name: file.vnodeName,
            refcount: 0,
        };
        if (vnodes[file.vnodeName] === undefined) {
            vnodes[file.vnodeName] = vnodeEntry;
        } else if (!deepCompare(vnodeEntry, vnodes[file.vnodeName])) {
            throw new DebugDataError(`There is already a vnode ${file.vnodeName} with different `
                + 'info compared to this vnode!\n'
                + `New entry: ${JSON.stringify(vnodeEntry)}`
                + `Existing entry: ${JSON.stringify(vnodes[file.vnodeName])}`);
        }
    }

    // Set refcounts
    for (const openFile of Object.values(openFiles)) {
        vnodes[openFile.vnode].refcount += 1;
    }

    return vnodes;
}

function cleanContainerData(
    rawProcesses: RawContainerInfo,
): {globalPID: number; data: ContainerInfo} {
    const initProcess = rawProcesses['1'];
    if (initProcess === undefined) {
        throw new DebugDataError(
            'This namespace seems to be missing an init process! This should never happen.',
        );
    }

    const processes = Object.values(rawProcesses)
    // Omit the runc container-creating process, as well as our run.py script
        .filter((proc) => proc.containerPID > 1);
    const files = processes
        .map((process) => Object.values(process.files))
        .flat();

    const openFileTable = populateOpenFileTable(files);
    return {
        globalPID: initProcess.globalPID,
        data: {
            processes: populateProcessTable(processes),
            openFiles: openFileTable,
            vnodes: populateVnodeTable(files, openFileTable),
        },
    };
}

/**
 * Given the data structure generated from loading the raw kernel file,
 * reorganizes this information in a way that is readily consumable by the
 * client. (E.g. strip out global PIDs, so that no extra-container info is
 * leaked)
 */
function reconstructTables(namespaces: RawInfoByNamespace): CleanedInfoByNamespace {
    const containers: CleanedInfoByNamespace = {};
    for (const namespaceID of Object.keys(namespaces)) {
        try {
            const { globalPID, data } = cleanContainerData(namespaces[namespaceID]);
            containers[globalPID] = data;
        } catch (exc) {
            console.error(
                `Encountered error while cleaning data for namespace ${namespaceID}`,
                exc,
                namespaces[namespaceID],
            );
        }
    }
    return containers;
}

let processInfo: CleanedInfoByNamespace | null = null;

/**
 * Start the polling mechanism that loads info from /proc/cplayground
 */
export async function init(): Promise<void> {
    if (USE_MOCK_DATA) {
        // We don't actually need to poll /proc/cplayground
        return;
    }

    processInfo = reconstructTables(await loadRawProcessInfo());
    // TODO: only poll the file if there is an active debugging session
    setInterval(async () => {
        processInfo = reconstructTables(await loadRawProcessInfo());
    }, 1000);
}

export async function getContainerInfo(containerId: string): Promise<ContainerInfo> {
    if (USE_MOCK_DATA) {
        console.warn('CP_MOCK_DEBUGGER is set. Mock container data will be used.');
        return MOCK_DATA;
    }

    const pidFile = `/sys/fs/cgroup/pids/docker/${containerId}/cgroup.procs`;
    let initPID;

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
        initPID = parseInt(line, 10);
        rl.close();
        break;
    }
    return processInfo[initPID];
}
