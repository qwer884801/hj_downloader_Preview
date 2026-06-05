"use strict";

const fs = require("fs");
const vm = require("vm");

function assert(condition, message) {
  if (!condition) throw new Error(message || "assertion failed");
}

function makeDownloaderContext() {
  const elements = new Map();
  const ids = [
    "site-origin", "origin-import", "batch-input", "name-template", "conflict-mode",
    "delay-seconds", "segment-timeout", "segment-concurrency", "adaptive-concurrency",
    "task-concurrency", "global-media-concurrency",
    "login-assist", "by-author", "save-manifest", "fallback-preview", "sell-video-only",
    "auto-download-after-parse", "toggle-parsed-sources", "summary", "results",
    "stop", "float-stop", "float-login", "float-root", "float-state", "float-current",
    "float-progress-fill", "float-task-concurrency", "float-global-media-concurrency"
  ];
  for (const id of ids) {
    elements.set(id, {
      value: id === "site-origin" ? "https://www.example.test" : "",
      checked: false,
      disabled: false,
      textContent: "",
      dataset: {},
      addEventListener() {},
      classList: { toggle() {} },
      contains() { return false; },
      matches() { return false; },
      querySelector() { return null; },
      querySelectorAll() { return []; },
    });
  }
  elements.get("name-template").value = "{title}";
  elements.get("conflict-mode").value = "skip";
  elements.get("segment-concurrency").value = "12";
  elements.get("task-concurrency").value = "2";
  elements.get("global-media-concurrency").value = "24";

  const storage = new Map();
  const permissionRequests = [];
  const grantedOrigins = new Set();
  const context = {
    console,
    URL,
    BigInt,
    Blob,
    Map,
    Set,
    Array,
    Object,
    String,
    Number,
    Boolean,
    RegExp,
    Date,
    Math,
    Error,
    TextDecoder,
    Uint8Array,
    document: {
      activeElement: null,
      documentElement: { dataset: {} },
      addEventListener() {},
      getElementById(id) { return elements.get(id) || null; },
      querySelectorAll() { return []; },
    },
    window: { setTimeout, clearTimeout },
    chrome: {
      runtime: { getManifest() { return { version: "test" }; } },
      tabs: { onRemoved: { addListener() {} }, onUpdated: { addListener() {} } },
      permissions: {
        async contains(request) {
          return (request.origins || []).every((origin) => grantedOrigins.has(origin));
        },
        async request(request) {
          const origins = request.origins || [];
          permissionRequests.push(origins);
          for (const origin of origins) grantedOrigins.add(origin);
          return true;
        },
        async getAll() {
          return { origins: Array.from(grantedOrigins) };
        },
      },
    },
    localStorage: {
      getItem(key) { return storage.has(key) ? storage.get(key) : null; },
      setItem(key, value) { storage.set(key, value); },
    },
    requestAnimationFrame(fn) { return setTimeout(fn, 0); },
  };
  context.__permissionRequests = permissionRequests;
  context.__grantedOrigins = grantedOrigins;
  vm.createContext(context);
  vm.runInContext(fs.readFileSync("downloader.js", "utf8"), context, { filename: "downloader.js" });
  return { context, storage };
}

async function run() {
  const extensionManifest = JSON.parse(fs.readFileSync("manifest.json", "utf8"));
  assert(!extensionManifest.permissions.includes("permissions"), "manifest should not declare unknown permissions permission");
  assert(extensionManifest.host_permissions.includes("https://*/*"), "manifest should allow extension-page HTTPS media fetches");
  assert(!Object.prototype.hasOwnProperty.call(extensionManifest, "optional_host_permissions"), "optional host permissions should not duplicate required HTTPS access");

  const { context, storage } = makeDownloaderContext();

  const entries = context.parseBatchInput("https://www.example.test/homepage/sell/22485950");
  assert(entries.length === 1, "sell URL should produce one entry");
  assert(entries[0].type === "sell", "sell URL should not be parsed as post pid");

  const manifest = context.analyzeManifest(`#EXTM3U\n#EXT-X-KEY:method=AES-128,uri="key.key",iv=0x01\n#EXTINF:5,\nseg0.ts\n#EXT-X-ENDLIST`, "https://cdn.example/a/index.m3u8");
  assert(manifest.segmentEntries[0].key.method === "AES-128", "M3U8 key attributes should be case-insensitive");

  const fmp4 = context.analyzeManifest(`#EXTM3U\n#EXT-X-MAP:URI="init.mp4",BYTERANGE="720@0"\n#EXTINF:5,\nseg0.m4s\n#EXT-X-BYTERANGE:100@720\nseg.mp4\n#EXT-X-BYTERANGE:120\nseg.mp4\n#EXT-X-ENDLIST`, "https://cdn.example/a/index.m3u8");
  assert(fmp4.mediaContainer === "mp4", "EXT-X-MAP should mark fMP4 output");
  assert(fmp4.segmentEntries[0].map.uri === "https://cdn.example/a/init.mp4", "EXT-X-MAP uri should resolve");
  assert(fmp4.segmentEntries[1].byteRange.offset === 720, "explicit byte-range offset should parse");
  assert(fmp4.segmentEntries[2].byteRange.offset === 820, "implicit byte-range offset should continue per URL");

  const byteRangeTs = context.analyzeManifest(`#EXTM3U\n#EXTINF:5,\nall.ts\n#EXT-X-BYTERANGE:100@0\nall.ts\n#EXT-X-ENDLIST`, "https://cdn.example/a/index.m3u8");
  assert(byteRangeTs.mediaContainer === "ts", "TS byte-range should keep TS output");

  const candidates = context.deriveM3u8Candidates([{ url: "https://cdn.example/a/video_000.ts" }], "https://cdn.example/a/preview.m3u8");
  assert(candidates.includes("https://cdn.example/a/video_.m3u8"), "numbered segment should derive prefix m3u8");
  assert(candidates.includes("https://cdn.example/a/index.m3u8"), "same-directory index.m3u8 should be a fallback candidate");

  const sampleAes = context.analyzeManifest(`#EXTM3U\n#EXT-X-KEY:METHOD=SAMPLE-AES,URI="key.key"\n#EXTINF:5,\nseg0.ts\n#EXT-X-ENDLIST`, "https://cdn.example/a/index.m3u8");
  assert(context.getUnsupportedKeyMethods({ analysis: sampleAes })[0] === "SAMPLE-AES", "SAMPLE-AES should be reported unsupported");

  storage.set("settings", "{bad json");
  storage.set("settingsBackup", JSON.stringify({ nameTemplate: "{pid}" }));
  assert(context.loadStoredSettings().nameTemplate === "{pid}", "settings backup should recover corrupted settings");

  assert(context.getFetchCredentials("https://www.example.test/a.m3u8") === "include", "site fetch should include credentials");
  assert(context.getFetchCredentials("https://cdn.example/a.ts") === "omit", "cdn fetch should omit credentials");
  assert(context.isStaleMediaFetchError(new Error("segment HTTP 403 https://cdn.example/a.ts")), "403 segments should skip retry and refresh manifest");
  assert(!context.isStaleMediaFetchError(new Error("segment HTTP 500 https://cdn.example/a.ts")), "500 segments should keep normal retry behavior");

  await context.ensureUrlFetchPermission("https://cdn.example/a.ts");
  assert(context.__permissionRequests.some((request) => request.includes("https://cdn.example/*")), "cdn fetch should check exact-origin permission");

  assert(context.getEstimateSampleIndexes(2).length === 2, "short videos should sample all segments when practical");
  assert(context.getEstimateSampleIndexes(20).length === 10, "long videos should cap samples at 10");

  console.log("tests ok");
}

run().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
