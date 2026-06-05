"use strict";

const DB_NAME = "hj-downloader-preview";
const DB_VERSION = 1;
const ROOT_KEY = "root";
const SOURCE_HISTORY_KEY = "sourceHistoryV1";
const LOCAL_HISTORY_DIR = ".hj-downloader-preview";
const SELL_HISTORY_DIR = "sell-history";
const SELL_SOURCE_INDEX_FILE = "sell-sources-v1.json";
const SELL_HISTORY_VERSION = 1;
const SELL_HISTORY_MIN_SUPPORTED_VERSION = 1;
const SETTINGS_KEY = "settings";
const SETTINGS_BACKUP_KEY = "settingsBackup";
const RESULT_VIEW_STATE_KEY = "resultViewState";
const LEGACY_DEFAULT_NAME_TEMPLATE = "{title} - {author}-用户{uid} - 帖子{pid} - {seconds}s";
const DEFAULT_NAME_TEMPLATE = "{publishedSort} - {title} - {author}-用户{uid} - 帖子{pid} - {seconds}s";
const LOGIN_ASSIST_DURATION_MS = 120000;
const SELL_LIST_TYPE = 5;
const SELL_SCAN_PAGE_DELAY_MS = 350;
const WRITE_FLUSH_THRESHOLD_BYTES = 8 * 1024 * 1024;
const PARSE_CONCURRENCY = 4;
const DEFAULT_SEGMENT_CONCURRENCY = 12;
const DEFAULT_TASK_CONCURRENCY = 2;
const DEFAULT_GLOBAL_MEDIA_CONCURRENCY = 24;
const SLOW_SEGMENT_BACKUP_AFTER_MS = 9000;
const SLOW_SEGMENT_MIN_PROGRESS_MS = 2500;
const AUTHORS_PER_PAGE = 6;
const DEFAULT_AUTHOR_ITEM_PAGE_SIZE = 20;
const DEFAULT_SITE_ORIGIN = "";
const STATUS = Object.freeze({
  OK: "ok",
  FAILED: "failed",
  PREVIEW: "preview",
  EXCLUDED: "excluded",
  STOPPED: "stopped",
  SKIPPED: "skipped",
  RUNNING: "running",
  PENDING: "pending",
  PARSED: "parsed",
});
const FLOAT_SYNC_FIELDS = [
  ["site-origin", "float-site-origin", "value"],
  ["batch-input", "float-batch-input", "value"],
  ["delay-seconds", "float-delay-seconds", "value"],
  ["segment-timeout", "float-segment-timeout", "value"],
  ["segment-concurrency", "float-segment-concurrency", "value"],
  ["task-concurrency", "float-task-concurrency", "value"],
  ["global-media-concurrency", "float-global-media-concurrency", "value"],
  ["sell-video-only", "float-sell-video-only", "checked"],
  ["auto-download-after-parse", "float-auto-download-after-parse", "checked"],
  ["adaptive-concurrency", "float-adaptive-concurrency", "checked"],
  ["login-assist", "float-login-assist", "checked"],
];
const FLOAT_SYNC_MAIN_IDS = FLOAT_SYNC_FIELDS.map(([mainId]) => mainId);

let rootHandle = null;
let activeReport = null;
let running = false;
let stopRequested = false;
let activeStopController = null;
let renderQueued = false;
let deferredResultRenderTimer = null;
let saveSettingsTimer = null;
let forceNextResultRender = false;
let helperTabId = null;
let helperTabCreated = false;
let helperTabOrigin = "";
let helperTabToken = "";
const contentHelperInjectedTabs = new Set();
let loginState = { status: "unknown", text: "未检测" };
let estimatingSelectedSize = false;
let backfillingPublishedTimes = false;
let busyMode = "";
let detectedSiteOrigins = [];
const sellHistoryWriteQueues = new Map();
let activeMediaRequestLimiter = null;
let activeMediaKeyCache = null;
let resultViewState = {
  authorPage: 1,
  authorItemPageSize: DEFAULT_AUTHOR_ITEM_PAGE_SIZE,
  statusFilter: "all",
  sortMode: "default",
  globalQuery: "",
  selectedAuthorKeys: [],
  authorItemPages: {},
  authorQueries: {},
};
let hideParsedInputSources = false;

const $ = (id) => document.getElementById(id);

function isBusy() {
  return Boolean(running || busyMode || estimatingSelectedSize || backfillingPublishedTimes);
}

function beginBusy(mode) {
  busyMode = mode || "busy";
  updateFloatingButtons();
}

function endBusy(mode) {
  if (!mode || busyMode === mode) busyMode = "";
  updateFloatingButtons();
}

function beginStoppableRun() {
  stopRequested = false;
  activeStopController = new AbortController();
}

function requestStop() {
  stopRequested = true;
  if (activeStopController) activeStopController.abort();
  closeHelperTab().catch(() => {});
  setDisabled("stop", true);
  setDisabled("float-stop", true);
  setSummary("正在停止，当前请求会尽快中断。");
}

function clearStoppableRun() {
  activeStopController = null;
}

function throwIfStopRequested() {
  if (stopRequested) throw new Error("用户停止");
}

function createMediaRequestLimiter(limit) {
  const maxActive = clampInteger(limit, 1, 96, DEFAULT_GLOBAL_MEDIA_CONCURRENCY);
  const queue = [];
  let active = 0;

  function drain() {
    while (active < maxActive && queue.length) {
      const entry = queue.shift();
      if (entry.signal && entry.onAbort) entry.signal.removeEventListener("abort", entry.onAbort);
      active += 1;
      let released = false;
      entry.resolve(() => {
        if (released) return;
        released = true;
        active = Math.max(0, active - 1);
        drain();
      });
    }
  }

  function acquire(signal) {
    if (signal && signal.aborted) return Promise.reject(new Error("用户停止"));
    return new Promise((resolve, reject) => {
      const entry = { resolve, reject, signal, onAbort: null };
      entry.onAbort = () => {
        const index = queue.indexOf(entry);
        if (index >= 0) queue.splice(index, 1);
        reject(new Error("用户停止"));
      };
      if (signal) signal.addEventListener("abort", entry.onAbort, { once: true });
      queue.push(entry);
      drain();
    });
  }

  return { acquire, limit: maxActive };
}

async function withMediaRequestSlot(task) {
  const limiter = activeMediaRequestLimiter;
  if (!limiter) return task();
  const release = await limiter.acquire(activeStopController && activeStopController.signal);
  try {
    return await task();
  } finally {
    release();
  }
}

function runUiAction(label, action) {
  Promise.resolve()
    .then(action)
    .catch((error) => {
      if (error && error.name === "AbortError") {
        setSummary(`${label}已取消。`);
        return;
      }
      console.error(error);
      setSummary(`${label}失败：${String(error && error.message || error)}`);
      updateFloatingButtons();
    });
}

document.addEventListener("DOMContentLoaded", async () => {
  bindEvents();
  renderAppVersion();
  restoreSettings();
  restoreResultViewState();
  applySiteOriginInput(false);
  syncFloatingFromMain();
  updateSiteOriginState();
  rootHandle = await loadRootHandle();
  await refreshRootState();
  await renderSavedSellSources();
});

function renderAppVersion() {
  const badge = $("app-version");
  if (!badge || !chrome.runtime || !chrome.runtime.getManifest) return;
  badge.textContent = ` v${chrome.runtime.getManifest().version}`;
}

function bindEvents() {
  $("choose-root").addEventListener("click", () => runUiAction("选择根目录", chooseRootDirectory));
  $("open-root").addEventListener("click", () => runUiAction("打开/授权根目录", openRootDirectory));
  $("authorize-origin").addEventListener("click", () => runUiAction("授权当前域名", authorizeCurrentOrigin));
  $("refresh-origins").addEventListener("click", () => runUiAction("刷新域名列表", () => updateSiteOriginState("已刷新域名列表。")));
  $("detect-origins").addEventListener("click", () => runUiAction("识别域名", () => importDetectedOrigins(false)));
  $("authorize-detected-origins").addEventListener("click", () => runUiAction("授权识别域名", () => importDetectedOrigins(true)));
  $("check-login").addEventListener("click", () => runUiAction("检查登录", checkLoginStatus));
  $("open-login").addEventListener("click", () => runUiAction("打开登录页", openLoginPage));
  $("parse").addEventListener("click", () => runUiAction("解析资源", () => parseResources({ respectAuto: true })));
  $("start").addEventListener("click", () => runUiAction("下载选中", downloadOrParse));
  $("stop").addEventListener("click", requestStop);
  $("export-report").addEventListener("click", exportReport);
  $("toggle-parsed-sources").addEventListener("click", toggleParsedSourcesVisibility);
  $("saved-sell-refresh").addEventListener("click", () => runUiAction("刷新已保存博主", renderSavedSellSources));
  $("saved-sell-add").addEventListener("click", addSelectedSavedSellsToInput);
  $("float-toggle").addEventListener("click", toggleFloatConsole);
  $("float-check-login").addEventListener("click", () => runUiAction("检查登录", checkLoginStatus));
  $("float-open-login").addEventListener("click", () => runUiAction("打开登录页", openLoginPage));
  $("float-choose-root").addEventListener("click", () => runUiAction("选择根目录", chooseRootDirectory));
  $("float-parse").addEventListener("click", () => runUiAction("解析资源", () => parseResources({ respectAuto: true })));
  $("float-start").addEventListener("click", () => runUiAction("下载选中", downloadOrParse));
  $("float-stop").addEventListener("click", requestStop);
  $("float-export").addEventListener("click", exportReport);
  $("results").addEventListener("change", handleResultChange);
  $("results").addEventListener("input", handleResultInput);
  $("results").addEventListener("click", handleResultClick);
  bindBatchFormatter("batch-input");
  bindBatchFormatter("float-batch-input");

  for (const id of Array.from(new Set([...FLOAT_SYNC_MAIN_IDS, "origin-import", "name-template", "conflict-mode", "by-author", "save-manifest", "fallback-preview"]))) {
    $(id).addEventListener("change", () => {
      if (id === "site-origin") applySiteOriginInput(false);
      syncFloatingFromMain();
      updateSiteOriginState();
      saveSettings();
    });
    $(id).addEventListener("input", () => {
      syncFloatingFromMain();
      if (id === "site-origin") updateSiteOriginState();
      saveSettings();
    });
  }

  for (const [mainId, floatId] of FLOAT_SYNC_FIELDS) {
    $(floatId).addEventListener("change", () => {
      syncMainFromFloating();
      if (mainId === "site-origin") applySiteOriginInput(false);
      updateSiteOriginState();
      saveSettings();
    });
    $(floatId).addEventListener("input", () => {
      syncMainFromFloating();
      if (mainId === "site-origin") updateSiteOriginState();
      saveSettings();
    });
  }
}

function bindBatchFormatter(id) {
  const input = $(id);
  input.addEventListener("paste", () => {
    window.setTimeout(() => {
      formatBatchInput(id);
      if (id === "batch-input") syncFloatingFromMain();
      if (id === "float-batch-input") syncMainFromFloating();
      saveSettings();
    }, 0);
  });
  input.addEventListener("blur", () => {
    if (formatBatchInput(id)) {
      if (id === "batch-input") syncFloatingFromMain();
      if (id === "float-batch-input") syncMainFromFloating();
      saveSettings();
    }
  });
}

async function chooseRootDirectory() {
  if (!window.showDirectoryPicker) {
    setSummary("当前 Chrome 不支持目录选择 API，请升级浏览器。");
    return;
  }
  const previousRoot = rootHandle;
  const picked = await pickDirectory(rootHandle);
  if (!(await ensureDirectoryPermission(picked))) {
    setSummary("目录授权失败，无法开始解析或下载。");
    return;
  }
  const migration = await prepareRootHistory(previousRoot, picked);
  rootHandle = picked;
  await saveRootHandle(rootHandle);
  await refreshRootState();
  await renderSavedSellSources();
  setSummary(formatRootHistorySummary("根目录已选择", migration));
}

async function openRootDirectory() {
  if (!rootHandle) {
    await chooseRootDirectory();
    return;
  }
  if (!(await ensureDirectoryPermission(rootHandle))) {
    setSummary("根目录授权失败。");
    await refreshRootState();
  }

  try {
    const picked = await pickDirectory(rootHandle);
    if (picked) {
      const previousRoot = rootHandle;
      if (!(await ensureDirectoryPermission(picked))) {
        setSummary("目录授权失败，已保留当前根目录。");
        return;
      }
      const migration = await prepareRootHistory(previousRoot, picked);
      rootHandle = picked;
      await saveRootHandle(rootHandle);
      await refreshRootState();
      await renderSavedSellSources();
      setTimeout(() => setSummary(formatRootHistorySummary("根目录已确认", migration)), 0);
      setSummary("根目录已确认。");
    }
  } catch (error) {
    if (error && error.name === "AbortError") {
      setSummary("已保留当前根目录。");
      return;
    }
    throw error;
  }
}

async function ensureRootForParsing() {
  if (!rootHandle) {
    setSummary("请先选择保存根目录。解析记录会写入本地历史文件，没有目录不能开始。");
    try {
      await chooseRootDirectory();
    } catch (error) {
      if (error && error.name === "AbortError") {
        setSummary("已取消选择目录，解析未开始。");
        return false;
      }
      throw error;
    }
    if (!rootHandle) return false;
  }
  if (!(await ensureDirectoryPermission(rootHandle))) {
    setSummary("根目录没有读写权限，无法写入解析历史。");
    await refreshRootState();
    return false;
  }
  return true;
}

async function pickDirectory(startHandle) {
  const options = { mode: "readwrite" };
  if (startHandle) options.startIn = startHandle;
  try {
    return await window.showDirectoryPicker(options);
  } catch (error) {
    if (startHandle && error && error.name === "TypeError") {
      return window.showDirectoryPicker({ mode: "readwrite" });
    }
    throw error;
  }
}

async function refreshRootState() {
  if (!rootHandle) {
    $("root-state").textContent = "未选择目录";
    $("root-detail").textContent = "选择后会按楼主名创建或复用子文件夹。";
    $("open-root").disabled = true;
    updateFloatingConsole();
    return;
  }
  const granted = await hasDirectoryPermission(rootHandle);
  $("root-state").textContent = granted ? "目录已授权" : "目录需重新授权";
  $("root-detail").textContent = `根目录：${rootHandle.name}${granted ? "" : "。开始前会请求授权。"}`;
  $("open-root").disabled = false;
  updateFloatingConsole();
}

async function checkLoginStatus() {
  loginState = { status: "checking", text: "检测中" };
  updateLoginState();
  try {
    const adopted = adoptSiteOriginFromBatchInput();
    if (adopted) {
      syncFloatingFromMain();
      saveSettings();
    }
    const entries = parseBatchInput($("batch-input").value);
    await prepareOriginsForEntries(entries);
    if (!entries.length) {
      loginState = { status: "unknown", text: "请先输入一个 pid 或详情页链接再检测" };
      updateLoginState();
      return;
    }
    const postEntry = entries.find((entry) => entry.type !== "sell");
    const sellEntry = entries.find((entry) => entry.type === "sell");
    const result = postEntry
      ? await pageFetch("topic", { pid: postEntry.pid, sourceOrigin: postEntry.sourceOrigin })
      : await fetchSellTopics(sellEntry.uid, 1, sellEntry.sourceOrigin);
    if (result && (result.topicId || Array.isArray(result.attachments) || Array.isArray(result.results))) {
      loginState = { status: "ok", text: postEntry ? `登录态可用，测试 pid ${postEntry.pid}` : `登录态可用，测试 sell uid ${sellEntry.uid}` };
    } else {
      loginState = { status: "warn", text: "接口返回异常，可能未登录或登录过期" };
    }
  } catch (error) {
    loginState = { status: "fail", text: `检测失败：${String(error && error.message || error)}` };
  }
  updateLoginState();
}

async function openLoginPage() {
  const adopted = adoptSiteOriginFromBatchInput();
  if (adopted) {
    syncFloatingFromMain();
    saveSettings();
  }
  const origin = getSiteOrigin();
  await ensureSiteOriginPermission(origin);
  const tab = await chrome.tabs.create({ url: `${origin}/home`, active: true });
  if ($("login-assist").checked && tab && tab.id) {
    const result = await startLoginAssistInTab(tab.id);
    loginState = result && result.ok
      ? { status: "unknown", text: "已打开登录页；临时跳过提示已开启 2 分钟，登录后回到插件点击检查登录" }
      : { status: "warn", text: "已打开登录页，但临时跳过提示注入失败；请手动关闭弹窗后登录" };
  } else {
    loginState = { status: "unknown", text: "已打开登录页，登录后回到插件点击检查登录" };
  }
  updateLoginState();
}

async function startLoginAssistInTab(tabId) {
  await waitForTabComplete(tabId, 30000).catch(() => {});
  await sleep(600);
  await ensureContentHelper(tabId).catch(() => {});

  for (let attempt = 1; attempt <= 10; attempt += 1) {
    try {
      const response = await chrome.tabs.sendMessage(tabId, {
        type: "HJBD_LOGIN_ASSIST_START",
        ttlMs: LOGIN_ASSIST_DURATION_MS,
      });
      if (response && response.ok) return response;
    } catch {
      // Content scripts are injected after the document exists; retry briefly.
    }
    await sleep(300 * attempt);
  }
  return null;
}

function updateLoginState() {
  $("login-detail").textContent = loginState.text;
  updateFloatingConsole();
}

function getSiteOrigin() {
  return normalizeSiteOrigin($("site-origin") && $("site-origin").value) || DEFAULT_SITE_ORIGIN;
}

function setSiteOrigin(origin, options = {}) {
  const normalized = normalizeSiteOrigin(origin) || DEFAULT_SITE_ORIGIN;
  const input = $("site-origin");
  if (input && input.value !== normalized) input.value = normalized;
  if (helperTabOrigin && helperTabOrigin !== normalized) {
    closeHelperTab().catch(() => {});
  }
  if (options.save !== false) saveSettings();
  syncFloatingFromMain();
  updateSiteOriginState();
  return normalized;
}

function applySiteOriginInput(requestPermission) {
  const input = $("site-origin");
  const normalized = normalizeSiteOrigin(input && input.value);
  if (!normalized) {
    if (input) input.value = "";
    updateSiteOriginState("请输入 HTTPS 目标域名。");
    return DEFAULT_SITE_ORIGIN;
  }
  if (input && input.value !== normalized) input.value = normalized;
  if (requestPermission) {
    authorizeSiteOrigin(normalized).catch((error) => {
      updateSiteOriginState(`授权失败：${String(error && error.message || error)}`);
    });
  }
  return normalized;
}

async function authorizeCurrentOrigin() {
  const origin = applySiteOriginInput(false);
  try {
    const ok = await ensureSiteOriginPermission(origin);
    updateSiteOriginState(ok ? "当前域名已授权。" : "当前域名未授权。");
  } catch (error) {
    updateSiteOriginState(`授权失败：${String(error && error.message || error)}`);
  }
}

async function authorizeSiteOrigin(origin) {
  return ensureSiteOriginPermission(normalizeSiteOrigin(origin));
}

async function updateSiteOriginState(extraText = "") {
  const state = $("site-origin-state");
  if (!state) return;
  const origin = normalizeSiteOrigin($("site-origin") && $("site-origin").value);
  if (!origin) {
    state.textContent = extraText || "请输入 HTTPS 目标域名。";
    state.parentElement && state.parentElement.classList.remove("authorized", "pending");
    await renderAuthorizedOriginList();
    return;
  }
  let granted = false;
  try {
    granted = await hasOriginPermissions(origin);
  } catch {
    granted = false;
  }
  state.textContent = `${granted ? "已授权" : "未授权"}：${origin}${extraText ? `。${extraText}` : ""}`;
  if (state.parentElement) {
    state.parentElement.classList.toggle("authorized", granted);
    state.parentElement.classList.toggle("pending", !granted);
  }
  await renderAuthorizedOriginList();
  updateFloatingConsole();
}

async function importDetectedOrigins(authorize) {
  const text = [
    $("origin-import") && $("origin-import").value,
    $("batch-input") && $("batch-input").value,
    $("site-origin") && $("site-origin").value,
  ].filter(Boolean).join("\n");
  const origins = extractSiteOriginsFromText(text);
  detectedSiteOrigins = origins;
  if (!origins.length) {
    await updateSiteOriginState("没有识别到允许范围内的域名。");
    return;
  }

  setSiteOrigin(origins[0], { save: false });
  let grantedCount = 0;
  if (authorize) {
    for (const origin of origins) {
      await ensureSiteOriginPermission(origin);
      grantedCount += 1;
    }
  }
  saveSettings();
  await updateSiteOriginState(authorize ? `已授权 ${grantedCount} 个识别域名。` : `已识别 ${origins.length} 个域名。`);
}

async function renderAuthorizedOriginList() {
  const list = $("authorized-origin-list");
  if (!list) return;
  const current = getSiteOrigin();
  const records = await getOriginDisplayRecords(current);
  if (!records.length) {
    list.innerHTML = `<span class="origin-chip pending"><strong>暂无可显示域名</strong></span>`;
    return;
  }
  list.innerHTML = records.map((record) => {
    const classes = [
      "origin-chip",
      record.authorized ? "authorized" : "pending",
      record.current ? "current" : "",
    ].filter(Boolean).join(" ");
    const label = `${record.current ? "当前 · " : ""}${record.authorized ? "已授权" : "未授权"}${record.wildcard ? " · 通配" : ""}`;
    return `<span class="${classes}" title="${escapeHtml(record.origin)}"><span>${escapeHtml(label)}</span><strong>${escapeHtml(record.origin)}</strong></span>`;
  }).join("");
}

async function getOriginDisplayRecords(current) {
  const byOrigin = new Map();
  const addRecord = async (origin, extra = {}) => {
    const normalized = normalizeDisplayOrigin(origin);
    if (!normalized) return;
    const previous = byOrigin.get(normalized) || {};
    const authorized = extra.authorized != null ? Boolean(extra.authorized) : await hasDisplayOriginPermission(normalized);
    byOrigin.set(normalized, {
      ...previous,
      ...extra,
      origin: normalized,
      authorized: Boolean(previous.authorized || authorized),
      current: Boolean(previous.current || normalized === current),
      wildcard: Boolean(previous.wildcard || extra.wildcard),
    });
  };

  await addRecord(current, { current: true });
  for (const origin of detectedSiteOrigins || []) {
    await addRecord(origin);
  }

  try {
    const all = await chrome.permissions.getAll();
    for (const pattern of all.origins || []) {
      const record = permissionPatternToOriginRecord(pattern);
      if (record) await addRecord(record.origin, { authorized: true, wildcard: record.wildcard });
    }
  } catch {
    // ignore permission read failures
  }

  return Array.from(byOrigin.values()).sort((a, b) => {
    if (a.current !== b.current) return a.current ? -1 : 1;
    if (a.authorized !== b.authorized) return a.authorized ? -1 : 1;
    return a.origin.localeCompare(b.origin);
  });
}

function permissionPatternToOriginRecord(pattern) {
  const text = String(pattern || "").trim();
  const wildcard = text.match(/^https:\/\/\*\.(.+?)\/\*$/i);
  if (wildcard && isAllowedTargetHost(wildcard[1])) {
    return { origin: `https://*.${wildcard[1].toLowerCase()}`, wildcard: true };
  }
  const exact = text.match(/^https:\/\/([^/*]+)\/\*$/i);
  if (exact && isAllowedTargetHost(exact[1])) {
    return { origin: `https://${exact[1].toLowerCase()}`, wildcard: false };
  }
  return null;
}

function normalizeDisplayOrigin(value) {
  const text = String(value || "").trim();
  if (!text) return "";
  if (/^https:\/\/\*\./i.test(text)) {
    const host = text.replace(/^https:\/\/\*\./i, "").replace(/\/.*$/, "").toLowerCase();
    return isAllowedTargetHost(host) ? `https://*.${host}` : "";
  }
  return normalizeSiteOrigin(text);
}

async function hasDisplayOriginPermission(origin) {
  if (/^https:\/\/\*\./i.test(origin)) return true;
  return hasOriginPermissions(origin);
}

async function prepareOriginsForEntries(entries) {
  const origins = Array.from(new Set((entries || [])
    .map((entry) => normalizeSiteOrigin(entry && entry.sourceOrigin || ""))
    .filter(Boolean)));
  if (origins.length) setSiteOrigin(origins[0], { save: true });
  const targets = origins.length ? origins : [getSiteOrigin()];
  for (const origin of targets) {
    await ensureSiteOriginPermission(origin);
  }
  return targets[0] || getSiteOrigin();
}

function normalizeSiteOrigin(value) {
  let text = String(value || "").trim();
  if (!text) return "";
  if (!/^https?:\/\//i.test(text)) text = `https://${text}`;
  try {
    const url = new URL(text);
    url.protocol = "https:";
    url.username = "";
    url.password = "";
    url.pathname = "/";
    url.search = "";
    url.hash = "";
    const hostname = url.hostname.toLowerCase();
    if (!isAllowedTargetHost(hostname)) return "";
    return `https://${hostname}${url.port ? `:${url.port}` : ""}`;
  } catch {
    return "";
  }
}

function getOriginFromText(value) {
  return extractSiteOriginsFromText(value)[0] || normalizeSiteOrigin(value);
}

function isAllowedTargetHost(hostname) {
  const host = String(hostname || "").toLowerCase();
  return Boolean(host && !host.includes("/") && !host.includes(" ") && (host.includes(".") || host === "localhost"));
}

function originPermissionPatterns(origin) {
  const normalized = normalizeSiteOrigin(origin);
  if (!normalized) return [];
  const url = new URL(normalized);
  return [`${url.origin}/*`];
}

async function hasOriginPermissions(origin) {
  const patterns = originPermissionPatterns(origin);
  if (!patterns.length || !chrome.permissions) return false;
  return chrome.permissions.contains({ origins: patterns });
}

async function ensureSiteOriginPermission(origin) {
  const normalized = normalizeSiteOrigin(origin);
  if (!normalized) throw new Error("请输入 HTTPS 目标域名");
  const patterns = originPermissionPatterns(normalized);
  if (await chrome.permissions.contains({ origins: patterns })) return true;
  const granted = await chrome.permissions.request({ origins: patterns });
  if (!granted) throw new Error(`未授权 ${normalized}`);
  return true;
}

async function ensureUrlFetchPermission(url) {
  let parsed = null;
  try {
    parsed = new URL(String(url || ""));
  } catch {
    return true;
  }
  if (!["http:", "https:"].includes(parsed.protocol)) return true;
  if (!chrome.permissions) return true;
  const origin = parsed.origin;
  const pattern = `${origin}/*`;
  if (await chrome.permissions.contains({ origins: [pattern] })) return true;
  const granted = await chrome.permissions.request({ origins: [pattern] });
  if (!granted) throw new Error(`未授权媒体域名 ${origin}`);
  return true;
}

function toggleFloatConsole() {
  const panel = $("float-console");
  panel.classList.toggle("collapsed");
  $("float-toggle").textContent = panel.classList.contains("collapsed") ? "海" : "×";
  $("float-toggle").title = panel.classList.contains("collapsed") ? "打开下载设置" : "收起下载设置";
}

async function expandBatchEntries(rawEntries, options, existingPids = new Set(), sourceHistory = {}) {
  const entries = [];
  const importSources = [];
  const seenPids = new Set(Array.from(existingPids || []).map((value) => String(value)));

  const addPost = (entry, source) => {
    const pid = String(entry && entry.pid || "").trim();
    if (!/^\d{4,}$/.test(pid) || seenPids.has(pid)) return false;
    const sourceOrigin = normalizeSiteOrigin(source && source.sourceOrigin || entry.sourceOrigin || "") || getSiteOrigin();
    seenPids.add(pid);
    entries.push({
      pid,
      url: `${sourceOrigin}/post/details?pid=${encodeURIComponent(pid)}`,
      sourceOrigin,
      sourceType: source && source.type || entry.sourceType || "post",
      sourceUid: source && source.uid || entry.sourceUid || "",
      sourceUrl: source && source.url || entry.sourceUrl || "",
      sourceTitle: source && source.title || entry.sourceTitle || "",
      sourceKey: source && source.key || getEntrySourceKey(entry),
      newFromScan: Boolean(source && source.newFromScan || entry.newFromScan),
    });
    return true;
  };

  for (const entry of rawEntries) {
    if (stopRequested) break;
    if (entry.type === "sell") {
      const historyRecord = getSourceHistoryRecord(entry, sourceHistory);
      const scan = await scanSellPage(entry, options, addPost, getKnownTopicIdsForEntry(entry, sourceHistory));
      restoreUndownloadedHistoryPosts(entry, historyRecord, addPost, scan, options);
      importSources.push(scan);
    } else {
      addPost(entry, {
        type: "post",
        pid: entry.pid,
        url: entry.url,
        sourceOrigin: entry.sourceOrigin,
        key: getEntrySourceKey(entry),
      });
    }
  }

  return { entries, importSources };
}

async function scanSellPage(entry, options, addPost, knownTopicIds = new Set()) {
  const uid = String(entry.uid || "").trim();
  const knownIds = new Set(Array.from(knownTopicIds || []).map((value) => String(value)));
  const scan = {
    type: "sell",
    uid,
    url: entry.url,
    sourceOrigin: normalizeSiteOrigin(entry.sourceOrigin || "") || getSiteOrigin(),
    listType: SELL_LIST_TYPE,
    videoOnly: Boolean(options.sellVideoOnly),
    incremental: knownIds.size > 0,
    knownBefore: knownIds.size,
    knownMatched: 0,
    discoveredTopicIds: [],
    restoredFromHistory: 0,
    status: "running",
    user: null,
    total: 0,
    limit: 0,
    pageCount: 0,
    scannedPages: 0,
    scannedTopics: 0,
    included: 0,
    excludedNoVideo: 0,
    duplicate: 0,
    topics: [],
    pages: [],
    error: "",
  };

  try {
    scan.user = await fetchUserInfo(uid, scan.sourceOrigin).catch(() => null);
    let page = 1;
    let knownPageCount = 0;

    while (!stopRequested) {
      setSummary(`${knownIds.size ? "刷新" : "扫描"}出售页 uid ${uid}：第 ${page}${knownPageCount ? `/${knownPageCount}` : ""} 页`);
      const data = await fetchSellTopics(uid, page, scan.sourceOrigin);
      const normalized = normalizeSellTopicsPage(data, page);
      let pageHitKnown = false;

      if (page === 1) {
        scan.total = normalized.total;
        scan.limit = normalized.limit;
        knownPageCount = normalized.pageCount;
        scan.pageCount = knownPageCount;
      }

      scan.scannedPages += 1;
      scan.scannedTopics += normalized.results.length;
      scan.pages.push({
        page,
        count: normalized.results.length,
        total: normalized.total,
        limit: normalized.limit,
      });

      for (const topic of normalized.results) {
        const topicId = String(topic && topic.topicId || "").trim();
        if (!/^\d{4,}$/.test(topicId)) continue;
        scan.discoveredTopicIds.push(topicId);

        if (knownIds.has(topicId)) {
          pageHitKnown = true;
          scan.knownMatched += 1;
          scan.duplicate += 1;
          scan.topics.push(makeSellTopicRecord(topic, "known", topicHasVideo(topic)));
          continue;
        }

        const hasVideo = topicHasVideo(topic);
        if (options.sellVideoOnly && !hasVideo) {
          scan.excludedNoVideo += 1;
          scan.topics.push(makeSellTopicRecord(topic, "excluded_no_video", hasVideo));
          continue;
        }

        const added = addPost({ pid: topicId }, {
          type: "sell",
          uid,
          url: entry.url,
          sourceOrigin: scan.sourceOrigin,
          key: getEntrySourceKey(entry),
          title: getSellUserName(scan.user) || "",
          newFromScan: true,
        });
        if (added) {
          scan.included += 1;
          scan.topics.push(makeSellTopicRecord(topic, "included", hasVideo));
        } else {
          scan.duplicate += 1;
          scan.topics.push(makeSellTopicRecord(topic, "duplicate", hasVideo));
        }
      }

      if (knownIds.size && pageHitKnown) break;
      if (knownPageCount && page >= knownPageCount) break;
      if (!knownPageCount && normalized.results.length === 0) break;
      page += 1;
      await sleep(SELL_SCAN_PAGE_DELAY_MS);
    }

    scan.status = stopRequested ? "stopped" : "ok";
    setSummary(`出售页 uid ${uid} 扫描完成：加入 ${scan.included} 条，排除无视频 ${scan.excludedNoVideo} 条`);
  } catch (error) {
    scan.status = "failed";
    scan.error = String(error && error.message || error);
    throw error;
  }
  return scan;
}

async function fetchTopic(pid, sourceOrigin = "") {
  const result = await pageFetch("topic", { pid, sourceOrigin });
  if (!result || typeof result !== "object") throw new Error("帖子接口解析失败");
  return result;
}

async function fetchAttachment(attachmentId, pid, sourceOrigin = "") {
  return pageFetch("attachment", { pid, attachmentId, sourceOrigin });
}

async function fetchSellTopics(uid, page, sourceOrigin = "") {
  const result = await pageFetch("sellTopics", {
    uid,
    page: Math.max(1, Number(page) || 1),
    listType: SELL_LIST_TYPE,
    sourceOrigin,
  });
  if (!result || typeof result !== "object") throw new Error("出售页列表接口解析失败");
  return result;
}

async function fetchUserInfo(uid, sourceOrigin = "") {
  return pageFetch("userInfo", { uid, sourceOrigin });
}

async function pageFetch(kind, payload) {
  const origin = normalizeSiteOrigin(payload && payload.sourceOrigin) || getSiteOrigin();
  await ensureSiteOriginPermission(origin);
  const tabId = await ensureHelperTab(payload && payload.pid, origin);
  await ensureContentHelper(tabId);
  for (let attempt = 1; attempt <= 5; attempt += 1) {
    try {
      const response = await chrome.tabs.sendMessage(tabId, {
        type: "HJBD_PAGE_FETCH",
        kind,
        ...payload,
      });
      if (!response || !response.ok) throw new Error(response && response.error || "page fetch failed");
      return response.data;
    } catch (error) {
      if (attempt === 5) throw error;
      await sleep(400 * attempt);
    }
  }
  throw new Error("page fetch failed");
}

async function ensureHelperTab(pid, origin = getSiteOrigin()) {
  origin = normalizeSiteOrigin(origin) || DEFAULT_SITE_ORIGIN;
  if (helperTabId) {
    try {
      const tab = await chrome.tabs.get(helperTabId);
      if (tab && isTabOnOrigin(tab, origin) && helperTabCreated && helperTabToken) {
        if ((await isOwnedHelperTab(helperTabId)) || (await markHelperTab(helperTabId, helperTabToken))) {
          return helperTabId;
        }
      }
    } catch {
      helperTabId = null;
      helperTabCreated = false;
      helperTabOrigin = "";
      helperTabToken = "";
    }
  }

  const url = pid
    ? `${origin}/post/details?pid=${encodeURIComponent(pid)}`
    : `${origin}/home`;
  const tab = await chrome.tabs.create({ url, active: false });
  helperTabId = tab.id;
  helperTabCreated = true;
  helperTabOrigin = origin;
  helperTabToken = makeHelperTabToken();
  await waitForTabComplete(helperTabId, 20000);
  await sleep(800);
  await markHelperTab(helperTabId, helperTabToken);
  return helperTabId;
}

function makeHelperTabToken() {
  return `${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 10)}`;
}

async function markHelperTab(tabId, token) {
  if (!tabId || !token) return false;
  try {
    await chrome.scripting.executeScript({
      target: { tabId },
      func: (value) => {
        document.documentElement.dataset.hjbdHelperTab = value;
      },
      args: [token],
    });
    return true;
  } catch {
    return false;
  }
}

async function isOwnedHelperTab(tabId) {
  if (!tabId || !helperTabCreated || !helperTabToken) return false;
  try {
    const result = await chrome.scripting.executeScript({
      target: { tabId },
      func: () => document.documentElement.dataset.hjbdHelperTab || "",
    });
    return Boolean(result && result[0] && result[0].result === helperTabToken);
  } catch {
    return false;
  }
}

function isTabOnOrigin(tab, origin) {
  try {
    return Boolean(tab && new URL(tab.url || "").origin === origin);
  } catch {
    return false;
  }
}

async function ensureContentHelper(tabId) {
  const tab = await chrome.tabs.get(tabId).catch(() => null);
  if (!tab || !isAllowedTabUrl(tab.url)) throw new Error("当前标签页不在允许注入范围");
  if (tabId === helperTabId && !(await isOwnedHelperTab(tabId))) {
    contentHelperInjectedTabs.delete(tabId);
    throw new Error("helper tab ownership lost");
  }
  if (contentHelperInjectedTabs.has(tabId)) return;
  try {
    await chrome.tabs.sendMessage(tabId, { type: "HJBD_PING" });
    contentHelperInjectedTabs.add(tabId);
    return;
  } catch {
    // Fall through and inject on mirror domains that are not covered by content_scripts.
  }
  await chrome.scripting.executeScript({
    target: { tabId },
    files: ["content-helper.js"],
  });
  contentHelperInjectedTabs.add(tabId);
}

function isAllowedTabUrl(url) {
  try {
    const parsed = new URL(String(url || ""));
    return parsed.protocol === "https:" && isAllowedTargetHost(parsed.hostname);
  } catch {
    return false;
  }
}

function waitForTabComplete(tabId, timeoutMs) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      chrome.tabs.onUpdated.removeListener(listener);
      reject(new Error("helper tab load timeout"));
    }, timeoutMs || 20000);

    function listener(updatedTabId, changeInfo) {
      if (updatedTabId !== tabId || changeInfo.status !== "complete") return;
      clearTimeout(timer);
      chrome.tabs.onUpdated.removeListener(listener);
      resolve();
    }

    chrome.tabs.onUpdated.addListener(listener);
    chrome.tabs.get(tabId).then((tab) => {
      if (tab.status === "complete") {
        clearTimeout(timer);
        chrome.tabs.onUpdated.removeListener(listener);
        resolve();
      }
    }).catch((error) => {
      clearTimeout(timer);
      chrome.tabs.onUpdated.removeListener(listener);
      reject(error);
    });
  });
}

async function closeHelperTab() {
  if (!helperTabId || !helperTabCreated) {
    helperTabId = null;
    helperTabCreated = false;
    helperTabOrigin = "";
    helperTabToken = "";
    return;
  }
  const tabId = helperTabId;
  const shouldRemove = await isOwnedHelperTab(tabId);
  helperTabId = null;
  helperTabCreated = false;
  helperTabOrigin = "";
  helperTabToken = "";
  contentHelperInjectedTabs.delete(tabId);
  if (shouldRemove) await chrome.tabs.remove(tabId).catch(() => {});
}

if (chrome.tabs && chrome.tabs.onRemoved) {
  chrome.tabs.onRemoved.addListener((tabId) => {
    contentHelperInjectedTabs.delete(tabId);
    if (tabId !== helperTabId) return;
    helperTabId = null;
    helperTabCreated = false;
    helperTabOrigin = "";
    helperTabToken = "";
  });
}

if (chrome.tabs && chrome.tabs.onUpdated) {
  chrome.tabs.onUpdated.addListener((tabId, changeInfo) => {
    if (changeInfo && changeInfo.status === "loading") contentHelperInjectedTabs.delete(tabId);
  });
}

function findVideoAttachment(topic) {
  return Array.isArray(topic && topic.attachments)
    ? topic.attachments.find((item) => item && item.category === "video")
    : null;
}

function applyTopicPublishedFields(item, topic) {
  const fields = getTopicPublishedFields(topic);
  item.publishedAtRaw = fields.publishedAtRaw;
  item.publishedAt = fields.publishedAt;
  item.publishedDate = fields.publishedDate;
  item.publishedSort = fields.publishedSort;
}

function getTopicPublishedFields(topic) {
  return normalizePublishedTime(firstText(
    topic && topic.createTime,
    topic && topic.createdAt,
    topic && topic.create_time,
    topic && topic.publishTime,
    topic && topic.publishedAt,
    topic && topic.postTime,
    topic && topic.time
  ));
}

function normalizePublishedTime(value) {
  const raw = cleanTitle(value);
  if (!raw) return emptyPublishedFields();

  let parts = null;
  const numeric = raw.match(/^\d{10,13}$/);
  if (numeric) {
    const number = Number(raw);
    const date = new Date(raw.length >= 13 ? number : number * 1000);
    parts = dateToPublishedParts(date);
  }

  if (!parts && !/(?:z|[+-]\d{2}:?\d{2})$/i.test(raw)) {
    const match = raw.match(/^(\d{4})[-/](\d{1,2})[-/](\d{1,2})(?:[ T](\d{1,2}):(\d{1,2})(?::(\d{1,2}))?)?/);
    if (match) {
      parts = {
        year: Number(match[1]),
        month: Number(match[2]),
        day: Number(match[3]),
        hour: Number(match[4] || 0),
        minute: Number(match[5] || 0),
        second: Number(match[6] || 0),
      };
    }
  }

  if (!parts) {
    parts = dateToPublishedParts(new Date(raw));
  }

  if (!parts) return emptyPublishedFields(raw);
  const yyyy = String(parts.year).padStart(4, "0");
  const mm = String(parts.month).padStart(2, "0");
  const dd = String(parts.day).padStart(2, "0");
  const hh = String(parts.hour).padStart(2, "0");
  const mi = String(parts.minute).padStart(2, "0");
  const ss = String(parts.second).padStart(2, "0");
  return {
    publishedAtRaw: raw,
    publishedAt: `${yyyy}-${mm}-${dd} ${hh}:${mi}:${ss}`,
    publishedDate: `${yyyy}-${mm}-${dd}`,
    publishedSort: `${yyyy}${mm}${dd}-${hh}${mi}${ss}`,
  };
}

function dateToPublishedParts(date) {
  if (!(date instanceof Date) || Number.isNaN(date.getTime())) return null;
  return {
    year: date.getFullYear(),
    month: date.getMonth() + 1,
    day: date.getDate(),
    hour: date.getHours(),
    minute: date.getMinutes(),
    second: date.getSeconds(),
  };
}

function emptyPublishedFields(raw = "") {
  return {
    publishedAtRaw: raw,
    publishedAt: "",
    publishedDate: "",
    publishedSort: "",
  };
}

function normalizeSellTopicsPage(data, requestedPage) {
  const pageInfo = data && typeof data.page === "object" ? data.page : {};
  const results = Array.isArray(data && data.results)
    ? data.results
    : Array.isArray(data && data.list)
      ? data.list
      : Array.isArray(data && data.items)
        ? data.items
        : [];
  const page = Number(pageInfo.page || requestedPage || 1);
  const limit = Number(pageInfo.limit || results.length || 0);
  const total = Number(pageInfo.total || 0);
  return {
    page,
    limit,
    total,
    pageCount: total && limit ? Math.ceil(total / limit) : 0,
    results,
  };
}

function topicHasVideo(topic) {
  if (!topic) return false;
  if (topic.hasVideo === true) return true;
  return Boolean(findVideoAttachment(topic));
}

function makeSellTopicRecord(topic, decision, hasVideo) {
  const published = getTopicPublishedFields(topic);
  return {
    topicId: topic && topic.topicId || null,
    title: cleanTitle(topic && topic.title || ""),
    publishedAtRaw: published.publishedAtRaw,
    publishedAt: published.publishedAt,
    publishedDate: published.publishedDate,
    publishedSort: published.publishedSort,
    newFromScan: decision === "included",
    hasVideo: Boolean(hasVideo),
    hasPic: Boolean(topic && topic.hasPic),
    hasAudio: Boolean(topic && topic.hasAudio),
    attachmentCount: Array.isArray(topic && topic.attachments) ? topic.attachments.length : 0,
    decision,
  };
}

function getAuthorName(topic) {
  const user = topic && topic.user;
  return firstText(
    user && user.name,
    user && user.username,
    user && user.userName,
    user && user.nickName,
    user && user.nickname,
    user && user.nick,
    user && user.displayName,
    topic && topic.username,
    topic && topic.userName,
    topic && topic.nickName,
    topic && topic.nickname,
    topic && topic.authorName
  );
}

function getAuthorId(topic) {
  const user = topic && topic.user;
  const value = user && (user.id || user.userId || user.uid) || topic && (topic.userId || topic.uid);
  return value == null ? "" : String(value);
}

function getSellUserName(userInfo) {
  const user = userInfo && userInfo.user || userInfo;
  return firstText(
    user && user.name,
    user && user.username,
    user && user.userName,
    user && user.nickName,
    user && user.nickname,
    user && user.nick,
    user && user.displayName
  );
}

function firstText(...values) {
  for (const value of values) {
    const text = cleanTitle(value);
    if (text) return text;
  }
  return "";
}

async function fetchManifest(url) {
  await ensureUrlFetchPermission(url);
  return withMediaRequestSlot(async () => {
    const response = await fetchWithTimeout(url, {
      credentials: getFetchCredentials(url),
      cache: "no-store",
      headers: { accept: "application/vnd.apple.mpegurl, application/x-mpegURL, */*" },
    }, 30000);
    const text = await response.text();
    return {
      url: response.url || url,
      status: response.status,
      ok: response.ok,
      contentType: response.headers.get("content-type") || "",
      text,
      analysis: analyzeManifest(text, response.url || url),
    };
  });
}

async function fetchMediaManifest(url, options = {}) {
  const manifest = await fetchManifest(url);
  return resolveMediaManifest(manifest, options);
}

async function resolveMediaManifest(manifest, options = {}) {
  if (isUsableManifest(manifest)) return manifest;
  if (!isMasterManifest(manifest)) return manifest;

  const depth = Number(options.masterDepth || 0);
  if (depth >= 2) return manifest;

  const variants = Array.from(new Set((manifest.analysis.variantUrls || []).filter(Boolean)));
  const maxVariants = clampInteger(options.maxVariants, 1, 12, 6);
  const variantConcurrency = clampInteger(options.variantConcurrency, 1, 6, 3);
  const checkedVariants = [];
  let best = null;
  let nextIndex = 0;

  async function worker() {
    while (nextIndex < Math.min(maxVariants, variants.length)) {
      const url = variants[nextIndex];
      nextIndex += 1;
      try {
        const child = await resolveMediaManifest(await fetchManifest(url), {
          ...options,
          masterDepth: depth + 1,
        });
        checkedVariants.push({
          url,
          status: child.status,
          ok: isUsableManifest(child),
          segments: child.analysis && child.analysis.segmentEntries ? child.analysis.segmentEntries.length : 0,
          seconds: child.analysis ? Math.round(child.analysis.totalDurationSeconds || 0) : 0,
        });
        if (isUsableManifest(child) && (!best || isBetterVariantManifest(child, best))) {
          best = child;
        }
      } catch (error) {
        checkedVariants.push({
          url,
          ok: false,
          error: String(error && error.message || error),
        });
      }
    }
  }

  await Promise.all(Array.from({ length: Math.min(variantConcurrency, variants.length, maxVariants) }, worker));

  manifest.checkedVariants = checkedVariants;
  return best || manifest;
}

function isBetterVariantManifest(candidate, current) {
  const candidateSeconds = Number(candidate && candidate.analysis && candidate.analysis.totalDurationSeconds || 0);
  const currentSeconds = Number(current && current.analysis && current.analysis.totalDurationSeconds || 0);
  if (candidateSeconds !== currentSeconds) return candidateSeconds > currentSeconds;
  const candidateSegments = Number(candidate && candidate.analysis && candidate.analysis.segmentEntries && candidate.analysis.segmentEntries.length || 0);
  const currentSegments = Number(current && current.analysis && current.analysis.segmentEntries && current.analysis.segmentEntries.length || 0);
  return candidateSegments > currentSegments;
}

function analyzeManifest(text, baseUrl) {
  const body = String(text || "");
  const lines = body.split(/\r?\n/).map((line) => line.trim()).filter(Boolean);
  const durations = Array.from(body.matchAll(/#EXTINF:([0-9.]+)/g)).map((match) => Number(match[1]));
  const segmentEntries = [];
  const variantUrls = [];
  const keyMethods = new Set();
  let expectVariant = false;
  let currentKey = null;
  let currentMap = null;
  let pendingByteRange = null;
  let pendingDuration = 0;
  let byteRangeOffsetByUrl = new Map();
  let segmentIndex = 0;
  const mediaSequence = Number((body.match(/#EXT-X-MEDIA-SEQUENCE:(\d+)/) || [])[1] || 0);

  for (const line of lines) {
    if (/^#EXT-X-STREAM-INF/i.test(line)) {
      expectVariant = true;
      continue;
    }
    if (/^#EXT-X-KEY:/i.test(line)) {
      currentKey = parseKeyLine(line, baseUrl);
      if (currentKey && currentKey.method) keyMethods.add(currentKey.method);
      continue;
    }
    if (/^#EXT-X-MAP:/i.test(line)) {
      currentMap = parseMapLine(line, baseUrl);
      continue;
    }
    if (/^#EXT-X-BYTERANGE:/i.test(line)) {
      pendingByteRange = parseByteRangeLine(line);
      continue;
    }
    if (/^#EXTINF:/i.test(line)) {
      pendingDuration = Number((line.match(/^#EXTINF:([0-9.]+)/i) || [])[1] || 0);
      continue;
    }
    if (line.startsWith("#")) continue;
    const resolved = resolveMediaUrl(line, baseUrl);
    if (!resolved) continue;
    if (expectVariant) {
      variantUrls.push(resolved);
      expectVariant = false;
      continue;
    }
    const sequence = mediaSequence + segmentIndex;
    const byteRange = resolveByteRange(pendingByteRange, resolved, byteRangeOffsetByUrl);
    segmentEntries.push({
      url: resolved,
      sequence,
      duration: Number.isFinite(pendingDuration) ? pendingDuration : 0,
      byteRange,
      map: currentMap,
      key: currentKey && currentKey.method === "AES-128"
        ? {
          method: currentKey.method,
          uri: currentKey.uri,
          iv: currentKey.iv || makeDefaultIvHex(sequence),
          raw: currentKey.raw || "",
        }
        : null,
    });
    segmentIndex += 1;
    pendingByteRange = null;
    pendingDuration = 0;
  }

  const hasMap = /#EXT-X-MAP/i.test(body);
  const hasByteRange = /#EXT-X-BYTERANGE/i.test(body);
  const hasFmp4Segments = segmentEntries.some((entry) => /\.(?:m4s|mp4|cmfv|m4v)(?:[?#]|$)/i.test(entry.url));

  return {
    hasExtM3u: /#EXTM3U/.test(body),
    segmentCount: durations.length || segmentEntries.length,
    totalDurationSeconds: durations.reduce((sum, value) => sum + (Number.isFinite(value) ? value : 0), 0),
    targetDuration: Number((body.match(/#EXT-X-TARGETDURATION:(\d+)/) || [])[1] || 0),
    mediaSequence,
    hasEndList: /#EXT-X-ENDLIST/.test(body),
    hasKey: /#EXT-X-KEY/i.test(body),
    hasMap,
    hasByteRange,
    mediaContainer: hasMap || hasFmp4Segments ? "mp4" : "ts",
    keyMethods: Array.from(keyMethods),
    segmentEntries,
    variantUrls,
  };
}

function parseMapLine(line, baseUrl) {
  const attrs = parseAttributeList(String(line || "").replace(/^#EXT-X-MAP:/i, ""));
  const uri = attrs.URI ? resolveMediaUrl(attrs.URI, baseUrl) : "";
  return uri ? {
    uri,
    byteRange: attrs.BYTERANGE ? parseByteRangeLine(`#EXT-X-BYTERANGE:${attrs.BYTERANGE}`) : null,
    raw: line,
  } : null;
}

function parseByteRangeLine(line) {
  const text = String(line || "").replace(/^#EXT-X-BYTERANGE:/i, "").trim();
  const match = text.match(/^(\d+)(?:@(\d+))?$/);
  if (!match) return null;
  return {
    length: Number(match[1]),
    offset: match[2] == null ? null : Number(match[2]),
  };
}

function resolveByteRange(range, url, offsets) {
  if (!range || !Number.isFinite(range.length) || range.length <= 0) return null;
  const previousEnd = offsets.get(url) || 0;
  const offset = range.offset == null ? previousEnd : Number(range.offset);
  offsets.set(url, offset + range.length);
  return { offset, length: range.length };
}

function parseKeyLine(line, baseUrl) {
  const raw = String(line || "");
  const attrs = parseAttributeList(raw.replace(/^#EXT-X-KEY:/i, ""));
  const method = String(attrs.METHOD || "").toUpperCase();
  if (!method || method === "NONE") return null;
  return {
    method,
    uri: attrs.URI ? resolveMediaUrl(attrs.URI, baseUrl) : "",
    iv: attrs.IV ? normalizeIvHex(attrs.IV) : "",
    raw,
  };
}

function parseAttributeList(text) {
  const attrs = {};
  const pattern = /([A-Z0-9-]+)=("(?:[^"\\]|\\.)*"|[^,]*)/gi;
  let match = pattern.exec(text);
  while (match) {
    const key = String(match[1] || "").toUpperCase();
    let value = match[2] || "";
    if (value.startsWith("\"") && value.endsWith("\"")) value = value.slice(1, -1);
    attrs[key] = value;
    match = pattern.exec(text);
  }
  return attrs;
}

function deriveM3u8FromSegmentEntries(segmentEntries, sourceUrl) {
  return deriveM3u8Candidates(segmentEntries, sourceUrl)[0] || "";
}

function deriveM3u8Candidates(segmentEntries, sourceUrl) {
  const candidates = [];
  const seen = new Set();

  const addCandidate = (url) => {
    if (!url || seen.has(url)) return;
    seen.add(url);
    candidates.push(url);
  };

  const makeCleanUrl = (url, replacer) => {
    try {
      const parsed = new URL(url, sourceUrl);
      replacer(parsed);
      parsed.search = "";
      parsed.hash = "";
      addCandidate(parsed.href);
    } catch {
      // ignore malformed URL
    }
  };

  for (const entry of (segmentEntries || []).slice(0, 8)) {
    const url = entry && entry.url || "";
    if (!url) continue;
    try {
      const segmentUrl = new URL(url, sourceUrl);
      const name = segmentUrl.pathname.split("/").pop() || "";
      const numbered = name.match(/^(.+?)(\d+)\.(?:ts|m4s|mp4|cmfv)$/i);
      if (numbered) {
        makeCleanUrl(segmentUrl.href, (parsed) => {
          parsed.pathname = parsed.pathname.replace(/[^/]+$/, `${numbered[1]}.m3u8`);
        });
      }

      const stem = name.replace(/\.[^.]+$/i, "");
      for (const suffixPattern of [
        /(?:[-_.]?preview|[-_.]?试看|[-_.]?sample|[-_.]?trailer)$/i,
        /(?:[-_.]?seg(?:ment)?[-_.]?\d+)$/i,
        /(?:[-_.]?\d+)$/i,
      ]) {
        const base = stem.replace(suffixPattern, "");
        if (base && base !== stem) {
          makeCleanUrl(segmentUrl.href, (parsed) => {
            parsed.pathname = parsed.pathname.replace(/[^/]+$/, `${base}.m3u8`);
          });
        }
      }

      for (const filename of ["index.m3u8", "playlist.m3u8", "main.m3u8", "master.m3u8"]) {
        makeCleanUrl(segmentUrl.href, (parsed) => {
          parsed.pathname = parsed.pathname.replace(/[^/]+$/, filename);
        });
      }
    } catch {
      // ignore malformed URL
    }
  }

  if (sourceUrl) {
    try {
      const parsed = new URL(sourceUrl);
      const name = parsed.pathname.split("/").pop() || "";
      const stem = name.replace(/\.m3u8$/i, "");
      for (const pattern of [/(?:[-_.]?preview|[-_.]?试看|[-_.]?sample|[-_.]?trailer)$/i]) {
        const base = stem.replace(pattern, "");
        if (base && base !== stem) {
          parsed.pathname = parsed.pathname.replace(/[^/]+$/, `${base}.m3u8`);
          parsed.search = "";
          parsed.hash = "";
          addCandidate(parsed.href);
          break;
        }
      }
    } catch {
      // ignore malformed URL
    }
  }

  return candidates;
}

function isBetterFullManifest(full, preview, expectedSeconds) {
  if (!isUsableManifest(full)) return false;
  const fullSeconds = Number(full.analysis.totalDurationSeconds || 0);
  const previewSeconds = Number(preview && preview.analysis && preview.analysis.totalDurationSeconds || 0);
  const fullSegments = Number(full.analysis.segmentEntries.length || 0);
  const previewSegments = Number(preview && preview.analysis && preview.analysis.segmentEntries.length || 0);
  if (expectedSeconds && Math.abs(fullSeconds - expectedSeconds) <= Math.max(8, expectedSeconds * 0.04)) return true;
  return fullSeconds >= Math.max(45, previewSeconds + 10)
    || fullSegments >= Math.max(previewSegments + 3, Math.ceil(previewSegments * 1.5));
}

async function writeSegmentsToFile(fileHandle, segments, item, options) {
  if (!Array.isArray(segments) || !segments.length) {
    throw new Error("manifest has no media segments");
  }

  const writable = await fileHandle.createWritable({ keepExistingData: false });
  const cryptoContext = { keyCache: activeMediaKeyCache || new Map(), importedKeyCache: new Map() };
  const initSegmentCache = new Map();
  const total = segments.length;
  const outputType = getManifestMediaContainer({ analysis: { segmentEntries: segments } }) === "mp4" ? "video/mp4" : "video/mp2t";
  const configuredConcurrency = clampInteger(options.segmentConcurrency, 1, 32, DEFAULT_SEGMENT_CONCURRENCY);
  const adaptive = Boolean(options.adaptiveConcurrency);
  const minConcurrency = adaptive ? Math.max(2, Math.floor(configuredConcurrency / 2)) : configuredConcurrency;
  const maxConcurrency = adaptive ? Math.min(32, Math.max(configuredConcurrency + 8, configuredConcurrency)) : configuredConcurrency;
  let targetConcurrency = configuredConcurrency;
  const started = Date.now();
  const results = new Map();
  let nextToStart = 0;
  let nextToWrite = 0;
  let active = 0;
  let waiters = [];
  let blockedWaits = 0;
  let lastTuneAt = started;
  let lastTuneBytes = 0;
  let lastTuneWritten = 0;
  let lastTuneBlocked = 0;
  let speedEma = 0;
  let pendingWriteChunks = [];
  let pendingWriteBytes = 0;
  const flushThresholdBytes = WRITE_FLUSH_THRESHOLD_BYTES;
  let closed = false;
  const stopSignal = activeStopController && activeStopController.signal;

  function signal() {
    const pending = waiters;
    waiters = [];
    for (const resolve of pending) resolve();
  }

  function waitForChange() {
    return new Promise((resolve) => {
      waiters.push(resolve);
      if (stopSignal) stopSignal.addEventListener("abort", resolve, { once: true });
    });
  }

  function currentBufferWindow() {
    return Math.max(adaptive ? 192 : 128, targetConcurrency * 8);
  }

  function pump() {
    while (
      !stopRequested
      && active < targetConcurrency
      && nextToStart < total
      && nextToStart < nextToWrite + currentBufferWindow()
    ) {
      const index = nextToStart;
      nextToStart += 1;
      active += 1;
      loadSegment(index).finally(() => {
        active -= 1;
        signal();
      });
    }
  }

  async function loadSegment(index) {
    const segment = segments[index];
    try {
      const chunks = [];
      const initChunk = await getInitSegmentChunk(segment, segments[index - 1]);
      if (initChunk) chunks.push(initChunk);
      const buffer = await fetchSegmentBufferWithBackup(segment);
      const bytes = segment.key && segment.key.method === "AES-128"
        ? new Uint8Array(await decryptAes128Segment(buffer, segment.key, cryptoContext))
        : new Uint8Array(buffer);
      chunks.push(bytes);
      results.set(index, { bytes: chunks.length === 1 ? chunks[0] : chunks });
    } catch (error) {
      results.set(index, { error: addSegmentErrorContext(error, segment, index) });
    }
  }

  async function fetchSegmentBufferWithBackup(segment) {
    let settled = false;
    let timer = null;
    const fetchSegment = () => fetchArrayBufferWithRetry(segment.url, options.segmentTimeoutSeconds * 1000, {
      byteRange: segment.byteRange,
    });
    const primary = fetchSegment();
    const backup = new Promise((resolve, reject) => {
      timer = window.setTimeout(() => {
        if (settled || stopRequested) return;
        fetchSegment().then(resolve, reject);
      }, Math.max(SLOW_SEGMENT_MIN_PROGRESS_MS, Math.min(SLOW_SEGMENT_BACKUP_AFTER_MS, options.segmentTimeoutSeconds * 500)));
    });
    try {
      return await Promise.race([primary, backup]);
    } finally {
      settled = true;
      if (timer) window.clearTimeout(timer);
    }
  }

  async function getInitSegmentChunk(segment, previousSegment) {
    const map = segment && segment.map;
    if (!map || !map.uri) return null;
    if (makeMapCacheKey(map) === makeMapCacheKey(previousSegment && previousSegment.map)) return null;
    const key = makeMapCacheKey(map);
    if (initSegmentCache.has(key)) return initSegmentCache.get(key);
    const buffer = await fetchArrayBufferWithRetry(map.uri, options.segmentTimeoutSeconds * 1000, {
      byteRange: map.byteRange,
      accept: "video/mp4, application/octet-stream, */*",
    });
    const bytes = segment && segment.key && segment.key.method === "AES-128"
      ? new Uint8Array(await decryptAes128Segment(buffer, segment.key, cryptoContext))
      : new Uint8Array(buffer);
    initSegmentCache.set(key, bytes);
    return bytes;
  }

  async function queueWrite(bytes) {
    const chunks = Array.isArray(bytes) ? bytes : [bytes];
    for (const chunk of chunks) {
      if (!chunk) continue;
      pendingWriteChunks.push(chunk);
      pendingWriteBytes += chunk.byteLength || chunk.size || 0;
      item.bytes += chunk.byteLength || chunk.size || 0;
    }
    if (pendingWriteBytes >= flushThresholdBytes) await flushWrites();
  }

  async function flushWrites() {
    if (!pendingWriteChunks.length) return;
    const chunks = pendingWriteChunks;
    pendingWriteChunks = [];
    pendingWriteBytes = 0;
    await writable.write(new Blob(chunks, { type: outputType }));
  }

  function tuneConcurrency() {
    if (!adaptive) return;
    const now = Date.now();
    const writtenDelta = nextToWrite - lastTuneWritten;
    if (now - lastTuneAt < 2500 && writtenDelta < 24) return;

    const seconds = Math.max(0.1, (now - lastTuneAt) / 1000);
    const deltaBytes = item.bytes - lastTuneBytes;
    const speed = deltaBytes / seconds;
    const blockedDelta = blockedWaits - lastTuneBlocked;
    const bufferPressure = results.size > currentBufferWindow() * 0.75;
    const speedDropped = speedEma > 0 && speed < speedEma * 0.72;

    if ((speedDropped || bufferPressure) && targetConcurrency > minConcurrency) {
      targetConcurrency = Math.max(minConcurrency, targetConcurrency - 2);
    } else if (blockedDelta > 1 && targetConcurrency < maxConcurrency) {
      targetConcurrency = Math.min(maxConcurrency, targetConcurrency + 2);
    } else if (blockedDelta === 0 && speedEma > 0 && speed > speedEma * 1.08 && targetConcurrency < maxConcurrency) {
      targetConcurrency = Math.min(maxConcurrency, targetConcurrency + 1);
    }

    speedEma = speedEma ? speedEma * 0.7 + speed * 0.3 : speed;
    lastTuneAt = now;
    lastTuneBytes = item.bytes;
    lastTuneWritten = nextToWrite;
    lastTuneBlocked = blockedWaits;
  }

  try {
    pump();
    while (nextToWrite < total) {
      throwIfStopRequested();

      const result = results.get(nextToWrite);
      if (!result) {
        blockedWaits += 1;
        tuneConcurrency();
        pump();
        await waitForChange();
        continue;
      }

      results.delete(nextToWrite);
      if (result.error) {
        throw new Error(`分片 ${nextToWrite + 1}/${total} 失败：${String(result.error && result.error.message || result.error)}`);
      }

      await queueWrite(result.bytes);
      nextToWrite += 1;
      item.progress = 18 + Math.round((nextToWrite / Math.max(1, total)) * 80);
      tuneConcurrency();
      item.message = `写入分片 ${nextToWrite}/${total} · 并发 ${targetConcurrency}${adaptive ? " 自适应" : ""} · ${formatBytes(item.bytes)} · ${formatSpeed(item.bytes, started)}`;
      scheduleRender();
      pump();
    }
    await flushWrites();
    await writable.close();
    closed = true;
  } finally {
    if (!closed && writable.abort) await writable.abort().catch(() => {});
  }
}

function addSegmentErrorContext(error, segment, index) {
  const message = String(error && error.message || error || "unknown segment error");
  const parts = [`segmentIndex=${index}`];
  if (segment && segment.url) parts.push(`segmentUrl=${segment.url}`);
  if (segment && segment.byteRange) parts.push(`byteRange=${segment.byteRange.offset}+${segment.byteRange.length}`);
  if (segment && segment.map && segment.map.uri) parts.push(`mapUrl=${segment.map.uri}`);
  if (segment && segment.key && segment.key.uri) parts.push(`keyUrl=${segment.key.uri}`);
  if (segment && segment.key && segment.key.raw) parts.push(`keyLine=${segment.key.raw}`);
  return new Error(`${message} | ${parts.join(" | ")}`);
}

function makeMapCacheKey(map) {
  if (!map || !map.uri) return "";
  const range = map.byteRange ? `${map.byteRange.offset || 0}+${map.byteRange.length || 0}` : "full";
  return `${map.uri}#${range}`;
}

function isRetryableMediaFetchError(error) {
  const message = String(error && error.message || error || "");
  return isStaleMediaFetchError(error)
    || /\bmanifest (?:不可用|刷新后仍不可用)：?HTTP (?:403|404)\b/i.test(message);
}

function isStaleMediaFetchError(error) {
  const status = Number(error && error.status || 0);
  if (status === 403 || status === 404) return true;
  const message = String(error && error.message || error || "");
  return /\b(?:key|segment) HTTP (?:403|404)\b/i.test(message);
}

function summarizeError(error) {
  return String(error && error.message || error || "请求失败").slice(0, 240);
}

async function fetchArrayBufferWithRetry(url, timeoutMs, requestOptions = {}) {
  await ensureUrlFetchPermission(url);
  const byteRange = requestOptions && requestOptions.byteRange;
  let lastError = null;
  for (let attempt = 1; attempt <= 3; attempt += 1) {
    try {
      return await withMediaRequestSlot(async () => {
        const headers = { accept: requestOptions.accept || "video/mp2t, video/mp4, application/octet-stream, */*" };
        if (byteRange) headers.Range = `bytes=${byteRange.offset}-${byteRange.offset + byteRange.length - 1}`;
        const response = await fetchWithTimeout(url, {
          credentials: getFetchCredentials(url),
          cache: "no-store",
          headers,
        }, timeoutMs);
        if (byteRange && response.status !== 206) {
          const error = new Error(`segment range HTTP ${response.status} ${url}`);
          error.status = response.status;
          throw error;
        }
        if (!response.ok) {
          const error = new Error(`segment HTTP ${response.status} ${url}`);
          error.status = response.status;
          throw error;
        }
        return response.arrayBuffer();
      });
    } catch (error) {
      lastError = error;
      if (isStaleMediaFetchError(error)) throw error;
      if (attempt < 3) await sleep(500 * attempt);
    }
  }
  throw lastError || new Error("segment fetch failed");
}

async function decryptAes128Segment(buffer, keyInfo, cryptoContext) {
  if (!keyInfo || !keyInfo.uri) throw new Error("missing AES-128 key uri");
  let imported = cryptoContext.importedKeyCache.get(keyInfo.uri);
  if (!imported) {
    const keyBytes = await fetchKeyBytes(keyInfo.uri, cryptoContext);
    imported = await crypto.subtle.importKey("raw", keyBytes, { name: "AES-CBC" }, false, ["decrypt"]);
    cryptoContext.importedKeyCache.set(keyInfo.uri, imported);
  }
  return crypto.subtle.decrypt({ name: "AES-CBC", iv: hexToBytes(keyInfo.iv) }, imported, buffer);
}

async function fetchKeyBytes(url, cryptoContext) {
  let bytes = cryptoContext.keyCache.get(url);
  if (bytes) return bytes;
  await ensureUrlFetchPermission(url);
  bytes = await withMediaRequestSlot(async () => {
    const response = await fetchWithTimeout(url, {
      credentials: getFetchCredentials(url),
      cache: "no-store",
      headers: { accept: "application/octet-stream, */*" },
    }, 30000);
    if (!response.ok) {
      const error = new Error(`key HTTP ${response.status} ${url}`);
      error.status = response.status;
      throw error;
    }
    return new Uint8Array(await response.arrayBuffer());
  });
  if (bytes.byteLength !== 16) throw new Error(`invalid AES-128 key length: ${bytes.byteLength}`);
  cryptoContext.keyCache.set(url, bytes);
  return bytes;
}

async function fetchWithTimeout(url, options, timeoutMs) {
  const controller = new AbortController();
  const stopSignal = activeStopController && activeStopController.signal;
  const abort = () => controller.abort();
  if (stopSignal) {
    if (stopSignal.aborted) controller.abort();
    else stopSignal.addEventListener("abort", abort, { once: true });
  }
  const timer = setTimeout(() => controller.abort(), timeoutMs || 30000);
  try {
    return await fetch(url, { ...options, signal: controller.signal });
  } finally {
    clearTimeout(timer);
    if (stopSignal) stopSignal.removeEventListener("abort", abort);
  }
}

function getFetchCredentials(url) {
  try {
    const target = normalizeSiteOrigin(getSiteOrigin());
    return target && new URL(String(url || "")).origin === target ? "include" : "omit";
  } catch {
    return "omit";
  }
}

async function getOutputDirectory(root, author, options) {
  if (!options.byAuthor) return root;
  return root.getDirectoryHandle(sanitizePathPart(author || "unknown_author"), { create: true });
}

async function prepareFileHandle(dir, desiredName, conflictMode, ext = ".ts") {
  let name = ensureSafeExtension(desiredName, ext);
  const existing = await getExistingFileInfo(dir, name);
  if (existing && existing.size > 0 && conflictMode === "skip") {
    return { skipped: true, name, handle: null, size: existing.size };
  }
  if (existing && existing.size > 0 && conflictMode === "rename") {
    name = await uniqueFilename(dir, name);
  }
  const temp = await createUniqueTempFileHandle(dir, `${name}.part`);
  return {
    skipped: false,
    name,
    tempName: temp.name,
    replaceExistingEmpty: Boolean(existing && existing.size === 0),
    allowOverwriteFinal: conflictMode === "overwrite",
    handle: temp.handle,
  };
}

async function commitPreparedFile(dir, prepared) {
  if (!prepared || prepared.skipped || !prepared.tempName || prepared.tempName === prepared.name) return;
  const tempHandle = prepared.handle || await dir.getFileHandle(prepared.tempName);
  const initialExisting = await getExistingFileInfo(dir, prepared.name).catch(() => null);
  if (initialExisting && !canReplacePreparedFinal(prepared, initialExisting)) {
    throw new Error(`目标文件仍然存在，取消覆盖：${prepared.name}`);
  }

  if (typeof tempHandle.move === "function") {
    try {
      if (initialExisting) await removeEntryIfExists(dir, prepared.name);
      await tempHandle.move(dir, prepared.name);
      return;
    } catch (error) {
      // Fall back to stream copy below; move() availability differs across Chrome versions.
      prepared.moveError = String(error && error.message || error);
    }
  }

  const finalExisting = await getExistingFileInfo(dir, prepared.name).catch(() => null);
  if (finalExisting && !canReplacePreparedFinal(prepared, finalExisting)) {
    throw new Error(`目标文件仍然存在，取消覆盖：${prepared.name}`);
  }
  if (finalExisting) await removeEntryIfExists(dir, prepared.name);
  const tempFile = await tempHandle.getFile();
  const finalHandle = await dir.getFileHandle(prepared.name, { create: true });
  const writable = await finalHandle.createWritable({ keepExistingData: false });
  try {
    await tempFile.stream().pipeTo(writable);
  } catch (error) {
    if (writable.abort) await writable.abort().catch(() => {});
    throw error;
  }
  await removeEntryIfExists(dir, prepared.tempName);
}

function canReplacePreparedFinal(prepared, existing) {
  if (!existing) return true;
  return Boolean(prepared && (prepared.allowOverwriteFinal || (prepared.replaceExistingEmpty && existing.size === 0)));
}

async function cleanupPreparedFile(dir, prepared) {
  if (!prepared || prepared.skipped) return;
  if (prepared.tempName) await removeEntryIfExists(dir, prepared.tempName);
  if (prepared.replaceExistingEmpty) {
    const existing = await getExistingFileInfo(dir, prepared.name).catch(() => null);
    if (existing && existing.size === 0) await removeEntryIfExists(dir, prepared.name);
  }
}

async function removeEntryIfExists(dir, name) {
  if (!dir || !name) return;
  try {
    await dir.removeEntry(name);
  } catch (error) {
    if (!error || error.name !== "NotFoundError") throw error;
  }
}

async function writeTextFile(dir, desiredName, text, conflictMode) {
  let name = ensureSafeExtension(desiredName, ".m3u8");
  const exists = await fileExists(dir, name);
  if (exists && conflictMode === "skip") return { skipped: true, name };
  if (exists && conflictMode === "rename") name = await uniqueFilename(dir, name);
  const handle = await dir.getFileHandle(name, { create: true });
  const writable = await handle.createWritable({ keepExistingData: false });
  await writable.write(text);
  await writable.close();
  return { skipped: false, name };
}

async function fileExists(dir, name) {
  return Boolean(await getExistingFileInfo(dir, name));
}

async function getExistingFileInfo(dir, name) {
  try {
    const handle = await dir.getFileHandle(name);
    const file = await handle.getFile();
    return { name, size: Number(file && file.size || 0), lastModified: Number(file && file.lastModified || 0) };
  } catch (error) {
    if (error && error.name === "NotFoundError") return null;
    throw error;
  }
}

async function syncLocalDownloadMatchesForItems(items, options) {
  let matched = 0;
  let missing = 0;
  for (const item of items || []) {
    const result = await syncLocalDownloadMatchForItem(item, options);
    if (result === "downloaded") matched += 1;
    if (result === "missing") missing += 1;
  }
  return { matched, missing };
}

async function syncLocalDownloadMatchForItem(item, options) {
  if (!isLocalDownloadCheckCandidate(item)) return "";
  const match = await findLocalDownloadedFile(item, options);
  if (match) {
    applyLocalDownloadMatch(item, match);
    await markItemDownloadedInHistory(item).catch(() => {});
    return "downloaded";
  }
  applyLocalDownloadMissing(item);
  await markItemParsedInHistory(item).catch(() => {});
  return "missing";
}

function isLocalDownloadCheckCandidate(item) {
  return Boolean(item && item.pid && !["running", "excluded", "failed", "stopped", "skipped"].includes(item.status));
}

async function findLocalDownloadedFile(item, options) {
  if (!rootHandle) return null;
  const dirs = [];
  const seen = new Set();

  const addDir = async (dir, folder) => {
    if (!dir) return;
    const key = folder || "__root__";
    if (seen.has(key)) return;
    seen.add(key);
    dirs.push({ dir, folder });
  };

  await addDir(await getDirectoryByOutputFolder(item.outputFolder), item.outputFolder || rootHandle.name);
  await addDir(await getExistingOutputDirectory(rootHandle, item.author, options), options && options.byAuthor ? sanitizePathPart(item.author || "unknown_author") : rootHandle.name);

  for (const { dir, folder } of dirs) {
    if (item.outputFile) {
      const matched = await getExistingMediaFile(dir, item.outputFile, folder);
      if (matched) return matched;
    }
    if (item.title && item.author && item.seconds) {
      const expected = ensureSafeExtension(renderNameTemplate(options.nameTemplate, item), ".ts");
      const matched = await getExistingMediaFile(dir, expected, folder);
      if (matched) return matched;
    }
    const byPid = await findDownloadedFileByPid(dir, item.pid, folder);
    if (byPid) return byPid;
  }

  return null;
}

async function getDirectoryByOutputFolder(folder) {
  if (!rootHandle) return null;
  const name = String(folder || "").trim();
  if (!name || name === rootHandle.name) return rootHandle;
  try {
    return await rootHandle.getDirectoryHandle(name);
  } catch {
    return null;
  }
}

async function getExistingOutputDirectory(root, author, options) {
  if (!root) return null;
  if (!options || !options.byAuthor) return root;
  try {
    return await root.getDirectoryHandle(sanitizePathPart(author || "unknown_author"));
  } catch {
    return null;
  }
}

async function getExistingMediaFile(dir, name, folder) {
  if (!dir || !name || !isDownloadedMediaName(name)) return null;
  try {
    const handle = await dir.getFileHandle(name);
    const file = await handle.getFile();
    if (!file || !file.size) return null;
    return { name, folder, size: file.size, lastModified: file.lastModified || 0 };
  } catch {
    return null;
  }
}

async function findDownloadedFileByPid(dir, pid, folder) {
  if (!dir || !pid) return null;
  let best = null;
  for await (const [name, handle] of dir.entries()) {
    if (!handle || handle.kind !== "file") continue;
    if (!isDownloadedMediaName(name) || !isFileNameForPid(name, pid)) continue;
    const file = await handle.getFile().catch(() => null);
    if (!file || !file.size) continue;
    const candidate = { name, folder, size: file.size, lastModified: file.lastModified || 0 };
    if (!best || candidate.lastModified > best.lastModified) best = candidate;
  }
  return best;
}

function isFileNameForPid(name, pid) {
  const value = String(pid || "").trim();
  if (!/^\d{4,}$/.test(value)) return false;
  const base = String(name || "").replace(/\.[^.]+$/, "");
  const escaped = escapeRegExp(value);
  return new RegExp(`(?:^|[^0-9])帖子\\s*${escaped}(?:[^0-9]|$)`).test(base)
    || new RegExp(`(?:^|[^0-9])pid\\s*${escaped}(?:[^0-9]|$)`, "i").test(base)
    || new RegExp(`(?:^|[^0-9])${escaped}(?:[^0-9]|$)`).test(base);
}

function isDownloadedMediaName(name) {
  return /\.(ts|mp4|m4v|mov|mkv)$/i.test(String(name || ""));
}

function applyLocalDownloadMatch(item, match) {
  item.status = "ok";
  item.canDownload = false;
  item.selected = false;
  item.localDownloadStatus = "downloaded";
  item.localDownloadMatched = true;
  item.bytes = Number(item.bytes || match.size || 0);
  item.outputFolder = match.folder || item.outputFolder || "";
  item.outputFile = match.name || item.outputFile || "";
  item.progress = 100;
  item.message = "本地文件已匹配";
}

function applyLocalDownloadMissing(item) {
  item.localDownloadStatus = item.newFromScan ? "new_missing" : "missing";
  item.localDownloadMatched = false;
  if (item.status === "ok") {
    item.status = item.selectedManifestKind === "preview" ? "preview" : "parsed";
    item.canDownload = Boolean(item.selectedManifestUrl);
    item.selected = Boolean(item.canDownload && item.newFromScan && item.selectedManifestKind === "full");
    item.message = "本地未匹配到已下载文件";
  }
}

async function uniqueFilename(dir, name) {
  const dot = name.lastIndexOf(".");
  const base = dot > 0 ? name.slice(0, dot) : name;
  const ext = dot > 0 ? name.slice(dot) : "";
  for (let index = 2; index < 10000; index += 1) {
    const candidate = `${base} (${index})${ext}`;
    if (!(await fileExists(dir, candidate))) return candidate;
  }
  throw new Error("无法生成唯一文件名");
}

async function uniqueTempFilename(dir, name) {
  const base = sanitizePathPart(name || `download-${Date.now()}.part`);
  for (let index = 0; index < 10000; index += 1) {
    const suffix = index ? `.${index}` : "";
    const candidate = `${base}.${Date.now()}${suffix}.tmp`;
    if (!(await fileExists(dir, candidate))) return candidate;
  }
  throw new Error("无法生成临时文件名");
}

async function createUniqueTempFileHandle(dir, name) {
  const base = sanitizePathPart(name || `download-${Date.now()}.part`);
  for (let index = 0; index < 10000; index += 1) {
    const suffix = index ? `.${index}` : "";
    const candidate = `${base}.${Date.now()}.${Math.random().toString(36).slice(2, 10)}${suffix}.tmp`;
    try {
      if (await fileExists(dir, candidate)) continue;
      return { name: candidate, handle: await dir.getFileHandle(candidate, { create: true }) };
    } catch (error) {
      if (error && error.name === "InvalidModificationError") continue;
      throw error;
    }
  }
  throw new Error("无法生成临时文件名");
}

function renderNameTemplate(template, item) {
  const uid = getItemAuthorUid(item) || "未知";
  const values = {
    title: item.title || `pid_${item.pid}`,
    author: item.author || "unknown_author",
    uid,
    authorId: uid,
    sourceUid: item.sourceUid || "",
    pid: item.pid,
    seconds: String(item.seconds || 0),
    segments: String(item.segments || 0),
    attachmentId: String(item.attachmentId || ""),
    publishedAt: item.publishedAt || "",
    publishedDate: item.publishedDate || "",
    publishedSort: item.publishedSort || "unknown-time",
  };
  let name = String(template || DEFAULT_NAME_TEMPLATE);
  for (let pass = 0; pass < 3; pass += 1) {
    const previous = name;
    for (const [key, value] of Object.entries(values)) {
      name = name.replaceAll(`{${key}}`, value);
    }
    if (name === previous) break;
  }
  return sanitizeFileBase(name, 180);
}

function getItemAuthorUid(item) {
  const value = item && (item.authorId || item.sourceUid || item.uid || "");
  return cleanTitle(value);
}

function sanitizeFileBase(value, maxLength) {
  const cleaned = cleanTitle(value)
    .replace(/[\\/:*?"<>|]+/g, "_")
    .replace(/[\u0000-\u001f]+/g, "")
    .replace(/\s+/g, " ")
    .replace(/_+/g, "_")
    .replace(/[. ]+$/g, "")
    .replace(/^_+|_+$/g, "");
  return (cleaned || "download").slice(0, maxLength || 180);
}

function sanitizePathPart(value) {
  return sanitizeFileBase(value, 80) || "unknown_author";
}

function ensureSafeExtension(name, ext) {
  const cleaned = sanitizeFileBase(name.replace(new RegExp(`${escapeRegExp(ext)}$`, "i"), ""), 180);
  return `${cleaned}${ext}`;
}

function cleanTitle(value) {
  return repairMojibake(String(value == null ? "" : value))
    .replace(/<[^>]*>/g, "")
    .replace(/&nbsp;/gi, " ")
    .replace(/\s+/g, " ")
    .trim();
}

function repairMojibake(value) {
  const text = String(value || "");
  const repaired = decodeCp1252Utf8Mojibake(text);
  if (!repaired || repaired === text) return text;
  return mojibakeScore(repaired) < mojibakeScore(text) ? repaired : text;
}

function decodeCp1252Utf8Mojibake(text) {
  const bytes = [];
  for (const ch of String(text || "")) {
    const code = ch.charCodeAt(0);
    if (code <= 0xff) {
      bytes.push(code);
    } else {
      const mapped = CP1252_REVERSE[code];
      if (mapped == null) return "";
      bytes.push(mapped);
    }
  }
  try {
    return new TextDecoder("utf-8", { fatal: true }).decode(new Uint8Array(bytes));
  } catch {
    return "";
  }
}

function mojibakeScore(text) {
  const value = String(text || "");
  const markers = (value.match(/[ÃÂâïð]|æ|ç|å|ã|è|é|ä/g) || []).length;
  const controls = (value.match(/[\u0080-\u009f]/g) || []).length;
  const cjk = (value.match(/[\u3400-\u9fff]/g) || []).length;
  return markers * 3 + controls * 5 - cjk * 2;
}

const CP1252_REVERSE = {
  0x20ac: 0x80,
  0x201a: 0x82,
  0x0192: 0x83,
  0x201e: 0x84,
  0x2026: 0x85,
  0x2020: 0x86,
  0x2021: 0x87,
  0x02c6: 0x88,
  0x2030: 0x89,
  0x0160: 0x8a,
  0x2039: 0x8b,
  0x0152: 0x8c,
  0x017d: 0x8e,
  0x2018: 0x91,
  0x2019: 0x92,
  0x201c: 0x93,
  0x201d: 0x94,
  0x2022: 0x95,
  0x2013: 0x96,
  0x2014: 0x97,
  0x02dc: 0x98,
  0x2122: 0x99,
  0x0161: 0x9a,
  0x203a: 0x9b,
  0x0153: 0x9c,
  0x017e: 0x9e,
  0x0178: 0x9f,
};

function normalizeIvHex(value) {
  const hex = String(value || "").replace(/^0x/i, "").replace(/[^a-f0-9]/gi, "").padStart(32, "0");
  return hex.slice(-32).toLowerCase();
}

function makeDefaultIvHex(sequence) {
  let value = BigInt(Math.max(0, Number(sequence || 0)));
  const bytes = new Uint8Array(16);
  for (let index = 15; index >= 0; index -= 1) {
    bytes[index] = Number(value & 0xffn);
    value >>= 8n;
  }
  return Array.from(bytes).map((byte) => byte.toString(16).padStart(2, "0")).join("");
}

function hexToBytes(hex) {
  const clean = normalizeIvHex(hex);
  const out = new Uint8Array(16);
  for (let index = 0; index < 16; index += 1) {
    out[index] = parseInt(clean.slice(index * 2, index * 2 + 2), 16);
  }
  return out;
}

function resolveMediaUrl(value, baseUrl) {
  try {
    return new URL(value, baseUrl).href;
  } catch {
    return "";
  }
}

function splitJoinedUrls(text) {
  return String(text || "")
    .replace(/(?=https?:\/\/)/gi, "\n")
    .replace(/(?=\bwww\.[a-z0-9.-]+\b)/gi, "\n");
}

function extractSiteOriginsFromText(text) {
  const origins = [];
  const seen = new Set();
  const source = splitJoinedUrls(text);
  for (const token of source.split(/[\s,;\uFF0C\uFF1B]+/)) {
    const candidate = normalizeLooseOriginToken(token);
    if (!candidate || seen.has(candidate)) continue;
    seen.add(candidate);
    origins.push(candidate);
  }
  return origins;
}

function normalizeLooseOriginToken(token) {
  const text = String(token || "").trim();
  if (!text) return "";
  const match = text.match(/^(?:https?:\/\/)?[a-z0-9.-]+(?::\d+)?/i);
  if (!match) return "";
  return normalizeSiteOrigin(match[0]);
}

function parseBatchInput(text) {
  const out = [];
  const seenPids = new Set();
  const seenSells = new Set();

  const makePostUrl = (pid, origin) => `${origin || getSiteOrigin()}/post/details?pid=${encodeURIComponent(pid)}`;
  const makeSellUrl = (uid, origin) => `${origin || getSiteOrigin()}/homepage/sell/${encodeURIComponent(uid)}`;

  const addPid = (pid, sourceOrigin = "") => {
    pid = String(pid || "").trim();
    if (!/^\d{4,}$/.test(pid) || seenPids.has(pid)) return;
    const origin = normalizeSiteOrigin(sourceOrigin) || getSiteOrigin();
    seenPids.add(pid);
    out.push({
      type: "post",
      pid,
      url: makePostUrl(pid, origin),
      sourceOrigin: origin,
    });
  };

  const addSell = (uid, sourceOrigin = "") => {
    uid = String(uid || "").trim();
    if (!/^\d{4,}$/.test(uid) || seenSells.has(uid)) return;
    const origin = normalizeSiteOrigin(sourceOrigin) || getSiteOrigin();
    seenSells.add(uid);
    out.push({
      type: "sell",
      uid,
      url: makeSellUrl(uid, origin),
      sourceOrigin: origin,
    });
  };

  const source = splitJoinedUrls(text);
  const matches = [];

  for (const match of source.matchAll(/((?:https?:\/\/)?[^/\s,;\uFF0C\uFF1B?#]+)?\/post\/details\?[^ \t\r\n,;\uFF0C\uFF1B#]*?[?&]?pid=(\d{4,})/gi)) {
    matches.push({ index: match.index || 0, type: "post", id: match[2], sourceOrigin: getOriginFromText(match[1] || "") });
  }
  for (const match of source.matchAll(/[?&]pid=(\d{4,})/gi)) {
    matches.push({ index: match.index || 0, type: "post", id: match[1], sourceOrigin: "" });
  }
  for (const match of source.matchAll(/((?:https?:\/\/)?[^/\s,;\uFF0C\uFF1B?#]+)?\/homepage\/(?:sell\/)?(\d{4,})(?=$|[/?#\s,;\uFF0C\uFF1B]|https?:\/\/)/gi)) {
    matches.push({ index: match.index || 0, type: "sell", id: match[2], sourceOrigin: getOriginFromText(match[1] || "") });
  }

  matches.sort((a, b) => a.index - b.index);
  for (const match of matches) {
    if (match.type === "sell") addSell(match.id, match.sourceOrigin);
    else addPid(match.id, match.sourceOrigin);
  }

  for (const match of source.matchAll(/(?:^|[\s,;\uFF0C\uFF1B])(\d{4,})(?=$|[\s,;\uFF0C\uFF1B])/g)) {
    if (isNumberInsideKnownUrl(source, match.index || 0, match[0])) continue;
    addPid(match[1]);
  }

  if (!out.length) {
    for (const rawLine of source.split(/\r?\n/)) {
      const line = rawLine.trim();
      if (!line) continue;
      const sellUid = extractSellUid(line);
      if (sellUid) addSell(sellUid, getOriginFromText(line));
      else addPid(extractPid(line), getOriginFromText(line));
    }
  }
  return out;
}

function isNumberInsideKnownUrl(source, matchIndex, matchText) {
  const numberIndex = matchIndex + String(matchText || "").search(/\d/);
  if (numberIndex < 0) return false;
  const before = String(source || "").slice(Math.max(0, numberIndex - 80), numberIndex).toLowerCase();
  return /\/(?:homepage\/(?:sell\/)?|post\/details\?[^\s,;\uFF0C\uFF1B]*pid=)$/.test(before);
}

function extractSellUid(value) {
  const text = String(value || "").trim();
  try {
    const url = new URL(text);
    const match = url.pathname.match(/^\/homepage\/(?:sell\/)?(\d{4,})/i);
    return match ? match[1] : "";
  } catch {
    const match = text.match(/\/homepage\/(?:sell\/)?(\d{4,})/i);
    return match ? match[1] : "";
  }
}

function extractPid(value) {
  const text = String(value || "").trim();
  if (/^\d+$/.test(text)) return text;
  try {
    const url = new URL(text);
    const pid = url.searchParams.get("pid") || "";
    return /^\d+$/.test(pid) ? pid : "";
  } catch {
    const match = text.match(/[?&]pid=(\d+)/i) || text.match(/\b(\d{4,})\b/);
    return match ? match[1] : "";
  }
}

function formatBatchInput(id) {
  const input = $(id);
  const entries = parseBatchInput(input.value);
  if (!entries.length) {
    const adopted = adoptSiteOriginFromBatchText(input.value);
    if (adopted) {
      syncFloatingFromMain();
      updateSiteOriginState("已从粘贴内容识别当前域名。");
      saveSettings();
    }
    return false;
  }
  adoptSiteOriginFromEntries(entries);

  const formatted = entries.map((entry) => entry.url).join("\n");
  if (formatted === input.value.trim()) return false;

  input.value = formatted;
  input.selectionStart = input.value.length;
  input.selectionEnd = input.value.length;
  return true;
}

function adoptSiteOriginFromEntries(entries) {
  const origin = (entries || []).map((entry) => entry && entry.sourceOrigin).find(Boolean);
  if (!origin || origin === getSiteOrigin()) return;
  setSiteOrigin(origin, { save: false });
  return origin;
}

function adoptSiteOriginFromBatchInput() {
  const input = $("batch-input");
  if (!input) return "";
  return adoptSiteOriginFromBatchText(input.value);
}

function adoptSiteOriginFromBatchText(text) {
  const entries = parseBatchInput(text);
  const fromEntry = adoptSiteOriginFromEntries(entries);
  if (fromEntry) return fromEntry;
  const origin = extractSiteOriginsFromText(text)[0] || "";
  if (!origin || origin === getSiteOrigin()) return "";
  setSiteOrigin(origin, { save: false });
  detectedSiteOrigins = Array.from(new Set([origin, ...detectedSiteOrigins]));
  return origin;
}

function syncFloatingFromMain() {
  for (const [mainId, floatId, property] of FLOAT_SYNC_FIELDS) {
    const main = $(mainId);
    const float = $(floatId);
    if (!main || !float || float[property] === main[property]) continue;
    float[property] = main[property];
  }
}

function syncMainFromFloating() {
  for (const [mainId, floatId, property] of FLOAT_SYNC_FIELDS) {
    const main = $(mainId);
    const float = $(floatId);
    if (!main || !float || main[property] === float[property]) continue;
    main[property] = float[property];
  }
}

function readOptions() {
  return {
    siteOrigin: getSiteOrigin(),
    nameTemplate: $("name-template").value || DEFAULT_NAME_TEMPLATE,
    conflictMode: $("conflict-mode").value || "skip",
    delaySeconds: readNumber("delay-seconds", 2),
    segmentTimeoutSeconds: readNumber("segment-timeout", 30),
    segmentConcurrency: readNumber("segment-concurrency", DEFAULT_SEGMENT_CONCURRENCY),
    taskConcurrency: readNumber("task-concurrency", DEFAULT_TASK_CONCURRENCY),
    globalMediaConcurrency: readNumber("global-media-concurrency", DEFAULT_GLOBAL_MEDIA_CONCURRENCY),
    adaptiveConcurrency: $("adaptive-concurrency").checked,
    loginAssist: $("login-assist").checked,
    byAuthor: $("by-author").checked,
    saveManifest: $("save-manifest").checked,
    fallbackPreview: $("fallback-preview").checked,
    sellVideoOnly: $("sell-video-only").checked,
    autoDownloadAfterParse: $("auto-download-after-parse").checked,
  };
}

function readNumber(id, fallback) {
  const value = Number($(id).value);
  return Number.isFinite(value) && value >= 0 ? value : fallback;
}

function saveSettings() {
  if (saveSettingsTimer) window.clearTimeout(saveSettingsTimer);
  saveSettingsTimer = window.setTimeout(() => {
    saveSettingsTimer = null;
    writeSettingsNow();
  }, 150);
}

function writeSettingsNow() {
  const settings = {
    siteOrigin: getSiteOrigin(),
    originImport: $("origin-import").value,
    batchInput: $("batch-input").value,
    nameTemplate: $("name-template").value,
    conflictMode: $("conflict-mode").value,
    delaySeconds: $("delay-seconds").value,
    segmentTimeout: $("segment-timeout").value,
    segmentConcurrency: $("segment-concurrency").value,
    taskConcurrency: $("task-concurrency").value,
    globalMediaConcurrency: $("global-media-concurrency").value,
    adaptiveConcurrency: $("adaptive-concurrency").checked,
    loginAssist: $("login-assist").checked,
    byAuthor: $("by-author").checked,
    saveManifest: $("save-manifest").checked,
    fallbackPreview: $("fallback-preview").checked,
    sellVideoOnly: $("sell-video-only").checked,
    autoDownloadAfterParse: $("auto-download-after-parse").checked,
    hideParsedInputSources,
  };
  try {
    const previous = localStorage.getItem(SETTINGS_KEY);
    if (previous) localStorage.setItem(SETTINGS_BACKUP_KEY, previous);
    localStorage.setItem(SETTINGS_KEY, JSON.stringify(settings));
  } catch (error) {
    setSummary(`保存设置失败：${String(error && error.message || error)}`);
  }
}

function restoreSettings() {
  try {
    const settings = loadStoredSettings();
    if (settings.siteOrigin != null) $("site-origin").value = normalizeSiteOrigin(settings.siteOrigin) || DEFAULT_SITE_ORIGIN;
    if (settings.originImport != null) $("origin-import").value = settings.originImport;
    if (settings.batchInput != null) $("batch-input").value = settings.batchInput;
    formatBatchInput("batch-input");
    if (settings.nameTemplate != null) $("name-template").value = migrateNameTemplate(settings.nameTemplate);
    if (settings.conflictMode != null) $("conflict-mode").value = settings.conflictMode;
    if (settings.delaySeconds != null) $("delay-seconds").value = settings.delaySeconds;
    if (settings.segmentTimeout != null) $("segment-timeout").value = settings.segmentTimeout;
    if (settings.segmentConcurrency != null) $("segment-concurrency").value = settings.segmentConcurrency;
    if (settings.taskConcurrency != null) $("task-concurrency").value = settings.taskConcurrency;
    if (settings.globalMediaConcurrency != null) $("global-media-concurrency").value = settings.globalMediaConcurrency;
    if (settings.adaptiveConcurrency != null) $("adaptive-concurrency").checked = Boolean(settings.adaptiveConcurrency);
    if (settings.loginAssist != null) $("login-assist").checked = Boolean(settings.loginAssist);
    if (settings.byAuthor != null) $("by-author").checked = Boolean(settings.byAuthor);
    if (settings.saveManifest != null) $("save-manifest").checked = Boolean(settings.saveManifest);
    if (settings.fallbackPreview != null) $("fallback-preview").checked = Boolean(settings.fallbackPreview);
    if (settings.sellVideoOnly != null) $("sell-video-only").checked = Boolean(settings.sellVideoOnly);
    if (settings.autoDownloadAfterParse != null) $("auto-download-after-parse").checked = Boolean(settings.autoDownloadAfterParse);
    if (settings.hideParsedInputSources != null) hideParsedInputSources = Boolean(settings.hideParsedInputSources);
    updateParsedSourcesToggle();
  } catch (error) {
    setSummary(`设置已损坏，已使用默认值：${String(error && error.message || error)}`);
  }
  $("name-template").value = migrateNameTemplate($("name-template").value);
}

function loadStoredSettings() {
  const primary = localStorage.getItem(SETTINGS_KEY) || "{}";
  try {
    return JSON.parse(primary);
  } catch (error) {
    const backup = localStorage.getItem(SETTINGS_BACKUP_KEY) || "{}";
    try {
      return JSON.parse(backup);
    } catch {
      throw error;
    }
  }
}

function migrateNameTemplate(template) {
  const text = String(template || "").trim();
  if (!text) return DEFAULT_NAME_TEMPLATE;
  if (text === LEGACY_DEFAULT_NAME_TEMPLATE || text === "{title} - {author} - {pid}" || text === "{title} - {author} - {pid} - {seconds}s") {
    return DEFAULT_NAME_TEMPLATE;
  }
  return text;
}

function scheduleRender() {
  saveResultViewState();
  if (renderQueued) return;
  renderQueued = true;
  requestAnimationFrame(() => {
    renderQueued = false;
    const forceFullRender = forceNextResultRender;
    forceNextResultRender = false;
    if (!forceFullRender && shouldDeferFullResultRender()) {
      renderDownloadProgressOnly();
      queueDeferredResultRender();
      return;
    }
    cancelDeferredResultRender();
    renderResults();
  });
}

function shouldDeferFullResultRender() {
  if (!activeReport || !["downloading", "parsing"].includes(activeReport.stage)) return false;
  const container = $("results");
  if (!container) return false;
  const active = document.activeElement;
  if (active && container.contains(active) && active.matches("select, input, textarea, button, summary")) return true;
  if (container.querySelector(".author-filter[open]")) return true;
  return activeReport.stage === "parsing" && activeReport.items && activeReport.items.length > 30;
}

function queueDeferredResultRender() {
  if (deferredResultRenderTimer) return;
  deferredResultRenderTimer = window.setTimeout(() => {
    deferredResultRenderTimer = null;
    if (shouldDeferFullResultRender()) {
      renderDownloadProgressOnly();
      queueDeferredResultRender();
      return;
    }
    renderResults();
  }, 700);
}

function cancelDeferredResultRender() {
  if (!deferredResultRenderTimer) return;
  window.clearTimeout(deferredResultRenderTimer);
  deferredResultRenderTimer = null;
}

function setSummary(text) {
  $("summary").textContent = text;
  updateFloatingConsole(text);
}

function busyModeLabel(mode) {
  return ({
    parsing: "解析中",
    downloading: "下载中",
    estimating: "估算中",
    backfilling: "补全中",
    ignoring: "忽略中",
  })[mode] || "运行中";
}

function exportReport() {
  if (!activeReport) return;
  const stamp = new Date().toISOString().replace(/[:.]/g, "-");
  const blob = new Blob([JSON.stringify(makeExportReport(activeReport), null, 2)], { type: "application/json" });
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.href = url;
  link.download = `hj-downloader-preview-${stamp}.json`;
  document.body.appendChild(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 60000);
}

function makeExportReport(report) {
  const cloned = JSON.parse(JSON.stringify(report || {}));
  cloned.exportedAt = new Date().toISOString();
  cloned.exportRedacted = true;
  cloned.redactionNote = "Temporary media, segment, and key URLs are redacted in exported reports.";
  return redactReportValue(cloned, "");
}

function redactReportValue(value, key) {
  if (Array.isArray(value)) return value.map((item) => redactReportValue(item, key));
  if (value && typeof value === "object") {
    const result = {};
    for (const [childKey, childValue] of Object.entries(value)) {
      result[childKey] = redactReportValue(childValue, childKey);
    }
    return result;
  }
  if (typeof value !== "string") return value;
  return redactReportString(value, key);
}

function redactReportString(value, key) {
  const lowerKey = String(key || "").toLowerCase();
  if (lowerKey === "keyline") return `[redacted-key-line:${shortHash(value)}]`;
  if (lowerKey === "manifesttext" || (lowerKey === "text" && /#EXTM3U/.test(value))) {
    const lineCount = value.split(/\r?\n/).length;
    return `[redacted-manifest:${lineCount} lines:${shortHash(value)}]`;
  }
  if (/manifesturl$|keyurl$|segmenturl$|remoteurl$/.test(lowerKey) && isMediaLikeUrl(value)) {
    return redactMediaUrl(value);
  }
  return value
    .replace(/#EXT-X-KEY:[^\r\n]*/gi, (match) => `[redacted-key-line:${shortHash(match)}]`)
    .replace(/https?:\/\/[^\s"'<>]+?\.(?:m3u8|ts|key)(?:[^\s"'<>]*)/gi, (match) => redactMediaUrl(match));
}

function isMediaLikeUrl(value) {
  return /^https?:\/\//i.test(String(value || "")) && /\.(?:m3u8|ts|key)(?:[?#]|$)/i.test(String(value || ""));
}

function redactMediaUrl(value) {
  const text = String(value || "");
  try {
    const url = new URL(text);
    const tail = url.pathname.split("/").filter(Boolean).pop() || "media";
    return `[redacted-media-url:${url.hostname}/${tail}:${shortHash(text)}]`;
  } catch {
    return `[redacted-media-url:${shortHash(text)}]`;
  }
}

function shortHash(value) {
  let hash = 2166136261;
  const text = String(value || "");
  for (let index = 0; index < text.length; index += 1) {
    hash ^= text.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return (hash >>> 0).toString(16).padStart(8, "0");
}

async function parseResources(config = {}) {
  if (isBusy()) return;
  formatBatchInput("batch-input");
  syncFloatingFromMain();

  const inputText = $("batch-input").value.trim();
  const rawEntries = parseBatchInput(inputText);
  if (!rawEntries.length) {
    setSummary(activeReport ? "没有新的来源需要解析。" : "没有可用链接。");
    return;
  }

  let options = null;
  let sourceHistory = {};
  try {
    await prepareOriginsForEntries(rawEntries);
    options = readOptions();
    if (activeReport && !Array.isArray(activeReport.sources)) {
      activeReport.sources = inferSourceRecords(activeReport);
    }
    if (!(await ensureRootForParsing())) return;
    sourceHistory = await loadSourceHistoryForEntries(rawEntries);
  } catch (error) {
    setSummary(`解析失败：${String(error && error.message || error)}`);
    if (activeReport) {
      activeReport.stage = "failed";
      activeReport.error = String(error && error.message || error);
      scheduleRender();
    }
    return;
  }

  beginStoppableRun();
  running = true;
  beginBusy("parsing");
  ensureActiveReport(inputText, options);
  updateFloatingButtons();
  setSummary("正在读取本地历史并准备解析...");
  scheduleRender();

  let wasStopped = false;
  try {
    activeReport.stage = "parsing";
    activeReport.inputText = mergeSourceInputText(inputText);
    activeReport.options = {
      ...activeReport.options,
      ...options,
    };
    activeReport.parseStartedAt = activeReport.parseStartedAt || new Date().toISOString();

    const restoredCount = restoreHistoryItemsForEntries(rawEntries, sourceHistory, options);
    if (restoredCount) {
      refreshItemIndexes();
      activeReport.total = activeReport.items.length;
      setSummary(`已从本地历史恢复 ${restoredCount} 条资源，继续联网检查新增。`);
      scheduleRender();
    }
    if (activeReport.items.length) {
      const localSync = await syncLocalDownloadMatchesForItems(activeReport.items, options);
      if (localSync.matched || localSync.missing) {
        setSummary(`已核对本地文件：匹配已下载 ${localSync.matched} 条，未匹配 ${localSync.missing} 条。`);
        scheduleRender();
      }
    }

    const existingSourceKeys = getParsedSourceKeys();
    const parseEntries = rawEntries.filter((entry) => shouldParseEntry(entry, existingSourceKeys, sourceHistory));
    if (!parseEntries.length) {
      upsertSourceRecords(makeHistorySourceRecords(rawEntries, sourceHistory));
      activeReport.stage = stopRequested ? "stopped" : "parsed";
      activeReport.parseFinishedAt = new Date().toISOString();
      activeReport.total = activeReport.items.length;
      activeReport.inputText = mergeSourceInputText($("batch-input").value.trim());
      if (!isBusy()) applyParsedSourcesVisibility();
      setSummary(activeReport.items.length ? makeParseSummary(activeReport) : "这些来源已经解析过，本地没有可恢复的资源。");
      scheduleRender();
      return;
    }

    setSummary(`正在追加/刷新解析 ${parseEntries.length} 个来源...`);
    scheduleRender();

    const existingPids = new Set(activeReport.items.map((item) => String(item.pid)));
    const expanded = await expandBatchEntries(parseEntries, options, existingPids, sourceHistory);
    const entries = expanded.entries;
    const previousLength = activeReport.items.length;
    const newItems = entries.map((entry, offset) => makePlanItem(entry, previousLength + offset));

    activeReport.items.push(...newItems);
    activeReport.imports.push(...expanded.importSources);
    upsertSourceRecords(makeSourceRecords(parseEntries, expanded, newItems));
    await updateSourceHistoryFromScans(sourceHistory, expanded.importSources);
    refreshItemIndexes();
    activeReport.total = activeReport.items.length;
    scheduleRender();

    if (!newItems.length) {
      activeReport.stage = stopRequested ? "stopped" : "parsed";
      activeReport.parseFinishedAt = new Date().toISOString();
      if (!isBusy()) applyParsedSourcesVisibility();
      setSummary(activeReport.items.length ? makeParseSummary(activeReport) : "新来源没有新增可下载资源，可能全部重复或被过滤。");
      return;
    }

    await analyzePlanItems(newItems, options);

    activeReport.stage = stopRequested ? "stopped" : "parsed";
    activeReport.parseFinishedAt = new Date().toISOString();
    activeReport.inputText = mergeSourceInputText($("batch-input").value.trim());
    if (!isBusy()) applyParsedSourcesVisibility();
    setSummary(makeParseSummary(activeReport));
  } catch (error) {
    setSummary(`解析失败：${String(error && error.message || error)}`);
    if (activeReport) {
      activeReport.stage = "failed";
      activeReport.error = String(error && error.message || error);
    }
  } finally {
    wasStopped = stopRequested;
    await closeHelperTab();
    clearStoppableRun();
    running = false;
    endBusy("parsing");
    updateFloatingButtons();
    scheduleRender();
    if (wasStopped) stopRequested = false;
  }

  if (!wasStopped && config.respectAuto && readOptions().autoDownloadAfterParse) {
    await downloadParsedSelection(readOptions());
  }
}

async function downloadOrParse() {
  if (isBusy()) return;
  if (stopRequested && !activeStopController) stopRequested = false;
  if (!activeReport || hasUnparsedInputSources()) {
    await parseResources({ respectAuto: false });
  }
  if (!running && activeReport && !hasUnparsedInputSources() && !stopRequested) {
    await downloadParsedSelection(readOptions());
  }
}

function hasUnparsedInputSources() {
  const entries = parseBatchInput($("batch-input").value);
  if (!entries.length) return false;
  if (activeReport && !Array.isArray(activeReport.sources)) {
    activeReport.sources = inferSourceRecords(activeReport);
  }
  const parsed = getParsedSourceKeys();
  return entries.some((entry) => !parsed.has(getEntrySourceKey(entry)));
}

function ensureActiveReport(inputText, options) {
  if (activeReport && Array.isArray(activeReport.items)) {
    activeReport.sources = Array.isArray(activeReport.sources) ? activeReport.sources : inferSourceRecords(activeReport);
    activeReport.imports = Array.isArray(activeReport.imports) ? activeReport.imports : [];
    activeReport.options = {
      ...activeReport.options,
      ...options,
    };
    activeReport.inputText = mergeSourceInputText(inputText);
    return;
  }

  resetResultViewState();
  activeReport = {
    kind: "hj_downloader_preview",
    version: chrome.runtime.getManifest().version,
    stage: "parsing",
    inputText,
    startedAt: new Date().toISOString(),
    parseStartedAt: "",
    parseFinishedAt: "",
    downloadStartedAt: "",
    finishedAt: "",
    options: { ...options },
    imports: [],
    sources: [],
    total: 0,
    items: [],
  };
}

function getEntrySourceKey(entry) {
  if (!entry) return "";
  if (entry.type === "sell") return `sell:${String(entry.uid || "").trim()}`;
  return `post:${String(entry.pid || "").trim()}`;
}

function shouldParseEntry(entry, existingSourceKeys, sourceHistory) {
  const key = getEntrySourceKey(entry);
  if (!key) return false;
  if (entry.type === "sell") return true;
  return !existingSourceKeys.has(key) && !sourceHistory[key];
}

function getParsedSourceKeys() {
  if (!activeReport || !Array.isArray(activeReport.sources)) return new Set();
  return new Set(activeReport.sources.map((source) => source && source.key).filter(Boolean));
}

function getSourceHistoryRecord(entry, sourceHistory) {
  const key = getEntrySourceKey(entry);
  return key && sourceHistory ? sourceHistory[key] || null : null;
}

function getKnownTopicIdsForEntry(entry, sourceHistory) {
  const key = getEntrySourceKey(entry);
  const ids = new Set();
  const history = getSourceHistoryRecord(entry, sourceHistory);
  if (hasCompleteSellTopicHistory(history)) {
    for (const id of history && history.knownTopicIds || []) {
      if (id) ids.add(String(id));
    }
  }
  for (const item of activeReport && activeReport.items || []) {
    const itemKey = item.sourceKey || (item.sourceType === "sell" ? `sell:${item.sourceUid}` : `post:${item.pid}`);
    if (itemKey === key && item.pid) ids.add(String(item.pid));
  }
  return ids;
}

function hasCompleteSellTopicHistory(history) {
  const record = normalizeSellHistoryRecord(history, history && history.uid || "");
  const topicCount = Object.keys(record.topics || {}).length;
  const knownCount = (record.knownTopicIds || []).length;
  const expected = Math.max(Number(record.lastTotal || 0), knownCount);
  return expected > 0 && topicCount >= expected;
}

function restoreUndownloadedHistoryPosts(entry, historyRecord, addPost, scan, options) {
  const record = normalizeSellHistoryRecord(historyRecord, entry && entry.uid || "");
  const topics = record.topics || {};
  let restored = 0;
  for (const [pid, topic] of Object.entries(topics)) {
    if (!/^\d{4,}$/.test(String(pid))) continue;
    if (options && options.sellVideoOnly && topic && topic.hasVideo === false) continue;
    if (isHistoryTopicDownloaded(topic)) continue;
    const added = addPost({ pid }, {
      type: "sell",
      uid: record.uid || entry.uid,
      url: entry.url || record.url,
      sourceOrigin: entry.sourceOrigin || record.sourceOrigin || "",
      key: getEntrySourceKey(entry),
      title: record.userName || "",
    });
    if (added) restored += 1;
  }
  if (scan) scan.restoredFromHistory = Number(scan.restoredFromHistory || 0) + restored;
  return restored;
}

function isHistoryTopicDownloaded(topic) {
  return Boolean(topic && (topic.downloadedAt || topic.downloadStatus === "downloaded" || topic.outputFile));
}

function makeSourceRecords(rawEntries, expanded, newItems) {
  const itemCountBySource = new Map();
  for (const item of newItems || []) {
    const key = item.sourceKey || "";
    if (!key) continue;
    itemCountBySource.set(key, (itemCountBySource.get(key) || 0) + 1);
  }

  const importByKey = new Map();
  for (const item of expanded && expanded.importSources || []) {
    importByKey.set(`sell:${String(item.uid || "").trim()}`, item);
  }

  return rawEntries.map((entry) => {
    const key = getEntrySourceKey(entry);
    const scan = importByKey.get(key) || null;
    return {
      key,
      type: entry.type || "post",
      uid: entry.uid || "",
      pid: entry.pid || "",
      url: entry.url,
      sourceOrigin: entry.sourceOrigin || "",
      status: "parsed",
      parsedAt: new Date().toISOString(),
      itemCount: itemCountBySource.get(key) || 0,
      scanSummary: scan ? {
        total: scan.total,
        included: scan.included,
        excludedNoVideo: scan.excludedNoVideo,
        duplicate: scan.duplicate,
        restoredFromHistory: scan.restoredFromHistory,
        knownBefore: scan.knownBefore,
        knownMatched: scan.knownMatched,
        scannedPages: scan.scannedPages,
        pageCount: scan.pageCount,
      } : null,
    };
  });
}

function makeHistorySourceRecords(rawEntries, sourceHistory) {
  const itemCountBySource = new Map();
  for (const item of activeReport && activeReport.items || []) {
    const key = item.sourceKey || (item.sourceType === "sell" ? `sell:${item.sourceUid}` : `post:${item.pid}`);
    if (!key) continue;
    itemCountBySource.set(key, (itemCountBySource.get(key) || 0) + 1);
  }

  return (rawEntries || []).map((entry) => {
    const key = getEntrySourceKey(entry);
    const history = getSourceHistoryRecord(entry, sourceHistory);
    const sellRecord = entry && entry.type === "sell" ? normalizeSellHistoryRecord(history, entry.uid) : null;
    const knownTopicCount = sellRecord ? (sellRecord.knownTopicIds || []).length : 0;
    const parsedTopicCount = sellRecord ? Object.keys(sellRecord.topics || {}).length : 0;
    return {
      key,
      type: entry.type || "post",
      uid: entry.uid || "",
      pid: entry.pid || "",
      url: entry.url,
      sourceOrigin: entry.sourceOrigin || history && history.sourceOrigin || "",
      status: "parsed",
      parsedAt: sellRecord && sellRecord.lastScannedAt || new Date().toISOString(),
      itemCount: itemCountBySource.get(key) || parsedTopicCount || 0,
      restoredFromHistory: true,
      scanSummary: sellRecord ? {
        total: sellRecord.lastTotal || knownTopicCount,
        included: parsedTopicCount,
        excludedNoVideo: 0,
        duplicate: knownTopicCount,
        restoredFromHistory: itemCountBySource.get(key) || 0,
        knownBefore: knownTopicCount,
        knownMatched: knownTopicCount,
        scannedPages: 0,
        pageCount: sellRecord.lastPageCount || 0,
      } : null,
    };
  }).filter((record) => record.key);
}

function upsertSourceRecords(records) {
  if (!activeReport) return;
  activeReport.sources = Array.isArray(activeReport.sources) ? activeReport.sources : [];
  const byKey = new Map(activeReport.sources.map((source, index) => [source.key, { source, index }]));
  for (const record of records || []) {
    if (!record || !record.key) continue;
    const existing = byKey.get(record.key);
    if (existing) {
      const itemCount = record.restoredFromHistory
        ? Math.max(Number(existing.source.itemCount || 0), Number(record.itemCount || 0))
        : Number(existing.source.itemCount || 0) + Number(record.itemCount || 0);
      activeReport.sources[existing.index] = {
        ...existing.source,
        ...record,
        itemCount,
        refreshedAt: record.parsedAt,
      };
    } else {
      activeReport.sources.push(record);
      byKey.set(record.key, { source: record, index: activeReport.sources.length - 1 });
    }
  }
}

function loadSourceHistory() {
  try {
    const parsed = JSON.parse(localStorage.getItem(SOURCE_HISTORY_KEY) || "{}");
    return parsed && typeof parsed === "object" ? parsed : {};
  } catch {
    return {};
  }
}

function saveSourceHistory(history) {
  try {
    localStorage.setItem(SOURCE_HISTORY_KEY, JSON.stringify(compactSourceHistory(history || {})));
  } catch {
    // Ignore quota or storage errors; the current in-memory report still works.
  }
}

function compactSourceHistory(history) {
  const compact = {};
  for (const [key, value] of Object.entries(history || {})) {
    if (!value || typeof value !== "object") continue;
    if (!key.startsWith("sell:") && value.type !== "sell") {
      compact[key] = value;
      continue;
    }
    const record = normalizeSellHistoryRecord(value, value.uid || (key.startsWith("sell:") ? key.slice(5) : ""));
    compact[key] = {
      key: record.key || key,
      type: record.type || "sell",
      uid: record.uid || "",
      url: record.url || "",
      sourceOrigin: record.sourceOrigin || "",
      userName: record.userName || "",
      lastScannedAt: record.lastScannedAt || "",
      lastTotal: Number(record.lastTotal || 0),
      lastLimit: Number(record.lastLimit || 0),
      lastPageCount: Number(record.lastPageCount || 0),
      knownTopicIds: record.knownTopicIds || [],
    };
  }
  return compact;
}

async function loadSourceHistoryForEntries(entries) {
  const history = loadSourceHistory();
  let changed = false;
  const uids = new Set();
  for (const entry of entries || []) {
    if (entry && entry.type === "sell" && isHistoryUid(entry.uid)) uids.add(String(entry.uid));
  }

  for (const uid of uids) {
    const localRecord = await readSellHistoryFile(uid);
    if (!localRecord) continue;
    const key = `sell:${uid}`;
    history[key] = mergeSellHistoryRecords(history[key], localRecord, uid);
    changed = true;
  }

  if (changed) saveSourceHistory(history);
  return history;
}

async function updateSourceHistoryFromScans(history, scans) {
  let changed = false;
  for (const scan of scans || []) {
    if (!scan || scan.type !== "sell" || !scan.uid) continue;
    const key = `sell:${String(scan.uid)}`;
    const updated = await mutateSellHistory(scan.uid, (record) => {
      const previous = mergeSellHistoryRecords(history[key], record, scan.uid);
      return buildSellHistoryRecordFromScan(previous, scan);
    }).catch((error) => {
      scan.historyError = String(error && error.message || error);
      return null;
    });
    if (updated) {
      history[key] = updated;
      changed = true;
    }
  }
  if (changed) {
    saveSourceHistory(history);
  }
}

function buildSellHistoryRecordFromScan(previous, scan) {
  const now = new Date().toISOString();
  const uid = String(scan && scan.uid || previous && previous.uid || "");
  const base = normalizeSellHistoryRecord(previous, uid);
  const known = new Set((base.knownTopicIds || []).map((id) => String(id)));
  const topics = { ...(base.topics || {}) };

  for (const id of scan.discoveredTopicIds || []) {
    if (id) known.add(String(id));
  }

  for (const topic of scan.topics || []) {
    const topicId = String(topic && topic.topicId || "").trim();
    if (!topicId) continue;
    const existing = topics[topicId] || {};
    known.add(topicId);
    topics[topicId] = {
      pid: topicId,
      title: cleanTitle(topic.title || existing.title || ""),
      publishedAtRaw: topic.publishedAtRaw || existing.publishedAtRaw || "",
      publishedAt: topic.publishedAt || existing.publishedAt || "",
      publishedDate: topic.publishedDate || existing.publishedDate || "",
      publishedSort: topic.publishedSort || existing.publishedSort || "",
      hasVideo: topic.hasVideo == null ? Boolean(existing.hasVideo) : Boolean(topic.hasVideo),
      hasPic: topic.hasPic == null ? Boolean(existing.hasPic) : Boolean(topic.hasPic),
      hasAudio: topic.hasAudio == null ? Boolean(existing.hasAudio) : Boolean(topic.hasAudio),
      attachmentCount: Number(topic.attachmentCount || existing.attachmentCount || 0),
      firstSeenAt: existing.firstSeenAt || now,
      lastSeenAt: now,
      lastDecision: topic.decision || existing.lastDecision || "",
    };
  }

  for (const id of Object.keys(topics)) {
    if (id) known.add(String(id));
  }

  return {
    ...base,
    version: SELL_HISTORY_VERSION,
    key: `sell:${uid}`,
    type: "sell",
    uid,
    url: scan.url || base.url || `${normalizeSiteOrigin(scan.sourceOrigin || base.sourceOrigin || "") || getSiteOrigin()}/homepage/sell/${encodeURIComponent(uid)}`,
    sourceOrigin: normalizeSiteOrigin(scan.sourceOrigin || base.sourceOrigin || "") || "",
    userName: getSellUserName(scan.user) || base.userName || "",
    lastScannedAt: now,
    lastTotal: Number(scan.total || base.lastTotal || 0),
    lastLimit: Number(scan.limit || base.lastLimit || 0),
    lastPageCount: Number(scan.pageCount || base.lastPageCount || 0),
    knownTopicIds: Array.from(known),
    topics,
  };
}

function mergeSellHistoryRecords(primary, secondary, fallbackUid) {
  const first = normalizeSellHistoryRecord(primary, fallbackUid);
  const second = normalizeSellHistoryRecord(secondary, fallbackUid);
  const uid = String(second.uid || first.uid || fallbackUid || "");
  const known = new Set();
  for (const id of first.knownTopicIds || []) if (id) known.add(String(id));
  for (const id of second.knownTopicIds || []) if (id) known.add(String(id));
  const topics = { ...(first.topics || {}) };
  for (const [pid, topic] of Object.entries(second.topics || {})) {
    topics[pid] = { ...(topics[pid] || {}), ...(topic || {}) };
    if (pid) known.add(String(pid));
  }
  for (const id of Object.keys(topics)) if (id) known.add(String(id));

  return {
    ...first,
    ...second,
    version: SELL_HISTORY_VERSION,
    key: `sell:${uid}`,
    type: "sell",
    uid,
    url: second.url || first.url || (uid ? `${normalizeSiteOrigin(second.sourceOrigin || first.sourceOrigin || "") || getSiteOrigin()}/homepage/sell/${encodeURIComponent(uid)}` : ""),
    sourceOrigin: normalizeSiteOrigin(second.sourceOrigin || first.sourceOrigin || "") || "",
    lastScannedAt: latestIso(first.lastScannedAt, second.lastScannedAt),
    lastTotal: Number(second.lastTotal || first.lastTotal || 0),
    lastLimit: Number(second.lastLimit || first.lastLimit || 0),
    lastPageCount: Number(second.lastPageCount || first.lastPageCount || 0),
    knownTopicIds: Array.from(known),
    topics,
  };
}

function normalizeSellHistoryRecord(record, fallbackUid) {
  if (!record || typeof record !== "object") return {};
  const version = Number(record.version || SELL_HISTORY_VERSION);
  if (version < SELL_HISTORY_MIN_SUPPORTED_VERSION) {
    record = migrateLegacySellHistoryRecord(record, fallbackUid, version);
  }
  const uid = String(record.uid || fallbackUid || "").trim();
  const topics = record.topics && typeof record.topics === "object" && !Array.isArray(record.topics) ? record.topics : {};
  const known = new Set();
  for (const id of record.knownTopicIds || []) if (id) known.add(String(id));
  for (const id of Object.keys(topics)) if (id) known.add(String(id));
  return {
    ...record,
    version: Number(record.version || SELL_HISTORY_VERSION),
    key: record.key || (uid ? `sell:${uid}` : ""),
    type: "sell",
    uid,
    sourceOrigin: normalizeSiteOrigin(record.sourceOrigin || getOriginFromText(record.url || "") || "") || "",
    knownTopicIds: Array.from(known),
    topics,
  };
}

function migrateLegacySellHistoryRecord(record, fallbackUid, version) {
  return {
    ...record,
    version: SELL_HISTORY_VERSION,
    uid: record.uid || fallbackUid || "",
    migratedFromVersion: version || 0,
  };
}

function latestIso(a, b) {
  if (!a) return b || "";
  if (!b) return a || "";
  return new Date(a).getTime() >= new Date(b).getTime() ? a : b;
}

function isHistoryUid(uid) {
  return /^\d{4,}$/.test(String(uid || "").trim());
}

async function readSellSourceIndex(baseHandle = rootHandle) {
  try {
    const dir = await getLocalHistoryDirectory(false, baseHandle);
    if (!dir) return await seedSellSourceIndex(baseHandle);
    const handle = await dir.getFileHandle(SELL_SOURCE_INDEX_FILE);
    const file = await handle.getFile();
    const parsed = JSON.parse(await file.text());
    const sources = normalizeSellSourceIndex(parsed);
    if (sources.length) return sources;
  } catch {
    // Missing or damaged indexes are rebuilt from existing history once.
  }
  return seedSellSourceIndex(baseHandle);
}

async function writeSellSourceIndex(sources, baseHandle = rootHandle) {
  const dir = await getLocalHistoryDirectory(true, baseHandle);
  if (!dir) return false;
  const normalized = normalizeSellSourceIndex({ sources });
  const payload = {
    version: 1,
    updatedAt: new Date().toISOString(),
    sources: normalized,
  };
  const handle = await dir.getFileHandle(SELL_SOURCE_INDEX_FILE, { create: true });
  const writable = await handle.createWritable({ keepExistingData: false });
  await writable.write(JSON.stringify(payload, null, 2));
  await writable.close();
  return true;
}

function normalizeSellSourceIndex(input) {
  const raw = Array.isArray(input) ? input : input && Array.isArray(input.sources) ? input.sources : [];
  const byUid = new Map();
  for (const item of raw) {
    const uid = String(item && item.uid || "").trim();
    if (!isHistoryUid(uid)) continue;
    const previous = byUid.get(uid) || {};
    byUid.set(uid, {
      ...previous,
      ...item,
      uid,
      sourceOrigin: normalizeSiteOrigin(item.sourceOrigin || previous.sourceOrigin || getOriginFromText(item.url || previous.url || "") || "") || "",
      url: item.url || previous.url || `${normalizeSiteOrigin(item.sourceOrigin || previous.sourceOrigin || "") || getSiteOrigin()}/homepage/sell/${encodeURIComponent(uid)}`,
      userName: cleanTitle(item.userName || item.name || previous.userName || ""),
      lastScannedAt: latestIso(previous.lastScannedAt, item.lastScannedAt),
      lastTotal: Number(item.lastTotal || previous.lastTotal || 0),
      lastPageCount: Number(item.lastPageCount || previous.lastPageCount || 0),
      knownTopicCount: Number(item.knownTopicCount || previous.knownTopicCount || 0),
      parsedTopicCount: Number(item.parsedTopicCount || previous.parsedTopicCount || 0),
    });
  }
  return Array.from(byUid.values()).sort((a, b) => {
    const time = new Date(b.lastScannedAt || 0).getTime() - new Date(a.lastScannedAt || 0).getTime();
    if (time) return time;
    return String(a.uid).localeCompare(String(b.uid), "zh-Hans-CN", { numeric: true });
  });
}

async function seedSellSourceIndex(baseHandle = rootHandle) {
  const sources = [];
  const cached = loadSourceHistory();
  for (const value of Object.values(cached || {})) {
    const source = makeSellSourceIndexRecord(value);
    if (source) sources.push(source);
  }

  if (!sources.length) {
    const dir = await getSellHistoryDirectory(false, baseHandle);
    if (dir) {
      for await (const [name, handle] of dir.entries()) {
        if (!handle || handle.kind !== "file") continue;
        const match = String(name || "").match(/^(\d{4,})\.json$/);
        if (!match) continue;
        const record = await readSellHistoryFile(match[1], baseHandle);
        const source = makeSellSourceIndexRecord(record);
        if (source) sources.push(source);
      }
    }
  }

  const normalized = normalizeSellSourceIndex({ sources });
  if (normalized.length) await writeSellSourceIndex(normalized, baseHandle).catch(() => {});
  return normalized;
}

async function updateSellSourceIndexFromHistory(history, baseHandle = rootHandle) {
  const existing = await readSellSourceIndex(baseHandle);
  const next = [...existing];
  for (const value of Object.values(history || {})) {
    const source = makeSellSourceIndexRecord(value);
    if (source) next.push(source);
  }
  await writeSellSourceIndex(next, baseHandle);
}

function makeSellSourceIndexRecord(record) {
  const normalized = normalizeSellHistoryRecord(record, record && record.uid || "");
  if (!isHistoryUid(normalized.uid)) return null;
  const topics = normalized.topics || {};
  return {
    uid: normalized.uid,
    url: normalized.url || `${normalizeSiteOrigin(normalized.sourceOrigin || "") || getSiteOrigin()}/homepage/sell/${encodeURIComponent(normalized.uid)}`,
    sourceOrigin: normalized.sourceOrigin || "",
    userName: cleanTitle(normalized.userName || ""),
    lastScannedAt: normalized.lastScannedAt || "",
    lastTotal: Number(normalized.lastTotal || 0),
    lastPageCount: Number(normalized.lastPageCount || 0),
    knownTopicCount: (normalized.knownTopicIds || []).length,
    parsedTopicCount: Object.keys(topics).length,
  };
}

async function renderSavedSellSources() {
  const list = $("saved-sell-list");
  const count = $("saved-sell-count");
  if (!list || !count) return;
  if (!rootHandle) {
    list.textContent = "选择根目录后读取。";
    count.textContent = "未读取";
    return;
  }
  if (!(await hasDirectoryPermission(rootHandle))) {
    list.textContent = "根目录未授权。";
    count.textContent = "需授权";
    return;
  }
  const sources = await readSellSourceIndex();
  count.textContent = `${sources.length} 位`;
  if (!sources.length) {
    list.textContent = "暂无已保存博主。解析 sell 页后会自动记录。";
    return;
  }
  list.innerHTML = sources.map((source) => {
    const name = source.userName || `uid ${source.uid}`;
    const total = source.lastTotal || source.knownTopicCount || 0;
    const parsed = source.parsedTopicCount || 0;
    return `
      <label class="saved-sell-row">
        <input class="saved-sell-check" type="checkbox" value="${escapeHtml(source.uid)}" data-url="${escapeHtml(source.url)}">
        <span>
          <span class="saved-sell-name" title="${escapeHtml(name)}">${escapeHtml(name)}</span>
          <span class="saved-sell-meta">uid ${escapeHtml(source.uid)} · ${escapeHtml(String(parsed))}/${escapeHtml(String(total))} · ${escapeHtml(formatShortDate(source.lastScannedAt))}</span>
        </span>
      </label>
    `;
  }).join("");
}

function addSelectedSavedSellsToInput() {
  const selected = Array.from(document.querySelectorAll(".saved-sell-check:checked"))
    .map((input) => input.dataset.url || "")
    .filter(Boolean);
  if (!selected.length) {
    setSummary("请先勾选要加入的博主。");
    return;
  }
  const currentEntries = parseBatchInput($("batch-input").value);
  const seen = new Set(currentEntries.map((entry) => getEntrySourceKey(entry)).filter(Boolean));
  const urls = currentEntries.map((entry) => entry.url);
  let added = 0;
  for (const url of selected) {
    const entry = parseBatchInput(url)[0];
    const key = getEntrySourceKey(entry);
    if (!entry || !key || seen.has(key)) continue;
    seen.add(key);
    urls.push(entry.url);
    added += 1;
  }
  $("batch-input").value = urls.join("\n");
  syncFloatingFromMain();
  saveSettings();
  setSummary(added ? `已加入 ${added} 位博主。` : "所选博主已在批量链接中。");
}

function formatShortDate(value) {
  if (!value) return "未扫描";
  const date = new Date(value);
  if (Number.isNaN(date.getTime())) return "未扫描";
  return `${date.getFullYear()}-${String(date.getMonth() + 1).padStart(2, "0")}-${String(date.getDate()).padStart(2, "0")}`;
}

async function prepareRootHistory(previousRoot, nextRoot) {
  const result = {
    migrated: 0,
    cacheSeeded: 0,
    skipped: 0,
    errors: [],
    sameRoot: false,
  };
  if (!nextRoot) return result;

  if (previousRoot && (await isSameDirectoryHandle(previousRoot, nextRoot))) {
    result.sameRoot = true;
  } else if (previousRoot) {
    await migrateSellHistoryBetweenRoots(previousRoot, nextRoot, result);
  }
  await seedSellHistoryFromCache(nextRoot, result);
  return result;
}

async function migrateSellHistoryBetweenRoots(previousRoot, nextRoot, result) {
  let sourceDir = null;
  try {
    sourceDir = await getSellHistoryDirectory(false, previousRoot);
  } catch (error) {
    result.errors.push(`old-root:${String(error && error.message || error)}`);
    return;
  }
  if (!sourceDir) return;

  try {
    await getSellHistoryDirectory(true, nextRoot);
  } catch (error) {
    result.errors.push(`new-root:${String(error && error.message || error)}`);
    return;
  }

  for await (const [name, handle] of sourceDir.entries()) {
    if (!handle || handle.kind !== "file") continue;
    const match = String(name || "").match(/^(\d{4,})\.json$/);
    if (!match) continue;
    const uid = match[1];
    try {
      const sourceRecord = await readSellHistoryFile(uid, previousRoot);
      if (!sourceRecord) {
        result.skipped += 1;
        continue;
      }
      const targetRecord = await readSellHistoryFile(uid, nextRoot);
      const merged = mergeSellHistoryRecords(targetRecord, sourceRecord, uid);
      await writeSellHistoryFile(uid, merged, nextRoot);
      result.migrated += 1;
    } catch (error) {
      result.errors.push(`${uid}:${String(error && error.message || error)}`);
    }
  }
}

async function seedSellHistoryFromCache(nextRoot, result) {
  const cached = loadSourceHistory();
  for (const [key, value] of Object.entries(cached || {})) {
    if (!key.startsWith("sell:") || !value || typeof value !== "object") continue;
    const uid = String(value.uid || key.slice(5) || "").trim();
    if (!isHistoryUid(uid)) continue;
    try {
      const targetRecord = await readSellHistoryFile(uid, nextRoot);
      const merged = mergeSellHistoryRecords(targetRecord, value, uid);
      await writeSellHistoryFile(uid, merged, nextRoot);
      if (!targetRecord) result.cacheSeeded += 1;
    } catch (error) {
      result.errors.push(`cache:${uid}:${String(error && error.message || error)}`);
    }
  }
  await updateSellSourceIndexFromHistory(cached, nextRoot).catch((error) => {
    result.errors.push(`source-index:${String(error && error.message || error)}`);
  });
}

async function isSameDirectoryHandle(a, b) {
  if (!a || !b) return false;
  if (a === b) return true;
  if (!a.isSameEntry) return false;
  try {
    return await a.isSameEntry(b);
  } catch {
    return false;
  }
}

function formatRootHistorySummary(prefix, result) {
  const parts = [prefix];
  if (result && result.sameRoot) parts.push("同一目录，历史保持不变");
  if (result && result.migrated) parts.push(`复制历史 ${result.migrated} 个 uid`);
  if (result && result.cacheSeeded) parts.push(`缓存补写 ${result.cacheSeeded} 个 uid`);
  if (result && result.errors && result.errors.length) parts.push(`历史复制异常 ${result.errors.length} 个`);
  if (parts.length === 1) parts.push("历史目录已准备");
  return `${parts.join("；")}。`;
}

async function getSellHistoryDirectory(create, baseHandle = rootHandle) {
  if (!baseHandle) return null;
  if (!(await ensureDirectoryPermission(baseHandle))) return null;
  try {
    const appDir = await getLocalHistoryDirectory(create, baseHandle);
    if (!appDir) return null;
    return appDir.getDirectoryHandle(SELL_HISTORY_DIR, { create: Boolean(create) });
  } catch (error) {
    if (!create && error && error.name === "NotFoundError") return null;
    throw error;
  }
}

async function getLocalHistoryDirectory(create, baseHandle = rootHandle) {
  if (!baseHandle) return null;
  if (!(await ensureDirectoryPermission(baseHandle))) return null;
  try {
    return baseHandle.getDirectoryHandle(LOCAL_HISTORY_DIR, { create: Boolean(create) });
  } catch (error) {
    if (!create && error && error.name === "NotFoundError") return null;
    throw error;
  }
}

async function readSellHistoryFile(uid, baseHandle = rootHandle) {
  uid = String(uid || "").trim();
  if (!isHistoryUid(uid)) return null;
  try {
    const dir = await getSellHistoryDirectory(false, baseHandle);
    if (!dir) return null;
    const handle = await dir.getFileHandle(`${uid}.json`);
    const file = await handle.getFile();
    const parsed = JSON.parse(await file.text());
    return normalizeSellHistoryRecord(parsed, uid);
  } catch (error) {
    if (error && (error.name === "NotFoundError" || error.name === "SyntaxError")) return null;
    return null;
  }
}

async function writeSellHistoryFile(uid, record, baseHandle = rootHandle) {
  uid = String(uid || "").trim();
  if (!isHistoryUid(uid)) return false;
  const dir = await getSellHistoryDirectory(true, baseHandle);
  if (!dir) return false;
  const handle = await dir.getFileHandle(`${uid}.json`, { create: true });
  const writable = await handle.createWritable({ keepExistingData: false });
  await writable.write(JSON.stringify(normalizeSellHistoryRecord(record, uid), null, 2));
  await writable.close();
  return true;
}

function enqueueSellHistoryWrite(uid, task) {
  uid = String(uid || "").trim();
  if (!isHistoryUid(uid)) return Promise.resolve(false);
  const previous = sellHistoryWriteQueues.get(uid) || Promise.resolve();
  const current = previous.catch(() => {}).then(task);
  const tracked = current.catch(() => {}).finally(() => {
    if (sellHistoryWriteQueues.get(uid) === tracked) sellHistoryWriteQueues.delete(uid);
  });
  sellHistoryWriteQueues.set(uid, tracked);
  return current;
}

async function mutateSellHistory(uid, mutator) {
  uid = String(uid || "").trim();
  if (!isHistoryUid(uid)) return false;
  return enqueueSellHistoryWrite(uid, async () => {
    const previous = await readSellHistoryFile(uid);
    let record = normalizeSellHistoryRecord(previous, uid);
    const result = await mutator(record);
    if (result === false) return false;
    record = normalizeSellHistoryRecord(result || record, uid);
    await writeSellHistoryFile(uid, record);

    const sourceHistory = loadSourceHistory();
    sourceHistory[`sell:${uid}`] = mergeSellHistoryRecords(sourceHistory[`sell:${uid}`], record, uid);
    saveSourceHistory(sourceHistory);
    await updateSellSourceIndexFromHistory({ [`sell:${uid}`]: record }).catch(() => {});
    await renderSavedSellSources().catch(() => {});
    return record;
  });
}

async function markItemParsedInHistory(item) {
  const uid = String(item && (item.sourceUid || item.authorId || "") || "").trim();
  const pid = String(item && item.pid || "").trim();
  if (!isHistoryUid(uid) || !/^\d{4,}$/.test(pid)) return false;

  return Boolean(await mutateSellHistory(uid, (record) => {
    const now = new Date().toISOString();
    const existing = record.topics && record.topics[pid] || {};
    record.topics = {
      ...(record.topics || {}),
      [pid]: mergeTopicHistory(existing, makeParsedTopicPatch(item, now)),
    };
    record.knownTopicIds = Array.from(new Set([...(record.knownTopicIds || []), pid]));
    return record;
  }));
}

async function markItemDownloadedInHistory(item) {
  const uid = String(item && (item.sourceUid || item.authorId || "") || "").trim();
  const pid = String(item && item.pid || "").trim();
  if (!isHistoryUid(uid) || !/^\d{4,}$/.test(pid)) return false;

  return Boolean(await mutateSellHistory(uid, (record) => {
    const now = new Date().toISOString();
    const existing = record.topics && record.topics[pid] || {};
    record.topics = {
      ...(record.topics || {}),
      [pid]: mergeTopicHistory(existing, {
        downloadedAt: now,
        downloadStatus: "downloaded",
        outputFolder: item.outputFolder || existing.outputFolder || "",
        outputFile: item.outputFile || existing.outputFile || "",
        localDownloadStatus: "downloaded",
        localDownloadMatched: true,
        publishedAtRaw: item.publishedAtRaw || existing.publishedAtRaw || "",
        publishedAt: item.publishedAt || existing.publishedAt || "",
        publishedDate: item.publishedDate || existing.publishedDate || "",
        publishedSort: item.publishedSort || existing.publishedSort || "",
        bytes: Number(item.bytes || existing.bytes || 0),
        estimatedBytes: Number(item.estimatedBytes || existing.estimatedBytes || 0),
        estimatedSampleCount: Number(item.estimatedSampleCount || existing.estimatedSampleCount || 0),
        estimatedAt: item.estimatedAt || existing.estimatedAt || "",
        estimatedError: item.estimatedError || existing.estimatedError || "",
        seconds: Number(item.seconds || existing.seconds || 0),
        segments: Number(item.segments || existing.segments || 0),
      }),
    };
    record.knownTopicIds = Array.from(new Set([...(record.knownTopicIds || []), pid]));
    return record;
  }));
}

function makeParsedTopicPatch(item, now) {
  const status = item && item.status || "";
  return {
    pid: String(item && item.pid || ""),
    title: cleanTitle(item && item.title || ""),
    author: cleanTitle(item && item.author || ""),
    authorId: String(item && item.authorId || item && item.sourceUid || ""),
    localDownloadStatus: item && item.localDownloadStatus === "downloaded" ? "downloaded" : "",
    localDownloadMatched: Boolean(item && item.localDownloadStatus === "downloaded" && item.localDownloadMatched),
    ignored: Boolean(item && item.ignored),
    ignoredAt: item && item.ignoredAt || "",
    ignoreReason: item && item.ignoreReason || "",
    ignoredBy: item && item.ignoredBy || "",
    publishedAtRaw: item && item.publishedAtRaw || "",
    publishedAt: item && item.publishedAt || "",
    publishedDate: item && item.publishedDate || "",
    publishedSort: item && item.publishedSort || "",
    hasVideo: status !== "excluded",
    firstSeenAt: now,
    lastSeenAt: now,
    parsedAt: now,
    parseStatus: status,
    parseMessage: item && item.message || "",
    parseError: item && item.error || "",
    canDownload: Boolean(item && item.canDownload),
    selectedByDefault: Boolean(item && item.selected),
    selectedManifestKind: item && item.selectedManifestKind || "",
    selectedManifestUrl: item && item.selectedManifestUrl || "",
    previewManifestUrl: item && item.previewManifestUrl || "",
    derivedManifestUrl: item && item.derivedManifestUrl || "",
    attachmentId: item && item.attachmentId || null,
    videoTimeLength: Number(item && item.videoTimeLength || 0),
    seconds: Number(item && item.seconds || 0),
    segments: Number(item && item.segments || 0),
    estimatedBytes: Number(item && item.estimatedBytes || 0),
    estimatedSampleCount: Number(item && item.estimatedSampleCount || 0),
    estimatedAt: item && item.estimatedAt || "",
    estimatedError: item && item.estimatedError || "",
  };
}

function mergeTopicHistory(existing, patch) {
  const merged = { ...(existing || {}) };
  for (const [key, value] of Object.entries(patch || {})) {
    if (["ignoredAt", "ignoreReason", "ignoredBy"].includes(key)) {
      merged[key] = value || "";
      continue;
    }
    if (value === "" || value == null) continue;
    if (typeof value === "number" && !value) {
      if (merged[key] == null) merged[key] = value;
      continue;
    }
    merged[key] = value;
  }
  merged.pid = String(patch && patch.pid || merged.pid || "");
  merged.firstSeenAt = existing && existing.firstSeenAt || patch && patch.firstSeenAt || merged.firstSeenAt || "";
  merged.lastSeenAt = patch && patch.lastSeenAt || merged.lastSeenAt || "";
  return merged;
}

function inferSourceRecords(report) {
  const sources = [];
  const seen = new Set();
  for (const item of report && report.items || []) {
    const key = item.sourceKey || (item.sourceType === "sell" ? `sell:${item.sourceUid}` : `post:${item.pid}`);
    if (!key || seen.has(key)) continue;
    seen.add(key);
    sources.push({
      key,
      type: key.startsWith("sell:") ? "sell" : "post",
      uid: key.startsWith("sell:") ? key.slice(5) : "",
      pid: key.startsWith("post:") ? key.slice(5) : "",
      url: item.sourceUrl || item.url || "",
      sourceOrigin: item.sourceOrigin || "",
      status: "parsed",
      parsedAt: item.finishedAt || item.startedAt || "",
      itemCount: 1,
      scanSummary: null,
    });
  }
  return sources;
}

function refreshItemIndexes() {
  if (!activeReport || !Array.isArray(activeReport.items)) return;
  activeReport.items.forEach((item, index) => {
    item.index = index;
    if (!item.id) item.id = makeItemId(item, index);
    if (item.order == null) item.order = index;
  });
}

function makeItemId(item, fallbackIndex = 0) {
  const key = item && (item.sourceKey || item.sourceUid || item.sourceOrigin || "") || "source";
  const pid = item && item.pid || fallbackIndex;
  return `${String(key).replace(/[^a-z0-9:_-]+/gi, "_")}:${pid}:${fallbackIndex}`;
}

function getItemById(id) {
  if (!activeReport || !Array.isArray(activeReport.items)) return null;
  return activeReport.items.find((item) => String(item.id || "") === String(id || "")) || null;
}

function mergeSourceInputText(currentText) {
  const sources = activeReport && Array.isArray(activeReport.sources) ? activeReport.sources : [];
  const out = [];
  const seen = new Set();
  for (const source of sources) {
    if (!source || !source.url || seen.has(source.key)) continue;
    seen.add(source.key);
    out.push(source.url);
  }
  for (const entry of parseBatchInput(currentText || "")) {
    const key = getEntrySourceKey(entry);
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(entry.url);
  }
  return out.join("\n");
}

function toggleParsedSourcesVisibility() {
  hideParsedInputSources = !hideParsedInputSources;
  applyParsedSourcesVisibility();
  saveSettings();
}

function applyParsedSourcesVisibility() {
  const input = $("batch-input");
  if (!input) return;
  const parsedKeys = getParsedSourceKeys();
  const currentEntries = parseBatchInput(input.value);
  let nextEntries;

  if (hideParsedInputSources) {
    const active = document.activeElement;
    if (isBusy() || (active === input && !input.dataset.allowParsedSourceRewrite)) {
      updateParsedSourcesToggle();
      return;
    }
    nextEntries = currentEntries.filter((entry) => !parsedKeys.has(getEntrySourceKey(entry)));
  } else {
    const sources = activeReport && Array.isArray(activeReport.sources) ? activeReport.sources : [];
    const fromSources = sources
      .filter((source) => source && source.url)
      .map((source) => ({
        type: source.type,
        uid: source.uid,
        pid: source.pid,
        url: source.url,
        sourceOrigin: source.sourceOrigin || "",
      }));
    nextEntries = [...fromSources, ...currentEntries];
  }

  const seen = new Set();
  const urls = [];
  for (const entry of nextEntries) {
    const key = getEntrySourceKey(entry);
    if (!key || seen.has(key)) continue;
    seen.add(key);
    urls.push(entry.url);
  }
  input.value = urls.join("\n");
  syncFloatingFromMain();
  updateParsedSourcesToggle();
  saveSettings();
}

function updateParsedSourcesToggle() {
  const button = $("toggle-parsed-sources");
  if (!button) return;
  button.textContent = hideParsedInputSources ? "显示已解析来源" : "隐藏已解析来源";
  button.disabled = isBusy() || !activeReport || !Array.isArray(activeReport.sources) || !activeReport.sources.length;
}

function restoreHistoryItemsForEntries(entries, sourceHistory, options) {
  if (!activeReport || !Array.isArray(activeReport.items)) return 0;
  const existingPids = new Set(activeReport.items.map((item) => String(item.pid)));
  let restored = 0;

  for (const entry of entries || []) {
    if (!entry || entry.type !== "sell") continue;
    const record = normalizeSellHistoryRecord(getSourceHistoryRecord(entry, sourceHistory), entry.uid);
    const topics = record.topics || {};
    for (const [pid, topic] of Object.entries(topics)) {
      if (!/^\d{4,}$/.test(String(pid)) || existingPids.has(String(pid))) continue;
      if (options && options.sellVideoOnly && topic && topic.hasVideo === false && !isHistoryTopicDownloaded(topic)) continue;
      const item = makePlanItemFromHistoryTopic(entry, record, pid, topic, activeReport.items.length);
      if (!item) continue;
      existingPids.add(String(pid));
      activeReport.items.push(item);
      restored += 1;
    }
  }
  return restored;
}

function makePlanItemFromHistoryTopic(entry, record, pid, topic, index) {
  if (!topic || typeof topic !== "object") return null;
  const downloaded = isHistoryTopicDownloaded(topic);
  const hasParsed = Boolean(topic.parsedAt || topic.parseStatus || topic.selectedManifestUrl || topic.previewManifestUrl || topic.derivedManifestUrl);
  if (!downloaded && !hasParsed) return null;

  const selectedManifestUrl = String(topic.selectedManifestUrl || "");
  const status = downloaded ? "ok" : normalizeHistoryParseStatus(topic.parseStatus, topic);
  const canDownload = !downloaded && Boolean(topic.canDownload && selectedManifestUrl);
  const selectedKind = String(topic.selectedManifestKind || "");

  return {
    id: makeItemId({ pid, sourceKey: getEntrySourceKey(entry), sourceUid: record.uid || entry.uid || "" }, index),
    order: index,
    index,
    pid: String(pid),
    url: `${normalizeSiteOrigin(entry.sourceOrigin || record.sourceOrigin || "") || getSiteOrigin()}/post/details?pid=${encodeURIComponent(pid)}`,
    sourceOrigin: normalizeSiteOrigin(entry.sourceOrigin || record.sourceOrigin || "") || getSiteOrigin(),
    sourceType: "sell",
    sourceUid: record.uid || entry.uid || "",
    sourceUrl: entry.url || record.url || "",
    sourceTitle: record.userName || "",
    sourceKey: getEntrySourceKey(entry),
    newFromScan: false,
    localDownloadStatus: downloaded ? "downloaded" : "missing",
    localDownloadMatched: downloaded,
    ignored: Boolean(topic.ignored),
    ignoredAt: topic.ignoredAt || "",
    ignoreReason: topic.ignoreReason || "",
    ignoredBy: topic.ignoredBy || "",
    selected: !topic.ignored && canDownload && Boolean(topic.selectedByDefault || selectedKind === "full"),
    canDownload,
    status,
    title: cleanTitle(topic.title || pid),
    author: cleanTitle(topic.author || record.userName || entry.sourceTitle || "") || "unknown_author",
    authorId: String(topic.authorId || record.uid || entry.uid || ""),
    publishedAtRaw: topic.publishedAtRaw || "",
    publishedAt: topic.publishedAt || "",
    publishedDate: topic.publishedDate || "",
    publishedSort: topic.publishedSort || "",
    attachmentId: topic.attachmentId || null,
    videoTimeLength: Number(topic.videoTimeLength || 0),
    selectedManifestUrl,
    selectedManifestKind: selectedKind,
    previewManifestUrl: String(topic.previewManifestUrl || ""),
    derivedManifestUrl: String(topic.derivedManifestUrl || ""),
    segments: Number(topic.segments || 0),
    seconds: Number(topic.seconds || 0),
    bytes: Number(topic.bytes || 0),
    estimatedBytes: Number(topic.estimatedBytes || 0),
    estimatedSampleCount: Number(topic.estimatedSampleCount || 0),
    estimatedAt: topic.estimatedAt || "",
    estimatedError: topic.estimatedError || "",
    outputFolder: topic.outputFolder || "",
    outputFile: topic.outputFile || "",
    manifestFile: topic.manifestFile || "",
    progress: 100,
    message: downloaded ? "本地历史标记为已下载" : topic.parseMessage || "从本地历史恢复",
    error: topic.parseError || "",
    startedAt: topic.parsedAt || "",
    finishedAt: topic.downloadedAt || topic.parsedAt || "",
    durationMs: 0,
    restoredFromHistory: true,
  };
}

function normalizeHistoryParseStatus(status, topic) {
  const value = String(status || "").trim();
  if (["parsed", "preview", "excluded", "failed"].includes(value)) return value;
  if (topic && topic.selectedManifestKind === "full") return "parsed";
  if (topic && topic.selectedManifestKind === "preview") return "preview";
  if (topic && topic.canDownload) return "parsed";
  return topic && topic.parseError ? "failed" : "pending";
}

function makePlanItem(entry, index) {
  return {
    id: makeItemId(entry, index),
    order: index,
    index,
    pid: entry.pid,
    url: entry.url,
    sourceOrigin: entry.sourceOrigin || "",
    sourceType: entry.sourceType || "post",
    sourceUid: entry.sourceUid || "",
    sourceUrl: entry.sourceUrl || "",
    sourceTitle: entry.sourceTitle || "",
    sourceKey: entry.sourceKey || "",
    newFromScan: Boolean(entry.newFromScan),
    localDownloadStatus: entry.newFromScan ? "new_missing" : "missing",
    localDownloadMatched: false,
    ignored: false,
    ignoredAt: "",
    ignoreReason: "",
    ignoredBy: "",
    selected: false,
    canDownload: false,
    status: "pending",
    title: "",
    author: "",
    authorId: "",
    publishedAtRaw: "",
    publishedAt: "",
    publishedDate: "",
    publishedSort: "",
    attachmentId: null,
    videoTimeLength: 0,
    selectedManifestUrl: "",
    selectedManifestKind: "",
    previewManifestUrl: "",
    derivedManifestUrl: "",
    segments: 0,
    seconds: 0,
    bytes: 0,
    estimatedBytes: 0,
    estimatedSampleCount: 0,
    estimatedAt: "",
    estimatedError: "",
    outputFolder: "",
    outputFile: "",
    manifestFile: "",
    progress: 0,
    message: "",
    error: "",
    startedAt: "",
    finishedAt: "",
    durationMs: 0,
  };
}

async function analyzePlanItem(item, options) {
  item.status = "running";
  item.progress = 2;
  item.message = "读取帖子接口";
  item.startedAt = new Date().toISOString();
  scheduleRender();

  const started = Date.now();
  const topic = await fetchTopic(item.pid, item.sourceOrigin);
  const video = findVideoAttachment(topic);
  item.title = cleanTitle(topic.title || item.pid);
  item.author = cleanTitle(getAuthorName(topic)) || cleanTitle(item.sourceTitle) || "unknown_author";
  item.authorId = getAuthorId(topic) || item.sourceUid || "";
  applyTopicPublishedFields(item, topic);

  if (!video) {
    item.status = "excluded";
    item.canDownload = false;
    item.selected = false;
    item.message = "详情页未找到视频附件，已排除";
    item.progress = 100;
    item.finishedAt = new Date().toISOString();
    item.durationMs = Date.now() - started;
    return;
  }

  item.attachmentId = video.id || null;
  item.videoTimeLength = Number(video.video_time_length || 0);

  let previewUrl = String(video.remoteUrl || "");
  if (!previewUrl && video.id) {
    const attachment = await fetchAttachment(video.id, item.pid, item.sourceOrigin);
    previewUrl = String(attachment && attachment.remoteUrl || "");
  }
  if (!previewUrl) throw new Error("视频附件没有 remoteUrl");

  item.previewManifestUrl = previewUrl;
  item.progress = 20;
  item.message = "校验 preview manifest";
  scheduleRender();

  const preview = await fetchMediaManifest(previewUrl, options);
  if (!isUsableManifest(preview)) {
    throw new Error(`preview manifest 不可用：${describeManifestFailure(preview)}`);
  }
  const previewUnsupported = getUnsupportedKeyMethods(preview);
  if (previewUnsupported.length) {
    throw new Error(`暂不支持 HLS 加密方式：${previewUnsupported.join(", ")}`);
  }

  const derivedUrls = deriveM3u8Candidates(preview.analysis.segmentEntries, previewUrl)
    .filter((url) => url && url !== preview.url && url !== previewUrl);
  item.derivedManifestUrl = derivedUrls[0] || "";
  let selected = preview;
  let selectedKind = "preview";

  if (derivedUrls.length) {
    for (let index = 0; index < derivedUrls.length; index += 1) {
      const derivedUrl = derivedUrls[index];
      item.progress = 55 + Math.min(25, index * 3);
      item.message = `校验完整 manifest 候选 ${index + 1}/${derivedUrls.length}`;
      scheduleRender();
      let full = null;
      try {
        full = await fetchMediaManifest(derivedUrl, options);
      } catch {
        continue;
      }
      const fullUnsupported = getUnsupportedKeyMethods(full);
      if (fullUnsupported.length) {
        throw new Error(`暂不支持 HLS 加密方式：${fullUnsupported.join(", ")}`);
      }
      if (isBetterFullManifest(full, selected, item.videoTimeLength)) {
        selected = full;
        selectedKind = "full";
        item.derivedManifestUrl = derivedUrl;
        break;
      }
    }
  }

  setItemManifest(item, selected);
  item.selectedManifestUrl = selected.url;
  item.selectedManifestKind = selectedKind;
  item.segments = selected.analysis.segmentEntries.length;
  item.seconds = Math.round(selected.analysis.totalDurationSeconds);
  item.canDownload = true;
  item.selected = selectedKind === "full" || Boolean(options.fallbackPreview);
  item.status = selectedKind === "full" ? "parsed" : "preview";
  item.progress = 100;
  item.message = selectedKind === "full"
    ? `完整资源可用：${item.segments} 片，约 ${item.seconds}s`
    : `仅解析到预览：${item.segments} 片，约 ${item.seconds}s${item.selected ? "" : "，默认不勾选"}`;
  item.finishedAt = new Date().toISOString();
  item.durationMs = Date.now() - started;
}

async function analyzePlanItems(items, options) {
  let nextIndex = 0;
  const workerCount = Math.min(PARSE_CONCURRENCY, Math.max(1, items.length));
  async function worker() {
    while (!stopRequested) {
      const item = items[nextIndex];
      nextIndex += 1;
      if (!item) return;
      await analyzePlanItemSafely(item, options);
    }
  }
  await Promise.all(Array.from({ length: workerCount }, worker));
  if (stopRequested) {
    for (const item of items) {
      if (item.status !== "pending") continue;
      item.status = "skipped";
      item.message = "用户停止";
      item.progress = 100;
    }
  }
}

async function analyzePlanItemSafely(item, options) {
  try {
    throwIfStopRequested();
    await analyzePlanItem(item, options);
    throwIfStopRequested();
    await syncLocalDownloadMatchForItem(item, options);
  } catch (error) {
    item.status = stopRequested ? "stopped" : "failed";
    item.canDownload = false;
    item.selected = false;
    item.error = String(error && error.message || error);
    item.message = item.error;
    item.progress = 100;
  } finally {
    if (item.status !== "failed" && item.status !== "stopped") {
      await markItemParsedInHistory(item).catch(() => {});
    }
    scheduleRender();
  }
}

function setItemManifest(item, manifest) {
  Object.defineProperty(item, "_selectedManifest", {
    value: manifest,
    writable: true,
    configurable: true,
    enumerable: false,
  });
}

function isUsableManifest(manifest) {
  return Boolean(
    manifest
    && manifest.ok
    && manifest.analysis
    && manifest.analysis.hasExtM3u
    && Array.isArray(manifest.analysis.segmentEntries)
    && manifest.analysis.segmentEntries.length > 0
  );
}

function getManifestMediaContainer(manifest) {
  const analysis = manifest && manifest.analysis || {};
  if (analysis.mediaContainer) return analysis.mediaContainer;
  const entries = Array.isArray(analysis.segmentEntries) ? analysis.segmentEntries : [];
  return entries.some((entry) => (
    entry
    && (entry.map || /\.(?:m4s|mp4|cmfv|m4v)(?:[?#]|$)/i.test(entry.url || ""))
  )) ? "mp4" : "ts";
}

function getUnsupportedKeyMethods(manifest) {
  const methods = manifest && manifest.analysis && manifest.analysis.keyMethods || [];
  return methods.filter((method) => method && method !== "AES-128" && method !== "NONE");
}

function isMasterManifest(manifest) {
  return Boolean(
    manifest
    && manifest.ok
    && manifest.analysis
    && manifest.analysis.hasExtM3u
    && Array.isArray(manifest.analysis.variantUrls)
    && manifest.analysis.variantUrls.length > 0
  );
}

function describeManifestFailure(manifest) {
  if (!manifest) return "空响应";
  if (!manifest.ok) return `HTTP ${manifest.status}`;
  if (!manifest.analysis || !manifest.analysis.hasExtM3u) return "不是有效 M3U8";
  if (isMasterManifest(manifest)) return "master playlist 没有可用媒体分片";
  if (!manifest.analysis.segmentEntries || !manifest.analysis.segmentEntries.length) return "M3U8 没有媒体分片";
  return "未知错误";
}

async function refreshItemManifestFromTopic(item, options, reason) {
  const previousUrl = String(item && item.selectedManifestUrl || "");
  item.error = "";
  item.message = `索引失效（${reason}），重新解析帖子`;
  item.progress = Math.max(12, Number(item.progress || 0));
  scheduleRender();

  await analyzePlanItem(item, options || {});
  await markItemParsedInHistory(item).catch(() => {});

  if (!item.selectedManifestUrl) {
    throw new Error("索引刷新失败：没有可用 manifest");
  }
  if (item.selectedManifestKind !== "full" && !(options && options.fallbackPreview)) {
    throw new Error("索引刷新后仅得到预览，未启用预览下载");
  }

  const cached = item._selectedManifest && item._selectedManifest.url === item.selectedManifestUrl
    ? item._selectedManifest
    : null;
  const refreshed = cached || await fetchMediaManifest(item.selectedManifestUrl, options);
  if (!isUsableManifest(refreshed)) {
    throw new Error(`索引刷新后仍不可用：${describeManifestFailure(refreshed)}`);
  }

  setItemManifest(item, refreshed);
  item.error = "";
  item.message = previousUrl && previousUrl !== item.selectedManifestUrl
    ? "索引已刷新，开始下载"
    : "索引重新校验完成，开始下载";
  scheduleRender();
  return refreshed;
}

async function getItemManifest(item, options = {}) {
  if (item._selectedManifest && item._selectedManifest.url === item.selectedManifestUrl && isUsableManifest(item._selectedManifest)) {
    return item._selectedManifest;
  }
  if (!item.selectedManifestUrl) throw new Error("manifest 地址为空");

  let manifest = null;
  try {
    manifest = await fetchMediaManifest(item.selectedManifestUrl, options);
  } catch (error) {
    if (options.refreshOnStale !== false) {
      return refreshItemManifestFromTopic(item, options, String(error && error.message || error || "请求失败"));
    }
    throw error;
  }

  if (!isUsableManifest(manifest)) {
    if (options.refreshOnStale !== false) {
      return refreshItemManifestFromTopic(item, options, describeManifestFailure(manifest));
    }
    throw new Error(`manifest 不可用：${describeManifestFailure(manifest)}`);
  }
  setItemManifest(item, manifest);
  return manifest;
}

async function downloadParsedSelection(options) {
  if (isBusy()) return;
  if (!activeReport || !Array.isArray(activeReport.items)) {
    setSummary("请先解析资源。");
    return;
  }

  const selectedItems = getSelectedDownloadItems();
  if (!selectedItems.length) {
    setSummary("没有选中的可下载资源。");
    return;
  }
  if (!rootHandle) {
    setSummary("请先选择保存根目录。");
    return;
  }
  if (!(await ensureDirectoryPermission(rootHandle))) {
    setSummary("目录没有写入权限。");
    return;
  }

  beginStoppableRun();
  running = true;
  beginBusy("downloading");
  activeReport.stage = "downloading";
  activeReport.downloadStartedAt = activeReport.downloadStartedAt || new Date().toISOString();
  activeReport.options = {
    ...activeReport.options,
    ...options,
    rootName: rootHandle.name,
  };
  updateFloatingButtons();
  const taskConcurrency = clampInteger(options.taskConcurrency, 1, 4, DEFAULT_TASK_CONCURRENCY);
  const mediaConcurrency = clampInteger(options.globalMediaConcurrency, 1, 48, DEFAULT_GLOBAL_MEDIA_CONCURRENCY);
  const workerCount = Math.min(taskConcurrency, selectedItems.length);
  const previousMediaRequestLimiter = activeMediaRequestLimiter;
  const previousMediaKeyCache = activeMediaKeyCache;
  activeMediaRequestLimiter = createMediaRequestLimiter(mediaConcurrency);
  activeMediaKeyCache = new Map();
  setSummary(`准备下载选中的 ${selectedItems.length} 条 · 任务并发 ${workerCount} · 全局请求 ${mediaConcurrency}。`);

  let wasStopped = false;
  let nextIndex = 0;
  let completed = 0;
  const startedThisRun = new Set();

  async function runSelectedItem(item) {
    const started = Date.now();
    startedThisRun.add(item);
    item.startedAt = new Date().toISOString();
    try {
      throwIfStopRequested();
      await downloadParsedItem(item, options);
    } catch (error) {
      item.status = stopRequested ? "stopped" : "failed";
      item.error = String(error && error.message || error);
      item.message = item.error;
      item.progress = 100;
      if (!stopRequested) await markItemParsedInHistory(item).catch(() => {});
    } finally {
      item.finishedAt = new Date().toISOString();
      item.durationMs = Date.now() - started;
      completed += 1;
      scheduleRender();
    }
  }

  async function worker() {
    while (!stopRequested) {
      const index = nextIndex;
      nextIndex += 1;
      if (index >= selectedItems.length) return;

      await runSelectedItem(selectedItems[index]);
      if (!stopRequested && options.delaySeconds > 0 && nextIndex < selectedItems.length) {
        await sleep(options.delaySeconds * 1000);
      }
      setSummary(`下载中：完成 ${completed}/${selectedItems.length} · 任务并发 ${workerCount} · 全局请求 ${mediaConcurrency}`);
    }
  }

  try {
    await Promise.all(Array.from({ length: workerCount }, worker));
  } finally {
    wasStopped = stopRequested;
    if (wasStopped) {
      for (const item of selectedItems) {
        if (startedThisRun.has(item) || ["ok", "failed", "stopped", "skipped"].includes(item.status)) continue;
        item.status = "skipped";
        item.message = "用户停止";
        item.progress = 100;
      }
    }
    const downloadSummary = summarizeDownloadedSelection(selectedItems);
    activeReport.downloadSummary = downloadSummary;
    activeReport.stage = wasStopped
      ? "stopped"
      : downloadSummary.failed > 0 || downloadSummary.stopped > 0
        ? "downloaded_with_errors"
        : "downloaded";
    activeReport.finishedAt = new Date().toISOString();
    await closeHelperTab();
    activeMediaRequestLimiter = previousMediaRequestLimiter;
    activeMediaKeyCache = previousMediaKeyCache;
    clearStoppableRun();
    running = false;
    endBusy("downloading");
    updateFloatingButtons();
    if (wasStopped) stopRequested = false;
  }

  setSummary(formatDownloadSelectionSummary(activeReport.downloadSummary, wasStopped));
  scheduleRender();
}

function summarizeDownloadedSelection(items) {
  const summary = { total: 0, ok: 0, failed: 0, skipped: 0, stopped: 0, other: 0, bytes: 0 };
  for (const item of items || []) {
    summary.total += 1;
    summary.bytes += Number(item && item.bytes || 0);
    if (item && item.status === "ok") summary.ok += 1;
    else if (item && item.status === "failed") summary.failed += 1;
    else if (item && item.status === "skipped") summary.skipped += 1;
    else if (item && item.status === "stopped") summary.stopped += 1;
    else summary.other += 1;
  }
  return summary;
}

function formatDownloadSelectionSummary(summary, stopped) {
  const data = summary || { total: 0, ok: 0, failed: 0, skipped: 0, stopped: 0, other: 0, bytes: 0 };
  const suffix = data.bytes ? `，写入 ${formatBytes(data.bytes)}` : "";
  if (stopped) {
    return `已停止：成功 ${data.ok}，失败 ${data.failed}，跳过 ${data.skipped}，未完成 ${data.stopped + data.other}${suffix}`;
  }
  if (data.failed || data.stopped || data.other) {
    return `下载完成但有异常：成功 ${data.ok}，失败 ${data.failed}，跳过 ${data.skipped}，未完成 ${data.stopped + data.other}${suffix}`;
  }
  return `下载完成：成功 ${data.ok}，跳过 ${data.skipped}${suffix}`;
}

async function downloadParsedItem(item, options) {
  item.status = "running";
  item.progress = Math.max(16, Number(item.progress || 0));
  item.bytes = 0;
  item.message = "准备保存分片";
  scheduleRender();

  let selected = await getItemManifest(item, options);
  for (let attempt = 0; attempt < 2; attempt += 1) {
    item.selectedManifestUrl = selected.url;
    item.segments = selected.analysis.segmentEntries.length;
    item.seconds = Math.round(selected.analysis.totalDurationSeconds);
    const unsupported = getUnsupportedKeyMethods(selected);
    if (unsupported.length) throw new Error(`暂不支持 HLS 加密方式：${unsupported.join(", ")}`);
    if (!item.segments) throw new Error("manifest has no media segments");

    const outputDir = await getOutputDirectory(rootHandle, item.author, options);
    item.outputFolder = options.byAuthor ? sanitizePathPart(item.author || "unknown_author") : rootHandle.name;
    const baseName = renderNameTemplate(options.nameTemplate, item);
    const mediaExt = getManifestMediaContainer(selected) === "mp4" ? ".mp4" : ".ts";
    const prepared = await prepareFileHandle(outputDir, `${baseName}${mediaExt}`, options.conflictMode, mediaExt);
    if (prepared.skipped) {
      item.status = "ok";
      item.canDownload = false;
      item.selected = false;
      item.progress = 100;
      item.bytes = Number(prepared.size || item.bytes || 0);
      item.outputFile = prepared.name;
      item.message = "文件已存在，按设置跳过";
      await markItemDownloadedInHistory(item).catch(() => {});
      return;
    }

    if (options.saveManifest) {
      const manifestResult = await writeTextFile(outputDir, `${baseName}.m3u8`, selected.text, options.conflictMode);
      item.manifestFile = manifestResult.skipped ? `[skipped] ${baseName}.m3u8` : manifestResult.name;
    }

    item.outputFile = prepared.name;
    item.bytes = 0;
    try {
      await writeSegmentsToFile(prepared.handle, selected.analysis.segmentEntries, item, options);
      await commitPreparedFile(outputDir, prepared);
      break;
    } catch (error) {
      await cleanupPreparedFile(outputDir, prepared).catch(() => {});
      if (attempt === 0 && isRetryableMediaFetchError(error)) {
        item.message = "下载阶段 key/分片失效，刷新索引后重试";
        item.error = "";
        item.progress = 16;
        scheduleRender();
        selected = await refreshItemManifestFromTopic(item, options, summarizeError(error));
        continue;
      }
      throw error;
    }
  }
  item.status = "ok";
  item.canDownload = false;
  item.selected = false;
  item.progress = 100;
  item.message = `已保存 ${formatBytes(item.bytes)}`;
  await markItemDownloadedInHistory(item).catch(() => {});
}

function getSelectedDownloadItems() {
  return activeReport && Array.isArray(activeReport.items)
    ? activeReport.items.filter((item) => item.selected && item.canDownload && item.status !== "ok" && !item.ignored)
    : [];
}

async function estimateSelectedResourceSizes() {
  if (isBusy()) return;
  const selectedItems = getSelectedDownloadItems();
  if (!selectedItems.length) {
    setSummary("没有选中的可下载资源。");
    return;
  }

  estimatingSelectedSize = true;
  beginBusy("estimating");
  setSummary(`正在估算 ${selectedItems.length} 条所选资源大小...`);
  scheduleRender();

  let nextIndex = 0;
  let done = 0;
  let ok = 0;
  let failed = 0;
  const workerCount = Math.min(4, selectedItems.length);

  async function worker() {
    while (nextIndex < selectedItems.length) {
      const item = selectedItems[nextIndex];
      nextIndex += 1;
      item.estimatedError = "";
      try {
        await estimateItemResourceSize(item, readOptions());
        ok += 1;
      } catch (error) {
        failed += 1;
        item.estimatedError = String(error && error.message || error);
      } finally {
        await markItemParsedInHistory(item).catch(() => {});
        done += 1;
        setSummary(`正在估算大小 ${done}/${selectedItems.length}，成功 ${ok}，失败 ${failed}`);
        scheduleRender();
      }
    }
  }

  try {
    await Promise.all(Array.from({ length: workerCount }, worker));
  } finally {
    estimatingSelectedSize = false;
    endBusy("estimating");
    setSummary(`大小估算完成：成功 ${ok}，失败 ${failed}。${makeSelectedSizeSummary().text}`);
    scheduleRender();
  }
}

async function estimateItemResourceSize(item, options) {
  const manifest = await getItemManifest(item, options);
  const segments = manifest && manifest.analysis && manifest.analysis.segmentEntries || [];
  if (!segments.length) throw new Error("没有可估算的分片");
  item.segments = segments.length;
  item.seconds = Math.round(manifest.analysis.totalDurationSeconds || item.seconds || 0);

  const indexes = getEstimateSampleIndexes(segments.length);
  const sizes = [];
  for (const index of indexes) {
    const size = await fetchSegmentContentLength(segments[index].url, Math.max(8000, Number(options.segmentTimeoutSeconds || 30) * 1000));
    if (size > 0) sizes.push(size);
  }
  if (!sizes.length) throw new Error("未读到分片 Content-Length");

  const average = sizes.reduce((sum, value) => sum + value, 0) / sizes.length;
  item.estimatedBytes = Math.round(average * segments.length);
  item.estimatedSampleCount = sizes.length;
  item.estimatedAt = new Date().toISOString();
  return item.estimatedBytes;
}

function getEstimateSampleIndexes(total) {
  total = Math.max(0, Number(total) || 0);
  if (total <= 0) return [];
  const sampleCount = Math.min(10, Math.max(3, Math.ceil(total / 2)));
  if (sampleCount >= total) return Array.from({ length: total }, (_, index) => index);
  const last = total - 1;
  return Array.from(new Set(Array.from({ length: sampleCount }, (_, index) => Math.round((last * index) / Math.max(1, sampleCount - 1)))));
}

async function fetchSegmentContentLength(url, timeoutMs) {
  await ensureUrlFetchPermission(url);
  const head = await fetchWithTimeout(url, {
    method: "HEAD",
    credentials: getFetchCredentials(url),
    cache: "no-store",
  }, timeoutMs).catch(() => null);
  const headLength = getResponseContentLength(head);
  if (headLength > 0) return headLength;

  const range = await fetchWithTimeout(url, {
    method: "GET",
    credentials: getFetchCredentials(url),
    cache: "no-store",
    headers: { Range: "bytes=0-0" },
  }, timeoutMs).catch(() => null);
  const rangeTotal = getResponseRangeTotal(range);
  if (rangeTotal > 0) return rangeTotal;
  if (range && range.body) {
    try {
      await range.body.cancel();
    } catch {
      // ignore cancel failures
    }
  }
  return 0;
}

function getResponseContentLength(response) {
  if (!response || !response.ok) return 0;
  const value = Number(response.headers.get("content-length") || 0);
  return Number.isFinite(value) ? value : 0;
}

function getResponseRangeTotal(response) {
  if (!response || response.status !== 206) return 0;
  const range = response.headers.get("content-range") || "";
  const match = range.match(/\/(\d+)$/);
  return match ? Number(match[1]) || 0 : 0;
}

async function backfillMissingPublishedTimes() {
  if (isBusy()) return;
  const items = getPublishedBackfillItems();
  if (!items.length) {
    setSummary("当前结果里没有缺失发布时间的资源。");
    return;
  }

  backfillingPublishedTimes = true;
  beginBusy("backfilling");
  setSummary(`正在补全发布时间 ${items.length} 条...`);
  scheduleRender();

  let nextIndex = 0;
  let done = 0;
  let ok = 0;
  let failed = 0;
  const workerCount = Math.min(4, items.length);

  async function worker() {
    while (nextIndex < items.length) {
      const item = items[nextIndex];
      nextIndex += 1;
      try {
        const topic = await fetchTopic(item.pid, item.sourceOrigin);
        applyTopicPublishedFields(item, topic);
        if (!item.title) item.title = cleanTitle(topic.title || item.pid);
        if (!item.author) item.author = cleanTitle(getAuthorName(topic)) || cleanTitle(item.sourceTitle) || "unknown_author";
        if (!item.authorId) item.authorId = getAuthorId(topic) || item.sourceUid || "";
        if (item.publishedSort) ok += 1;
        else failed += 1;
      } catch (error) {
        failed += 1;
        item.error = item.error || String(error && error.message || error);
      } finally {
        await markItemParsedInHistory(item).catch(() => {});
        done += 1;
        setSummary(`正在补全发布时间 ${done}/${items.length}，成功 ${ok}，失败 ${failed}`);
        scheduleRender();
      }
    }
  }

  try {
    await Promise.all(Array.from({ length: workerCount }, worker));
  } finally {
    await closeHelperTab();
    backfillingPublishedTimes = false;
    endBusy("backfilling");
    setSummary(`发布时间补全完成：成功 ${ok}，失败 ${failed}。`);
    scheduleRender();
  }
}

function getPublishedBackfillItems() {
  if (!activeReport || !Array.isArray(activeReport.items)) return [];
  return activeReport.items.filter((item) => item && item.pid && !getPublishedSortValue(item));
}

function getObviousPreviewItems() {
  if (!activeReport || !Array.isArray(activeReport.items)) return [];
  return activeReport.items.filter((item) => (
    item
    && !item.ignored
    && item.status === "preview"
    && item.selectedManifestKind === "preview"
    && Number(item.seconds || 0) <= 45
  ));
}

async function setItemIgnored(item, ignored, reason = "manual") {
  if (!item || !item.pid) return false;
  item.ignored = Boolean(ignored);
  item.ignoredAt = ignored ? new Date().toISOString() : "";
  item.ignoreReason = ignored ? reason : "";
  item.ignoredBy = ignored ? "manual" : "";
  if (ignored) item.selected = false;
  await markItemParsedInHistory(item).catch(() => {});
  setSummary(ignored ? `已忽略 pid ${item.pid}。` : `已取消忽略 pid ${item.pid}。`);
  scheduleRender();
  return true;
}

async function ignoreObviousPreviewItems() {
  if (isBusy()) return;
  const items = getObviousPreviewItems();
  if (!items.length) {
    setSummary("没有可自动忽略的预览资源。");
    return;
  }
  beginBusy("ignoring");
  try {
    let done = 0;
    for (const item of items) {
      item.ignored = true;
      item.ignoredAt = new Date().toISOString();
      item.ignoreReason = "preview";
      item.ignoredBy = "auto";
      item.selected = false;
      await markItemParsedInHistory(item).catch(() => {});
      done += 1;
      setSummary(`正在忽略预览 ${done}/${items.length}`);
      scheduleRender();
    }
    setSummary(`已忽略 ${done} 条明显预览资源。`);
  } finally {
    endBusy("ignoring");
    scheduleRender();
  }
}

function handleResultChange(event) {
  const target = event.target;
  if (!target || !target.classList || !activeReport || !Array.isArray(activeReport.items)) return;

  if (target.classList.contains("resource-select")) {
    const item = getItemById(target.dataset.itemId);
    if (!item || !item.canDownload || item.ignored || isBusy()) return;
    item.selected = Boolean(target.checked);
    setSummary(makeParseSummary(activeReport));
    scheduleRender();
    return;
  }

  if (target.id === "result-status-filter") {
    resultViewState.statusFilter = target.value || "all";
    resultViewState.authorPage = 1;
    resultViewState.authorItemPages = {};
    forceNextResultRender = true;
    scheduleRender();
    return;
  }

  if (target.id === "result-sort-mode") {
    resultViewState.sortMode = target.value || "default";
    resultViewState.authorItemPages = {};
    forceNextResultRender = true;
    scheduleRender();
    return;
  }

  if (target.id === "author-page-size") {
    resultViewState.authorItemPageSize = clampInteger(target.value, 5, 100, DEFAULT_AUTHOR_ITEM_PAGE_SIZE);
    resultViewState.authorItemPages = {};
    forceNextResultRender = true;
    scheduleRender();
    return;
  }

  if (target.classList.contains("author-filter-check")) {
    if (target.value === "__all__") {
      resultViewState.selectedAuthorKeys = [];
    } else {
      const selected = new Set(resultViewState.selectedAuthorKeys || []);
      if (target.checked) selected.add(target.value);
      else selected.delete(target.value);
      resultViewState.selectedAuthorKeys = Array.from(selected);
    }
    resultViewState.authorPage = 1;
    resultViewState.authorItemPages = {};
    scheduleRender();
  }
}

function handleResultInput(event) {
  const target = event.target;
  if (!target || !target.classList || !activeReport || !Array.isArray(activeReport.items)) return;

  if (target.id === "result-global-search") {
    resultViewState.globalQuery = target.value || "";
    resultViewState.authorPage = 1;
    resultViewState.authorItemPages = {};
    forceNextResultRender = true;
    scheduleRender();
    return;
  }

  if (target.classList.contains("author-resource-search")) {
    const key = target.dataset.authorKey || "";
    resultViewState.authorQueries = resultViewState.authorQueries || {};
    resultViewState.authorQueries[key] = target.value || "";
    setAuthorItemPage(key, 1);
    forceNextResultRender = true;
    scheduleRender();
  }
}

async function handleResultClick(event) {
  const button = event.target && event.target.closest && event.target.closest("[data-action]");
  if (!button || isBusy() || !activeReport || !Array.isArray(activeReport.items)) return;
  const action = button.dataset.action;

  if (action === "estimate-selected-size") {
    await estimateSelectedResourceSizes();
    return;
  }

  if (action === "backfill-published-times") {
    await backfillMissingPublishedTimes();
    return;
  }

  if (action === "ignore-preview-items") {
    await ignoreObviousPreviewItems();
    return;
  }

  if (action === "ignore-item" || action === "unignore-item") {
    const item = getItemById(button.dataset.itemId);
    await setItemIgnored(item, action === "ignore-item", "manual");
    return;
  }

  if (action === "author-page-prev" || action === "author-page-next") {
    const groups = getFilteredAuthorGroups();
    const pageCount = getAuthorPageCount(groups.length);
    resultViewState.authorPage = clampInteger(
      action === "author-page-prev" ? resultViewState.authorPage - 1 : resultViewState.authorPage + 1,
      1,
      pageCount,
      1
    );
    scheduleRender();
    return;
  }

  if (action === "item-page-prev" || action === "item-page-next") {
    const key = button.dataset.authorKey || "";
    const groups = getFilteredAuthorGroups();
    const group = groups.find((item) => item.key === key);
    if (!group) return;
    const items = getGroupVisibleItems(group);
    const pageCount = Math.max(1, Math.ceil(items.length / resultViewState.authorItemPageSize));
    const current = getAuthorItemPage(key);
    setAuthorItemPage(key, action === "item-page-prev" ? current - 1 : current + 1, pageCount);
    scheduleRender();
    return;
  }

  if (["select-page", "clear-page", "select-author", "clear-author"].includes(action)) {
    applyAuthorSelectionAction(button.dataset.authorKey || "", action);
  }
}

function resetResultViewState() {
  resultViewState = {
    authorPage: 1,
    authorItemPageSize: resultViewState.authorItemPageSize || DEFAULT_AUTHOR_ITEM_PAGE_SIZE,
    statusFilter: "all",
    sortMode: resultViewState.sortMode || "default",
    globalQuery: "",
    selectedAuthorKeys: [],
    authorItemPages: {},
    authorQueries: {},
  };
  saveResultViewState();
}

function saveResultViewState() {
  try {
    localStorage.setItem(RESULT_VIEW_STATE_KEY, JSON.stringify(resultViewState));
  } catch {
    // View state is convenience-only.
  }
}

function restoreResultViewState() {
  try {
    const parsed = JSON.parse(localStorage.getItem(RESULT_VIEW_STATE_KEY) || "{}");
    if (!parsed || typeof parsed !== "object") return;
    resultViewState = {
      ...resultViewState,
      authorPage: clampInteger(parsed.authorPage, 1, 9999, 1),
      authorItemPageSize: clampInteger(parsed.authorItemPageSize, 5, 100, DEFAULT_AUTHOR_ITEM_PAGE_SIZE),
      statusFilter: String(parsed.statusFilter || resultViewState.statusFilter),
      sortMode: String(parsed.sortMode || resultViewState.sortMode),
      globalQuery: String(parsed.globalQuery || ""),
      selectedAuthorKeys: Array.isArray(parsed.selectedAuthorKeys) ? parsed.selectedAuthorKeys.map(String) : [],
      authorItemPages: parsed.authorItemPages && typeof parsed.authorItemPages === "object" ? parsed.authorItemPages : {},
      authorQueries: parsed.authorQueries && typeof parsed.authorQueries === "object" ? parsed.authorQueries : {},
    };
  } catch {
    // Ignore invalid view state.
  }
}

function applyAuthorSelectionAction(authorKey, action) {
  const group = getAuthorGroups().find((item) => item.key === authorKey);
  if (!group) return;

  const visibleItems = getGroupPageItems(group).filter((item) => item.canDownload && item.status !== "ok");
  const allItems = group.items.filter((item) => item.canDownload && item.status !== "ok");
  const targetItems = action === "select-page" || action === "clear-page" ? visibleItems : allItems;
  if (!targetItems.length) return;

  const nextSelected = action === "select-page" || action === "select-author";
  if (action === "select-author" || action === "clear-author") {
    const verb = nextSelected ? "勾选" : "取消勾选";
    const ok = window.confirm(`这会${verb}博主「${group.name}」下全部 ${targetItems.length} 条可下载资源，包含当前未显示页。确定继续？`);
    if (!ok) return;
  }

  for (const item of targetItems) {
    item.selected = nextSelected;
  }
  setSummary(makeParseSummary(activeReport));
  scheduleRender();
}

function getAuthorGroups() {
  const groups = new Map();
  for (const item of activeReport && activeReport.items || []) {
    const key = makeAuthorKey(item);
    let group = groups.get(key);
    if (!group) {
      group = {
        key,
        name: getItemAuthorName(item),
        uid: item.authorId || item.sourceUid || "",
        items: [],
      };
      groups.set(key, group);
    }
    group.items.push(item);
  }
  return Array.from(groups.values()).sort((a, b) => {
    const sourceCompare = String(a.uid || "").localeCompare(String(b.uid || ""), "zh-Hans-CN", { numeric: true });
    if (sourceCompare) return sourceCompare;
    return a.name.localeCompare(b.name, "zh-Hans-CN", { numeric: true });
  });
}

function getFilteredAuthorGroups() {
  const selected = new Set(resultViewState.selectedAuthorKeys || []);
  return getAuthorGroups()
    .filter((group) => !selected.size || selected.has(group.key))
    .map((group) => ({ ...group, visibleItems: getGroupVisibleItems(group) }))
    .filter((group) => group.visibleItems.length > 0);
}

function makeAuthorKey(item) {
  const id = item.authorId || item.sourceUid || "";
  if (id) return `id:${id}`;
  return `name:${getItemAuthorName(item)}`;
}

function getItemAuthorName(item) {
  return cleanTitle(item && (item.author || item.sourceTitle) || "") || "未知博主";
}

function getGroupVisibleItems(group) {
  return group.items
    .filter((item) => itemMatchesStatus(item) && itemMatchesGlobalSearch(item) && itemMatchesAuthorSearch(item, group.key))
    .sort(compareResourceItems);
}

function itemMatchesGlobalSearch(item) {
  return itemMatchesSearchQuery(item, resultViewState.globalQuery);
}

function itemMatchesAuthorSearch(item, authorKey) {
  const queries = resultViewState.authorQueries || {};
  return itemMatchesSearchQuery(item, queries[authorKey]);
}

function itemMatchesSearchQuery(item, query) {
  const terms = normalizeSearchTerms(query);
  if (!terms.length) return true;
  const haystack = makeSearchText(item);
  return terms.every((term) => haystack.includes(term));
}

function normalizeSearchTerms(query) {
  return normalizeSearchText(query).split(/\s+/).filter(Boolean);
}

function makeSearchText(item) {
  return normalizeSearchText([
    item && item.pid,
    item && item.title,
    item && item.author,
    item && item.authorId,
    item && item.sourceUid,
    item && item.sourceTitle,
    item && item.publishedAt,
    item && item.publishedDate,
    item && item.publishedSort,
    item && item.selectedManifestKind,
    item && item.outputFile,
    item && item.outputFolder,
    item && item.message,
    item && item.error,
  ].filter(Boolean).join(" "));
}

function normalizeSearchText(value) {
  return cleanTitle(String(value || "")).toLowerCase();
}

function compareResourceItems(a, b) {
  const sortMode = resultViewState.sortMode || "default";
  if (sortMode === "published_desc" || sortMode === "published_asc") {
    const aTime = getPublishedSortValue(a);
    const bTime = getPublishedSortValue(b);
    if (aTime && bTime && aTime !== bTime) {
      return sortMode === "published_asc" ? aTime.localeCompare(bTime) : bTime.localeCompare(aTime);
    }
    if (aTime && !bTime) return -1;
    if (!aTime && bTime) return 1;
  }

  return compareDefaultResourceItems(a, b);
}

function compareDefaultResourceItems(a, b) {
  const priority = (item) => {
    if (item.status === "ok") return 5;
    if (item.status === "excluded") return 4;
    if (item.status === "failed" || item.status === "stopped") return 3;
    if (item.status === "preview") return 2;
    if (item.canDownload) return 0;
    return 1;
  };
  const diff = priority(a) - priority(b);
  if (diff) return diff;
  const restoredDiff = Number(Boolean(a.restoredFromHistory)) - Number(Boolean(b.restoredFromHistory));
  if (restoredDiff) return restoredDiff;
  return Number(b.order || b.index || 0) - Number(a.order || a.index || 0);
}

function getPublishedSortValue(item) {
  const direct = String(item && item.publishedSort || "").trim();
  if (/^\d{8}-\d{6}$/.test(direct)) return direct;
  const normalized = normalizePublishedTime(item && (item.publishedAt || item.publishedDate || item.publishedAtRaw));
  return normalized.publishedSort || "";
}

function itemMatchesStatus(item) {
  const filter = resultViewState.statusFilter || "all";
  if (filter === "ignored") return Boolean(item.ignored);
  if (item.ignored) return false;
  if (filter === "all") return true;
  if (filter === "selected") return Boolean(item.selected);
  if (filter === "downloadable") return Boolean(item.canDownload);
  if (filter === "full") return item.selectedManifestKind === "full";
  if (filter === "preview") return item.status === "preview";
  if (filter === "failed") return item.status === "failed";
  if (filter === "excluded") return item.status === "excluded";
  if (filter === "downloaded") return item.status === "ok";
  return true;
}

function getAuthorPageCount(totalGroups) {
  return Math.max(1, Math.ceil(Number(totalGroups || 0) / AUTHORS_PER_PAGE));
}

function getAuthorItemPage(authorKey) {
  return Math.max(1, Number(resultViewState.authorItemPages[authorKey] || 1));
}

function setAuthorItemPage(authorKey, page, pageCount) {
  resultViewState.authorItemPages[authorKey] = Math.max(1, Math.min(pageCount || 1, Number(page) || 1));
}

function getGroupPageItems(group) {
  const visibleItems = getGroupVisibleItems(group);
  const pageSize = resultViewState.authorItemPageSize;
  const pageCount = Math.max(1, Math.ceil(visibleItems.length / pageSize));
  const page = Math.max(1, Math.min(pageCount, getAuthorItemPage(group.key)));
  resultViewState.authorItemPages[group.key] = page;
  return visibleItems.slice((page - 1) * pageSize, page * pageSize);
}

function getGroupStats(group) {
  const stats = {
    total: group.items.length,
    visible: getGroupVisibleItems(group).length,
    downloadable: 0,
    full: 0,
    preview: 0,
    selected: 0,
    excluded: 0,
    failed: 0,
    ok: 0,
  };
  for (const item of group.items) {
    if (item.ignored) continue;
    if (item.canDownload && item.status !== "ok") stats.downloadable += 1;
    if (item.selectedManifestKind === "full") stats.full += 1;
    if (item.status === "preview") stats.preview += 1;
    if (item.selected && item.canDownload && item.status !== "ok") stats.selected += 1;
    if (item.status === "excluded") stats.excluded += 1;
    if (item.status === "failed") stats.failed += 1;
    if (item.status === "ok") stats.ok += 1;
  }
  return stats;
}

function getPageStats(items) {
  const stats = { total: items.length, selected: 0, downloadable: 0 };
  for (const item of items) {
    if (item.ignored) continue;
    if (item.canDownload && item.status !== "ok") stats.downloadable += 1;
    if (item.selected && item.canDownload && item.status !== "ok") stats.selected += 1;
  }
  return stats;
}

function makeSelectedSizeSummary() {
  const selectedItems = getSelectedDownloadItems();
  const stats = {
    count: selectedItems.length,
    estimatedCount: 0,
    estimatedBytes: 0,
    partialBytes: 0,
    seconds: 0,
    segments: 0,
  };

  for (const item of selectedItems) {
    const estimated = Number(item.estimatedBytes || 0);
    if (estimated > 0) {
      stats.estimatedBytes += estimated;
      stats.estimatedCount += 1;
    }
    stats.partialBytes += Number(item.bytes || 0);
    stats.seconds += Number(item.seconds || 0);
    stats.segments += Number(item.segments || 0);
  }

  if (!stats.count) return { ...stats, text: "所选 0", title: "没有选中的可下载资源" };
  const sizeText = stats.estimatedCount
    ? `约 ${formatBytes(stats.estimatedBytes)}${stats.estimatedCount < stats.count ? ` (${stats.estimatedCount}/${stats.count})` : ""}`
    : stats.partialBytes
      ? `已下 ${formatBytes(stats.partialBytes)}`
      : "大小未估算";
  const text = `所选 ${stats.count} · ${sizeText} · ${formatDuration(stats.seconds)} · ${stats.segments} 片`;
  const title = stats.estimatedCount
    ? "大小来自抽样分片 Content-Length 估算，下载完成后会写入真实大小。"
    : "HLS 索引通常不带总大小，点击估算会抽样分片计算近似值。";
  return { ...stats, text, title };
}

function makeParseSummary(report) {
  const counts = countReportItems(report);
  if (!report || !report.items || !report.items.length) return "解析完成，没有可下载资源。";
  return `解析完成：完整 ${counts.full}，预览 ${counts.preview}，已选 ${counts.selected}，已下载 ${counts.ok}，忽略 ${counts.ignored}，排除 ${counts.excluded}，失败 ${counts.failed}`;
}

function countReportItems(report) {
  const counts = { full: 0, preview: 0, selected: 0, excluded: 0, failed: 0, ok: 0, skipped: 0, stopped: 0, ignored: 0, done: 0 };
  for (const item of (report && report.items) || []) {
    if (item.ignored) counts.ignored += 1;
    if (item.selectedManifestKind === "full") counts.full += 1;
    if (item.status === "preview") counts.preview += 1;
    if (item.selected && item.canDownload && item.status !== "ok") counts.selected += 1;
    if (item.status === "excluded") counts.excluded += 1;
    if (item.status === "failed") counts.failed += 1;
    if (item.status === "ok") counts.ok += 1;
    if (item.status === "skipped") counts.skipped += 1;
    if (item.status === "stopped") counts.stopped += 1;
    if (["parsed", "preview", "excluded", "failed", "ok", "skipped", "stopped"].includes(item.status)) counts.done += 1;
  }
  return counts;
}

function updateResultSummary(counts) {
  if (!activeReport) return;
  if (activeReport.stage === "downloading") {
    $("summary").textContent = `下载中：完成 ${counts.ok}，失败 ${counts.failed}，跳过 ${counts.skipped}，选中待处理 ${counts.selected}`;
  } else if (activeReport.stage === "parsed") {
    $("summary").textContent = makeParseSummary(activeReport);
  } else if (activeReport.stage === "downloaded" || activeReport.stage === "downloaded_with_errors") {
    const label = activeReport.stage === "downloaded_with_errors" ? "下载完成但有异常" : "下载完成";
    $("summary").textContent = `${label}：成功 ${counts.ok}，失败 ${counts.failed}，跳过 ${counts.skipped}`;
  } else {
    $("summary").textContent = `处理中 ${counts.done}/${activeReport.total}`;
  }
  updateFloatingConsole();
}

function renderDownloadProgressOnly() {
  if (!activeReport) return;
  const counts = countReportItems(activeReport);
  updateResultSummary(counts);

  const lines = document.querySelectorAll("#results .resource-line[data-item-id]");
  for (const line of lines) {
    const item = getItemById(line.dataset.itemId);
    if (!item) continue;
    updateResourceLineProgress(line, item);
  }
}

function updateResourceLineProgress(line, item) {
  line.className = `resource-line ${getItemClass(item)}`;
  const status = line.querySelector(".status-dot");
  if (status) status.textContent = statusLabel(item);
  const meta = line.querySelector(".resource-line-meta");
  if (meta) meta.textContent = makeResourceMetaText(item);

  let bar = line.querySelector(".mini-bar");
  if (item.status !== "running") {
    if (bar) bar.remove();
    return;
  }
  if (!bar) {
    bar = document.createElement("div");
    bar.className = "mini-bar";
    bar.appendChild(document.createElement("div"));
    const body = line.querySelector(".resource-line-body") || line;
    body.appendChild(bar);
  }
  const fill = bar.firstElementChild;
  if (fill) fill.style.width = `${clampPercent(item.progress)}%`;
}

function renderResults() {
  const container = $("results");
  if (!activeReport) {
    container.innerHTML = "";
    updateFloatingConsole();
    return;
  }

  container.innerHTML = "";
  const counts = countReportItems(activeReport);
  const allGroups = getAuthorGroups();
  const filteredGroups = getFilteredAuthorGroups();
  const pageCount = getAuthorPageCount(filteredGroups.length);
  resultViewState.authorPage = Math.max(1, Math.min(pageCount, Number(resultViewState.authorPage || 1)));
  const pageStart = (resultViewState.authorPage - 1) * AUTHORS_PER_PAGE;
  const pageGroups = filteredGroups.slice(pageStart, pageStart + AUTHORS_PER_PAGE);

  const importLine = makeImportSummary(activeReport.imports || []);
  if (importLine) {
    const summary = document.createElement("div");
    summary.className = "import-summary";
    summary.textContent = importLine;
    container.appendChild(summary);
  }

  if (activeReport.stage === "parsing") {
    const parsing = document.createElement("div");
    parsing.className = "parsing-summary";
    const runningItem = activeReport.items.find((item) => item.status === "running");
    parsing.innerHTML = `
      <div class="parsing-title">正在解析资源</div>
      <div class="parsing-meta">处理 ${Math.min(activeReport.total, counts.done + (runningItem ? 1 : 0))}/${activeReport.total} · 完整 ${counts.full} · 预览 ${counts.preview} · 已选 ${counts.selected} · 排除 ${counts.excluded} · 失败 ${counts.failed}</div>
      <div class="parsing-current">${escapeHtml(runningItem ? `pid ${runningItem.pid} · ${runningItem.message || "处理中"}` : "正在准备下一项")}</div>
    `;
    container.appendChild(parsing);
    $("summary").textContent = `处理中 ${Math.min(activeReport.total, counts.done + (runningItem ? 1 : 0))}/${activeReport.total}`;
  }

  const controls = document.createElement("div");
  controls.className = "result-controls";
  controls.innerHTML = renderResultControls(allGroups, filteredGroups.length, pageCount);
  container.appendChild(controls);

  const grid = document.createElement("div");
  grid.className = "author-grid";
  grid.style.setProperty("--author-count", String(Math.max(1, pageGroups.length)));
  for (const group of pageGroups) {
    grid.appendChild(renderAuthorColumn(group));
  }
  if (!pageGroups.length) {
    const empty = document.createElement("div");
    empty.className = "empty-state";
    empty.textContent = "当前筛选下没有资源。";
    grid.appendChild(empty);
  }
  container.appendChild(grid);

  updateResultSummary(counts);
}

function renderResultControls(allGroups, filteredCount, pageCount) {
  const selected = new Set(resultViewState.selectedAuthorKeys || []);
  const selectedSize = makeSelectedSizeSummary();
  const missingTimeCount = getPublishedBackfillItems().length;
  const obviousPreviewCount = getObviousPreviewItems().length;
  const authorSummary = selected.size ? `已选 ${selected.size}/${allGroups.length} 位博主` : `全部 ${allGroups.length} 位博主`;
  const authorChecks = [
    `<label><input class="author-filter-check" type="checkbox" value="__all__" ${selected.size ? "" : "checked"}> 全部博主</label>`,
    ...allGroups.map((group) => {
      const stats = getGroupStats(group);
      const checked = selected.has(group.key) ? "checked" : "";
      return `<label><input class="author-filter-check" type="checkbox" value="${escapeHtml(group.key)}" ${checked}> ${escapeHtml(group.name)} <span>${stats.selected}/${stats.downloadable}</span></label>`;
    }),
  ].join("");

  return `
    <div class="result-filter-row">
      <details class="author-filter">
        <summary>${escapeHtml(authorSummary)}</summary>
        <div class="author-filter-menu">${authorChecks}</div>
      </details>
      <label class="inline-field">状态
        <select id="result-status-filter">
          ${renderOption("all", "全部状态", resultViewState.statusFilter)}
          ${renderOption("full", "完整", resultViewState.statusFilter)}
          ${renderOption("preview", "预览", resultViewState.statusFilter)}
          ${renderOption("selected", "已勾选", resultViewState.statusFilter)}
          ${renderOption("downloadable", "可下载", resultViewState.statusFilter)}
          ${renderOption("downloaded", "已下载", resultViewState.statusFilter)}
          ${renderOption("ignored", "已忽略", resultViewState.statusFilter)}
          ${renderOption("failed", "失败", resultViewState.statusFilter)}
          ${renderOption("excluded", "已排除", resultViewState.statusFilter)}
        </select>
      </label>
      <label class="inline-field sort-field">排序
        <select id="result-sort-mode">
          ${renderOption("default", "默认", resultViewState.sortMode)}
          ${renderOption("published_desc", "发布新→旧", resultViewState.sortMode)}
          ${renderOption("published_asc", "发布旧→新", resultViewState.sortMode)}
        </select>
      </label>
      <button class="result-small-action" data-action="backfill-published-times" ${backfillingPublishedTimes || !missingTimeCount ? "disabled" : ""} title="读取帖子详情接口，给旧本地记录补全发布时间">
        ${backfillingPublishedTimes ? "补时间中" : `补时间${missingTimeCount ? ` ${missingTimeCount}` : ""}`}
      </button>
      <button class="result-small-action" data-action="ignore-preview-items" ${isBusy() || !obviousPreviewCount ? "disabled" : ""} title="忽略 45 秒以内的 preview 资源，可在已忽略筛选中取消">
        忽略预览${obviousPreviewCount ? ` ${obviousPreviewCount}` : ""}
      </button>
      <label class="inline-field">每位博主显示
        <select id="author-page-size">
          ${renderOption("10", "10 条", resultViewState.authorItemPageSize)}
          ${renderOption("20", "20 条", resultViewState.authorItemPageSize)}
          ${renderOption("50", "50 条", resultViewState.authorItemPageSize)}
          ${renderOption("100", "100 条", resultViewState.authorItemPageSize)}
        </select>
      </label>
      <label class="inline-field search-field">搜索
        <input id="result-global-search" type="search" placeholder="pid / 标题 / 作者" value="${escapeHtml(resultViewState.globalQuery || "")}">
      </label>
      <div class="selection-size" title="${escapeHtml(selectedSize.title)}">
        <span>${escapeHtml(selectedSize.text)}</span>
        <button data-action="estimate-selected-size" ${estimatingSelectedSize || !selectedSize.count ? "disabled" : ""}>${estimatingSelectedSize ? "估算中" : "估算"}</button>
      </div>
      <div class="author-pager">
        <button data-action="author-page-prev" ${resultViewState.authorPage <= 1 ? "disabled" : ""}>上一页</button>
        <span>博主 ${filteredCount ? resultViewState.authorPage : 0}/${filteredCount ? pageCount : 0}，每页最多 ${AUTHORS_PER_PAGE} 位</span>
        <button data-action="author-page-next" ${resultViewState.authorPage >= pageCount ? "disabled" : ""}>下一页</button>
      </div>
    </div>
  `;
}

function renderOption(value, label, selectedValue) {
  return `<option value="${escapeHtml(value)}" ${String(value) === String(selectedValue) ? "selected" : ""}>${escapeHtml(label)}</option>`;
}

function renderAuthorColumn(group) {
  const stats = getGroupStats(group);
  const visibleItems = getGroupVisibleItems(group);
  const pageSize = resultViewState.authorItemPageSize;
  const pageCount = Math.max(1, Math.ceil(visibleItems.length / pageSize));
  const page = Math.max(1, Math.min(pageCount, getAuthorItemPage(group.key)));
  resultViewState.authorItemPages[group.key] = page;
  const pageItems = visibleItems.slice((page - 1) * pageSize, page * pageSize);
  const pageStats = getPageStats(pageItems);
  const authorQuery = resultViewState.authorQueries && resultViewState.authorQueries[group.key] || "";

  const column = document.createElement("section");
  column.className = "author-column";
  column.innerHTML = `
    <div class="author-column-head">
      <div class="author-title-row">
        <div class="author-name" title="${escapeHtml(group.name)}">${escapeHtml(group.name)}</div>
        <input class="author-resource-search" type="search" data-author-key="${escapeHtml(group.key)}" placeholder="搜本组" value="${escapeHtml(authorQuery)}" title="只搜索该博主的 pid、标题、文件名">
      </div>
      <div class="author-meta">${group.uid ? `uid ${escapeHtml(group.uid)} · ` : ""}已选 ${stats.selected}/${stats.downloadable}</div>
      <div class="author-meta">完整 ${stats.full} · 预览 ${stats.preview} · 已下载 ${stats.ok} · 排除 ${stats.excluded} · 失败 ${stats.failed}</div>
      <div class="author-actions">
        <button data-action="select-page" data-author-key="${escapeHtml(group.key)}">选当前页</button>
        <button data-action="clear-page" data-author-key="${escapeHtml(group.key)}">取消当前页</button>
        <button data-action="select-author" data-author-key="${escapeHtml(group.key)}">全选该博主</button>
        <button data-action="clear-author" data-author-key="${escapeHtml(group.key)}">取消该博主</button>
      </div>
      <div class="author-page-row">
        <button data-action="item-page-prev" data-author-key="${escapeHtml(group.key)}" ${page <= 1 ? "disabled" : ""}>‹</button>
        <span>资源 ${page}/${pageCount} · 当前页 ${pageStats.selected}/${pageStats.downloadable}</span>
        <button data-action="item-page-next" data-author-key="${escapeHtml(group.key)}" ${page >= pageCount ? "disabled" : ""}>›</button>
      </div>
    </div>
    <div class="author-items">
      ${pageItems.length ? pageItems.map(renderResourceLine).join("") : `<div class="empty-state small">当前筛选下没有资源</div>`}
    </div>
  `;
  return column;
}

function renderResourceLine(item) {
  const disabled = !item.canDownload || isBusy() || item.status === "ok" || item.ignored ? "disabled" : "";
  const checked = item.selected ? "checked" : "";
  const progress = item.status === "running" ? `<div class="mini-bar"><div style="width:${clampPercent(item.progress)}%"></div></div>` : "";
  const ignoreAction = item.ignored
    ? `<button class="resource-action" data-action="unignore-item" data-item-id="${escapeHtml(item.id || "")}">取消忽略</button>`
    : `<button class="resource-action" data-action="ignore-item" data-item-id="${escapeHtml(item.id || "")}">忽略</button>`;
  return `
    <div class="resource-line ${getItemClass(item)}" data-item-id="${escapeHtml(item.id || "")}">
      <label class="resource-line-check">
        <input class="resource-select" type="checkbox" data-item-id="${escapeHtml(item.id || "")}" ${checked} ${disabled}>
      </label>
      <div class="resource-line-body">
        <div class="resource-line-top">
          <span class="status-dot">${escapeHtml(statusLabel(item))}</span>
          <span class="pid">pid ${escapeHtml(item.pid)}</span>
          ${ignoreAction}
        </div>
        <div class="resource-title" title="${escapeHtml(item.title || item.sourceTitle || "")}">${escapeHtml(item.title || item.sourceTitle || `pid ${item.pid}`)}</div>
        <div class="resource-line-meta">${escapeHtml(makeResourceMetaText(item))}</div>
        ${progress}
      </div>
    </div>
  `;
}

function makeResourceMetaText(item) {
  const published = formatItemPublished(item);
  const size = formatItemSize(item);
  return `${published ? `发布 ${published} · ` : ""}${item.selectedManifestKind || "-"} · ${item.seconds || 0}s · ${item.segments || 0} 片${size ? ` · ${size}` : ""}`;
}

function formatItemPublished(item) {
  return item && (item.publishedAt || item.publishedDate || "") || "";
}

function formatItemSize(item) {
  const bytes = Number(item && item.bytes || 0);
  if (bytes > 0 && item.status === "ok") return formatBytes(bytes);
  const estimated = Number(item && item.estimatedBytes || 0);
  if (estimated > 0) return `约 ${formatBytes(estimated)}`;
  if (bytes > 0) return `已下 ${formatBytes(bytes)}`;
  return "";
}

function makeImportSummary(imports) {
  if (!imports.length) return "";
  return imports.map((item) => `sell uid ${item.uid}：扫描 ${item.scannedPages}/${item.pageCount || "?"} 页，帖子 ${item.scannedTopics}/${item.total || "?"}，导入 ${item.included}，历史恢复 ${item.restoredFromHistory || 0}，排除 ${item.excludedNoVideo}，重复 ${item.duplicate}`).join("；");
}

function getItemClass(item) {
  if (item.ignored) return "ignored";
  if (item.status === "ok") return "ok";
  if (item.status === "failed" || item.status === "stopped") return "fail";
  if (item.status === "excluded") return "muted-item";
  if (item.localDownloadStatus === "new_missing") return "new-item";
  if (item.status === "preview") return "preview";
  if (item.status === "parsed") return "ready";
  return "";
}

function statusLabel(itemOrStatus) {
  const item = itemOrStatus && typeof itemOrStatus === "object" ? itemOrStatus : null;
  const status = item ? item.status : itemOrStatus;
  if (item && item.ignored) return "已忽略";
  if (item && status === "ok") return "已下载";
  if (item && ["pending", "parsed", "preview"].includes(status)) {
    if (item.localDownloadStatus === "new_missing") return "新-未下载";
    if (item.localDownloadStatus === "missing" || item.canDownload) return "未下载";
  }
  return ({
    pending: "待解析",
    running: "处理中",
    parsed: "完整",
    preview: "预览",
    excluded: "排除",
    failed: "失败",
    skipped: "跳过",
    stopped: "停止",
    ok: "已下载",
  })[status] || status || "-";
}

function updateFloatingButtons() {
  const busy = isBusy();
  setDisabled("parse", busy);
  setDisabled("start", busy);
  setDisabled("stop", !running);
  setDisabled("export-report", !activeReport || busy);
  updateParsedSourcesToggle();
  setDisabled("float-parse", busy);
  setDisabled("float-start", busy);
  setDisabled("float-stop", !running);
  setDisabled("float-export", !activeReport || busy);
}

function setDisabled(id, value) {
  const element = $(id);
  if (element) element.disabled = Boolean(value);
}

function updateFloatingConsole(summaryText) {
  $("float-login").textContent = loginState.text;
  $("float-root").textContent = rootHandle ? rootHandle.name : "未选择";
  $("float-state").textContent = busyMode ? busyModeLabel(busyMode) : running ? "运行中" : "空闲";
  updateFloatingButtons();

  let currentText = summaryText || $("summary").textContent || "等待任务";
  let progress = 0;
  if (activeReport && activeReport.items) {
    const runningItem = activeReport.items.find((item) => item.status === "running");
    if (runningItem) {
      currentText = `pid ${runningItem.pid} · ${runningItem.message || "运行中"}`;
      progress = runningItem.progress || 0;
    } else {
      const counts = countReportItems(activeReport);
      progress = activeReport.total ? Math.round((counts.done / activeReport.total) * 100) : 0;
    }
  }
  $("float-current").textContent = currentText;
  $("float-progress-fill").style.width = `${clampPercent(progress)}%`;
}

function openDb() {
  return new Promise((resolve, reject) => {
    const request = indexedDB.open(DB_NAME, DB_VERSION);
    request.onupgradeneeded = () => {
      request.result.createObjectStore("handles");
    };
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
}

async function saveRootHandle(handle) {
  const db = await openDb();
  await idbRequest(db.transaction("handles", "readwrite").objectStore("handles").put(handle, ROOT_KEY));
  db.close();
}

async function loadRootHandle() {
  try {
    const db = await openDb();
    const handle = await idbRequest(db.transaction("handles", "readonly").objectStore("handles").get(ROOT_KEY));
    db.close();
    return handle || null;
  } catch {
    return null;
  }
}

function idbRequest(request) {
  return new Promise((resolve, reject) => {
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
}

async function hasDirectoryPermission(handle) {
  if (!handle || !handle.queryPermission) return false;
  return (await handle.queryPermission({ mode: "readwrite" })) === "granted";
}

async function ensureDirectoryPermission(handle) {
  if (!handle) return false;
  if ((await handle.queryPermission({ mode: "readwrite" })) === "granted") return true;
  return (await handle.requestPermission({ mode: "readwrite" })) === "granted";
}

function formatBytes(bytes) {
  const value = Number(bytes || 0);
  if (value < 1024) return `${value} B`;
  if (value < 1024 * 1024) return `${(value / 1024).toFixed(1)} KB`;
  if (value < 1024 * 1024 * 1024) return `${(value / 1024 / 1024).toFixed(1)} MB`;
  return `${(value / 1024 / 1024 / 1024).toFixed(2)} GB`;
}

function formatDuration(seconds) {
  let value = Math.max(0, Math.round(Number(seconds || 0)));
  const hours = Math.floor(value / 3600);
  value -= hours * 3600;
  const minutes = Math.floor(value / 60);
  const rest = value - minutes * 60;
  if (hours) return `${hours}h${String(minutes).padStart(2, "0")}m`;
  if (minutes) return `${minutes}m${String(rest).padStart(2, "0")}s`;
  return `${rest}s`;
}

function formatSpeed(bytes, startedAt) {
  const seconds = Math.max(0.1, (Date.now() - Number(startedAt || Date.now())) / 1000);
  return `${formatBytes(Number(bytes || 0) / seconds)}/s`;
}

function clampPercent(value) {
  const number = Number(value || 0);
  return Math.max(0, Math.min(100, Math.round(number)));
}

function clampInteger(value, min, max, fallback) {
  const number = Number(value);
  if (!Number.isFinite(number)) return fallback;
  return Math.max(min, Math.min(max, Math.floor(number)));
}

function escapeHtml(value) {
  return String(value == null ? "" : value).replace(/[&<>"']/g, (ch) => ({
    "&": "&amp;",
    "<": "&lt;",
    ">": "&gt;",
    "\"": "&quot;",
    "'": "&#39;",
  }[ch]));
}

function escapeRegExp(value) {
  return String(value || "").replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function sleep(ms) {
  const delay = Math.max(0, Number(ms) || 0);
  const signal = activeStopController && activeStopController.signal;
  return new Promise((resolve) => {
    if (signal && signal.aborted) {
      resolve();
      return;
    }

    const timer = window.setTimeout(done, delay);
    function done() {
      if (signal) signal.removeEventListener("abort", onAbort);
      resolve();
    }
    function onAbort() {
      window.clearTimeout(timer);
      done();
    }
    if (signal) signal.addEventListener("abort", onAbort, { once: true });
  });
}
