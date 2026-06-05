"use strict";

const LOGIN_ASSIST_DEFAULT_TTL_MS = 120000;
const LOGIN_ASSIST_STORAGE_KEY = "hjbd_login_assist_until";
let loginAssist = {
  until: 0,
  observer: null,
  timer: null,
  clicked: new WeakSet(),
  clickCount: 0,
};

chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  if (!message) return false;

  if (message.type === "HJBD_PING") {
    sendResponse({ ok: true });
    return false;
  }

  if (message.type === "HJBD_PAGE_FETCH") {
    handlePageFetch(message).then((data) => {
      sendResponse({ ok: true, data });
    }).catch((error) => {
      sendResponse({ ok: false, error: String(error && error.message || error) });
    });
    return true;
  }

  if (message.type === "HJBD_LOGIN_ASSIST_START") {
    try {
      const data = startLoginAssist(message.ttlMs);
      sendResponse({ ok: true, data });
    } catch (error) {
      sendResponse({ ok: false, error: String(error && error.message || error) });
    }
    return true;
  }

  return false;
});

function startLoginAssist(ttlMs) {
  const ttl = Math.max(10000, Math.min(Number(ttlMs) || LOGIN_ASSIST_DEFAULT_TTL_MS, 300000));
  loginAssist.until = Date.now() + ttl;
  saveLoginAssistUntil(loginAssist.until);
  loginAssist.clicked = new WeakSet();
  loginAssist.clickCount = 0;

  ensureLoginAssistObserver();
  scanLoginPrompts();

  return {
    until: new Date(loginAssist.until).toISOString(),
    ttlMs: ttl,
    clicked: loginAssist.clickCount,
  };
}

function ensureLoginAssistObserver() {
  if (!loginAssist.observer) {
    loginAssist.observer = new MutationObserver(() => {
      if (!isLoginAssistActive()) {
        stopLoginAssist();
        return;
      }
      window.setTimeout(scanLoginPrompts, 80);
    });
  }

  const root = document.documentElement || document.body;
  if (root) {
    try {
      loginAssist.observer.observe(root, {
        childList: true,
        subtree: true,
        attributes: true,
        attributeFilter: ["class", "style", "disabled", "aria-disabled"],
      });
    } catch {
      // The observer may already be attached to this document.
    }
  }

  if (!loginAssist.timer) {
    loginAssist.timer = window.setInterval(() => {
      if (!isLoginAssistActive()) {
        stopLoginAssist();
        return;
      }
      scanLoginPrompts();
    }, 500);
  }
}

function stopLoginAssist() {
  loginAssist.until = 0;
  saveLoginAssistUntil(0);
  if (loginAssist.observer) {
    loginAssist.observer.disconnect();
    loginAssist.observer = null;
  }
  if (loginAssist.timer) {
    window.clearInterval(loginAssist.timer);
    loginAssist.timer = null;
  }
}

function isLoginAssistActive() {
  return Date.now() < loginAssist.until;
}

function scanLoginPrompts() {
  if (!isLoginAssistActive()) return;

  const nodes = document.querySelectorAll("button, [role='button'], a, .btn, .button, .van-button, .el-button, [onclick]");
  for (const node of nodes) {
    const text = normalizeButtonText(node.textContent);
    const target = getClickableTarget(node);
    if (!target || loginAssist.clicked.has(target)) continue;
    if (!isVisible(target) || !isEnabled(target)) continue;

    if (shouldClickLoginPrompt(text)) {
      if (!isLoginPromptCandidate(node, target, text)) continue;
      clickOnce(target);
      continue;
    }

    if (shouldClickLoginAction(text, target)) {
      clickOnce(target);
    }
  }
}

function normalizeButtonText(value) {
  return String(value || "")
    .replace(/\s+/g, "")
    .replace(/[：:]+$/g, "")
    .trim();
}

function shouldClickLoginPrompt(text) {
  if (!text || text.length > 8) return false;
  if (text === "我知道了") return true;
  if (text === "我在想想" || text === "我再想想") return true;
  if (text === "好") return true;

  const countdown = text.match(/^好[（(](\d+)[）)]$/);
  if (!countdown) return false;
  return Number(countdown[1]) <= 0;
}

function shouldClickLoginAction(text, target) {
  if (text !== "登录") return false;
  if (isFilledLoginSubmit(target)) return true;
  return isLoginEntryPage() && isHomeLoginEntry(target);
}

function isLoginEntryPage() {
  const path = window.location && window.location.pathname || "";
  return /\/(?:home|login|signin|user)(?:\/|$)/i.test(path);
}

function isHomeLoginEntry(target) {
  if (hasVisiblePasswordInput()) return false;
  if (findPromptContext(target)) return true;
  const rect = target.getBoundingClientRect();
  return rect.top >= 0 && rect.top < 180 && rect.width <= 120 && rect.height <= 60;
}

function isFilledLoginSubmit(target) {
  const context = findLoginContext(target);
  if (!context) return false;

  const inputs = Array.from(context.querySelectorAll("input")).filter(isVisible);
  const password = inputs.find((input) => input.type === "password");
  const account = inputs.find((input) => input !== password && /^(text|tel|number|email|search|)$/i.test(input.type || "text"));
  return Boolean(account && account.value.trim() && password && password.value);
}

function findLoginContext(target) {
  let node = target;
  for (let depth = 0; node && depth < 8; depth += 1, node = node.parentElement) {
    if (node.querySelectorAll && node.querySelectorAll("input").length >= 2) return node;
  }
  return null;
}

function hasVisiblePasswordInput() {
  return Array.from(document.querySelectorAll("input[type='password']")).some(isVisible);
}

function getClickableTarget(node) {
  if (!node || node.nodeType !== Node.ELEMENT_NODE) return null;
  return node.closest("button, [role='button'], a, .van-button, .el-button, .btn, .button") || node;
}

function isLoginPromptCandidate(node, target, text) {
  if (!node || !target) return false;
  const buttonSelector = "button, [role='button'], a, .van-button, .el-button, .btn, .button";
  const context = findPromptContext(target);
  if (!context) return false;

  const contextText = normalizeButtonText(context.innerText || context.textContent || "");
  if (!hasLoginAssistPromptContext(contextText)) return false;

  if (text === "好") {
    return /好[（(]\d+[）)]/.test(contextText)
      || /登录|注册|VIP|会员|权限|购买|跳过|我在想想|我再想想|我知道了/.test(contextText);
  }

  if (node.matches(buttonSelector) || target.matches(buttonSelector)) return true;

  const style = window.getComputedStyle(target);
  return style.cursor === "pointer";
}

function findPromptContext(target) {
  let node = target;
  for (let depth = 0; node && depth < 8; depth += 1, node = node.parentElement) {
    if (node.matches && node.matches(".el-dialog, .el-message-box, .van-dialog, .van-popup, [role='dialog'], [class*='modal'], [class*='popup'], [class*='dialog']")) {
      return isVisible(node) ? node : null;
    }
  }
  return null;
}

function hasLoginAssistPromptContext(text) {
  return /登录|注册|VIP|会员|权限|购买|开通|试看|跳过|我在想想|我再想想|我知道了|请先登录|未登录/.test(String(text || ""));
}

function isVisible(element) {
  if (!element || !element.isConnected) return false;
  const rect = element.getBoundingClientRect();
  if (rect.width < 4 || rect.height < 4) return false;
  const style = window.getComputedStyle(element);
  return style.display !== "none" && style.visibility !== "hidden" && Number(style.opacity || 1) > 0;
}

function isEnabled(element) {
  if (!element) return false;
  if (element.disabled) return false;
  if (element.getAttribute("aria-disabled") === "true") return false;
  if (element.classList && (element.classList.contains("disabled") || element.classList.contains("is-disabled"))) return false;
  const style = window.getComputedStyle(element);
  return style.pointerEvents !== "none";
}

function clickElement(element) {
  if (typeof element.click === "function") {
    element.click();
    return;
  }
  element.dispatchEvent(new MouseEvent("click", { bubbles: true, cancelable: true, view: window }));
}

function clickOnce(target) {
  loginAssist.clicked.add(target);
  loginAssist.clickCount += 1;
  clickElement(target);
}

function saveLoginAssistUntil(value) {
  try {
    if (value && value > Date.now()) {
      sessionStorage.setItem(LOGIN_ASSIST_STORAGE_KEY, String(value));
    } else {
      sessionStorage.removeItem(LOGIN_ASSIST_STORAGE_KEY);
    }
  } catch {
    // sessionStorage can be unavailable in unusual browser modes.
  }
}

function resumeLoginAssistFromStorage() {
  try {
    const until = Number(sessionStorage.getItem(LOGIN_ASSIST_STORAGE_KEY) || 0);
    if (!Number.isFinite(until) || until <= Date.now()) return;
    loginAssist.until = until;
    ensureLoginAssistObserver();
    window.setTimeout(scanLoginPrompts, 300);
  } catch {
    // ignore
  }
}

async function handlePageFetch(message) {
  if (message.kind === "topic") {
    return fetchDecodedJson(`/api/topic/${encodeURIComponent(message.pid)}`, {
      method: "GET",
      credentials: "include",
      headers: { accept: "application/json, text/plain, */*" },
    });
  }
  if (message.kind === "attachment") {
    return fetchDecodedJson("/api/attachment", {
      method: "POST",
      credentials: "include",
      headers: {
        "content-type": "application/json",
        accept: "application/json, text/plain, */*",
      },
      body: JSON.stringify({
        id: Number(message.attachmentId),
        resource_id: Number(message.pid),
        resource_type: "topic",
        line: "",
      }),
    });
  }
  if (message.kind === "sellTopics") {
    const page = Math.max(1, Number(message.page) || 1);
    const uid = String(message.uid || "").replace(/\D+/g, "");
    const type = Number(message.listType || message.type || 5) || 5;
    if (!uid) throw new Error("missing sell page uid");
    return fetchDecodedJson(`/api/topic/node/topics?page=${encodeURIComponent(page)}&userId=${encodeURIComponent(uid)}&type=${encodeURIComponent(type)}`, {
      method: "GET",
      credentials: "include",
      headers: { accept: "application/json, text/plain, */*" },
    });
  }
  if (message.kind === "userInfo") {
    const uid = String(message.uid || "").replace(/\D+/g, "");
    if (!uid) throw new Error("missing user info uid");
    return fetchDecodedJson(`/api/user/info/${encodeURIComponent(uid)}`, {
      method: "GET",
      credentials: "include",
      headers: { accept: "application/json, text/plain, */*" },
    });
  }
  throw new Error(`unknown page fetch kind: ${message.kind}`);
}

async function fetchDecodedJson(url, options) {
  const response = await fetch(url, options);
  const text = await response.text();
  if (!response.ok) throw new Error(`${url} HTTP ${response.status}`);
  return decodeResponse(text, url);
}

function decodeResponse(text, url = "") {
  let parsed;
  try {
    parsed = JSON.parse(text);
  } catch (error) {
    throw new Error(`接口响应不是 JSON：${url || "unknown url"}；长度 ${String(text || "").length}；开头 ${previewText(text)}；${String(error && error.message || error)}`);
  }
  if (parsed && typeof parsed.data === "string") {
    try {
      return tripleBase64Json(parsed.data);
    } catch (error) {
      throw new Error(`接口 data 解码失败：${url || "unknown url"}；data 长度 ${parsed.data.length}；${String(error && error.message || error)}`);
    }
  }
  return parsed && Object.prototype.hasOwnProperty.call(parsed, "data") ? parsed.data : parsed;
}

function tripleBase64Json(text) {
  let value = String(text || "").trim();
  for (let index = 0; index < 3; index += 1) {
    try {
      value = decodeBase64(value, index === 2);
    } catch (error) {
      throw new Error(`第 ${index + 1} 层 base64 解码失败；输入长度 ${value.length}；开头 ${previewText(value)}；${String(error && error.message || error)}`);
    }
  }
  try {
    return JSON.parse(value);
  } catch (error) {
    throw new Error(`base64 解码完成但不是 JSON；最终长度 ${value.length}；开头 ${previewText(value)}；${String(error && error.message || error)}`);
  }
}

function decodeBase64(value, utf8) {
  const binary = atob(value);
  if (!utf8) return binary;
  const bytes = new Uint8Array(binary.length);
  for (let index = 0; index < binary.length; index += 1) bytes[index] = binary.charCodeAt(index);
  return new TextDecoder("utf-8").decode(bytes);
}

function previewText(value) {
  return JSON.stringify(String(value || "").slice(0, 80));
}

resumeLoginAssistFromStorage();
