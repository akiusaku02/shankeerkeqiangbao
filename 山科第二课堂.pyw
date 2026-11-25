# -*- coding: utf-8 -*-
"""
山科二课抢报脚本 v0.2.6
本版修复（蹲守误报名 / 登录失效刷屏 / stored_authorization 不复用）：

【令牌复用与凭证】
1. 【复用不再自毁】复用分支 save_cred(store_stable_auth=False) 原会把手里的 stored_authorization 覆盖成空串，
   等于复用一次就废掉持久令牌。现改为只刷新 Cookie，持久令牌原样保留。
2. 【load_cred 解耦】stored_authorization 独立读取，不再受 Authorization/Cookie/VPN_BASE 任一为空的影响。
3. 【失败来源分流】VPN 票据失效（返回 HTML / 401 / 403）只当“票据问题”，刷新 Cookie 即可，不再计入 token 失败次数；
   只有业务返回 code:10001（登录失效）才计一次真实失效，连续 3 次才清空持久令牌。
4. 【本地过期预判】Authorization 若为 JWT 且 exp 已过期，直接跳过复用走完整抓取；无 exp 的 token 视为可长期复用。
5. 【指纹与时间】日志打印 token 指纹（前10…后6），cred.json 记录 stored_at（保存时间）与 last_ok_at（最近一次接口成功时间），
   方便判断“是不是同一个 token”“存了多久”“最近还能不能用”。
6. 【路径固定】cred.json / task.json 固定为脚本所在目录，避免不同工作目录读到两份凭证。

【蹲守】
7. 名额判定改用活动列表快照（详情接口不返回 peopleLimit / enrollCount，旧写法恒为 0 导致满额活动每轮误判“释放名额”）；
   连续两轮确认才报名；字段缺失、isAbleEnroll=0、快照超 30s 未更新时一律不判定。

【登录失效】
8. 报名/详情接口返回 10001 时置位 relogin_event，由后台主循环统一重登一次并刷新 HEADERS，不再每 0.8s 空转刷屏。

【失败退避】
9. 蹲守报名失败后退避再判；普通抢报遇登录失效不消耗 SIGN_MAX_RETRY。
保留 v0.2.5 的修复：筛选后序号映射、序号从1开始、弹窗导入、GUI 轮询健壮性
"""
import requests
import time
import logging
import datetime
import json
import threading
import os
import random
import sys
from email.utils import parsedate_to_datetime
from urllib.parse import urlparse, quote
from collections import deque
from queue import Queue, Empty
# ===================== 配置 =====================
MAX_LOG_ITEMS = 150        # 日志最大行数
LOG_POLL_INTERVAL = 120    # 日志刷新间隔(ms)
# ★ 凭证/任务文件固定在“脚本所在目录”，避免双击启动器与其他方式运行时 CWD 不同导致读到两份文件
BASE_DIR = os.path.dirname(os.path.abspath(__file__)) if "__file__" in globals() else os.getcwd()
CRED_FILE = os.path.join(BASE_DIR, "cred.json")
TASK_FILE = os.path.join(BASE_DIR, "task.json")
TASK_TMP = os.path.join(BASE_DIR, "task.tmp.json")
FETCH_DAY_MAX = 30       # ✅抓取天数最大上限，在此修改
FETCH_DAY_DEFAULT = 7     # ✅默认抓取天数
empty_count = 0
max_empty = 8
LOOP_SLEEP = 4
SPRINT_SLEEP = 0.18
SPRINT_ADVANCE_MS = 450
SIGN_MAX_RETRY = 15
WATCHDOG_MAX_RETRY = 1200   # 蹲守模式最大循环次数
WATCHDOG_INTERVAL = 0.8     # 蹲守轮询间隔秒
SNAPSHOT_STALE_SEC = 30     # 活动列表快照超过该秒数视为过期，蹲守不做名额判定（避免用旧数据误报）
CACHE_TTL = 60
MAX_DETAIL_CACHE = 200
QUIET_COUNTDOWN = True      # 默认开启长倒计时静默
COUNTDOWN_ALERT_SEC = 30    # 剩余小于这个秒数才开始打印倒计时
MAX_WORKER = 6
VPN_QUERY_PARAM = "vpn-12-o2-ekta.sdust.edu.cn"
FILTER_FULL = False         # False：人满活动不隐藏，界面展示
FILTER_LIMIT_COLLEGE = False
BASE_BACKOFF = 0.15
MAX_BACKOFF = 2.0
ERKE_VPN_BASE = ""
STABLE_AUTH_MAX_CONTINUE_FAIL = 3  # 连续复用旧Authorization“验证失败”次数，到达后清空持久缓存
relogin_stable_auth_fail_count = 0 # 全局：复用token已被业务接口确认失效(10001)的次数，不含VPN票据失效
reused_stable_auth = False         # 当前运行的 Authorization 是否来自持久化复用（用于判定失败归属）
vpn_ticket_fail_count = 0          # 全局：VPN 票据失效次数（只提示，不清持久token）
last_ok_at_ms = 0                  # 全局：最近一次接口业务成功(code=0)的时间戳(ms)
_last_ok_persist_ts = 0.0          # 全局：last_ok_at 最近一次落盘时间，避免频繁写文件
DETAIL_RETRY = 2                   # 获取详情接口最大重试次数
TASK_SAVE_INTERVAL = 5             # 后台循环多少次自动保存一次任务到磁盘
# 窗口位置大小配置
LOG_W, LOG_H =300, 520
LOG_X, LOG_Y = 10, 40
LOG_TOPMOST = False
ACT_W, ACT_H = 1000, 720
ACT_X, ACT_Y = 350, 30
ACT_TOPMOST = False
# ==============================================
import tkinter as tk
from tkinter import scrolledtext, ttk
# --------- 线程安全队列 ---------
gui_log_queue = Queue(maxsize=500)
user_event_queue = Queue(maxsize=20)
act_table_queue = Queue(maxsize=5)
thread_local = threading.local()
time_offset_ms = 0
MAX_TIME_OFFSET = 120 * 1000
cred_lock = threading.Lock()
exit_flag = threading.Event()
# 任务停止标记字典 key: aid, value: threading.Event
task_stop_flags = dict()
task_stop_lock = threading.Lock()
# 报名/详情接口返回登录失效时置位，由后台主循环统一重新登录（避免多线程各自弹窗/空转）
relogin_event = threading.Event()
# 活动列表快照（与界面显示同源）：key=str(aid)，value 含 peopleLimit/enrollCount/isAbleEnroll
# 蹲守线程据此判定名额，详情接口不返回这两个字段
activity_snapshot = dict()
activity_snapshot_lock = threading.Lock()
# 全局缓存：真正学院列表（名字以学院结尾）
all_college_list = []
# 学校二课固定5大活动分类
FIX_CATEGORY_LIST = ["全部",
                     "思想政治与道德修养",
                     "社会实践与志愿服务",
                     "文化艺术与身心发展",
                     "学术科技与创新创业",
                     "社会工作与技能拓展"]
# -------- 日志处理器 --------
class QueueLogHandler(logging.Handler):
    def emit(self, record):
        msg = self.format(record)
        gui_log_queue.put(msg)
logger = logging.getLogger("sdust_erke_countdown")
logger.setLevel(logging.INFO)
logger.handlers.clear()
log_fmt = logging.Formatter("%(asctime)s - %(levelname)s - %(message)s", datefmt="%Y-%m-%d %H:%M:%S")
q_handler = QueueLogHandler()
q_handler.setFormatter(log_fmt)
logger.addHandler(q_handler)

def enqueue_user_event(evt):
    """事件入队工具：refresh事件做去重，丢弃队列内旧refresh，仅保留最新；其余事件直接入队"""
    if evt[0] == "refresh":
        temp = []
        while not user_event_queue.empty():
            item = user_event_queue.get_nowait()
            if item[0] != "refresh":
                temp.append(item)
        for t in temp:
            user_event_queue.put(t)
    user_event_queue.put(evt)

def safe_json_parse(resp):
    """安全解析response json，空/HTML/解析异常返回None"""
    if resp is None:
        return None
    txt = resp.text.strip()
    if not txt:
        return None
    try:
        return resp.json()
    except ValueError:
        return None

def to_int(v, default=-1):
    """把接口字段安全转int；无法识别时返回default（蹲守判定用-1表示未知，绝不当作0）"""
    if v is None or isinstance(v, bool):
        return default
    try:
        return int(v)
    except (TypeError, ValueError):
        try:
            return int(float(v))
        except (TypeError, ValueError):
            return default

def is_auth_fail_code(code, msg=""):
    """判断业务返回码是否为登录失效（10001 / 401 / 403 / 提示登陆失败）"""
    msg = msg or ""
    if str(code) in ("10001", "401", "403"):
        return True
    return ("登陆失败" in msg) or ("登录失败" in msg) or ("重新登陆" in msg) or ("重新登录" in msg)

def popup_input_dialog(title: str, prompt_text: str, is_password=False):
    dialog = tk.Toplevel()
    dialog.title(title)
    dialog.geometry("620x320+350+260")
    dialog.attributes("-topmost", True)
    dialog.grab_set()
    result_container = {"value": None}
    ttk.Label(dialog, text=prompt_text, wraplength=570).pack(pady=10, padx=12)
    var_input = tk.StringVar()
    ent = ttk.Entry(dialog, textvariable=var_input, show="*" if is_password else "")
    ent.pack(padx=12, pady=5, fill=tk.X)
    ent.focus_set()
    def on_ok():
        result_container["value"] = var_input.get()
        dialog.destroy()
    def on_cancel():
        result_container["value"] = None
        dialog.destroy()
    frm_btn = ttk.Frame(dialog)
    frm_btn.pack(pady=12)
    ttk.Button(frm_btn, text="确定", command=on_ok).pack(side=tk.LEFT, padx=8)
    ttk.Button(frm_btn, text="取消", command=on_cancel).pack(side=tk.LEFT, padx=8)
    ent.bind("<Return>", lambda e: on_ok())
    dialog.wait_window()
    return result_container["value"]

def token_fp(token: str) -> str:
    """token 指纹：前10…后6，只用于日志核对是否为同一个 token，不输出完整内容"""
    t = (token or "").strip()
    if not t:
        return "(空)"
    if len(t) <= 20:
        return t[:3] + "…" + t[-2:]
    return f"{t[:10]}…{t[-6:]}"

def _read_cred_file():
    """读 cred.json，失败返回空dict"""
    try:
        with open(CRED_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
            return d if isinstance(d, dict) else {}
    except Exception:
        return {}

def clear_stored_stable_auth(reason: str = ""):
    """清空cred.json中的stored_authorization持久token缓存，增加文件损坏容错"""
    global relogin_stable_auth_fail_count, reused_stable_auth
    with cred_lock:
        try:
            with open(CRED_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            data["stored_authorization"] = ""
            with open(CRED_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            relogin_stable_auth_fail_count = 0
            reused_stable_auth = False
            logger.warning(f"⚠️已清空持久Authorization缓存{('（' + reason + '）') if reason else ''}，下次登录强制完整抓取全新token")
        except (json.JSONDecodeError, IOError, Exception) as e:
            logger.warning(f"⚠️cred.json损坏或读取出错，重建空凭证文件:{e}")
            data = {"Authorization":"","Cookie":"","ERKE_VPN_BASE":"","stored_authorization":""}
            with open(CRED_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            relogin_stable_auth_fail_count = 0
            reused_stable_auth = False

def mark_reused_auth_fail(msg: str = ""):
    """复用来的 Authorization 被【业务层】确认失效（10001）时才累加计数。
    注意：VPN 票据失效（HTML/401/403）不走这里，见 mark_vpn_ticket_fail。
    """
    global relogin_stable_auth_fail_count, reused_stable_auth
    if not reused_stable_auth:
        # 非复用 token（本次是完整抓取的）失效，只提示，不计入复用失败
        logger.warning(f"⚠️当前Authorization被服务端判失效{('（' + msg + '）') if msg else ''}（非复用来源，不计入复用阈值）")
        return
    reused_stable_auth = False
    relogin_stable_auth_fail_count += 1
    logger.warning(f"⚠️复用Authorization验证失败{('（' + msg + '）') if msg else ''}，"
                   f"计数 {relogin_stable_auth_fail_count}/{STABLE_AUTH_MAX_CONTINUE_FAIL}")
    if relogin_stable_auth_fail_count >= STABLE_AUTH_MAX_CONTINUE_FAIL:
        clear_stored_stable_auth("连续复用失败达到阈值")

def mark_vpn_ticket_fail(msg: str = ""):
    """VPN 票据/代理层失效（返回登录页 HTML、401、403）：只刷新 Cookie 即可，绝不清持久 token"""
    global vpn_ticket_fail_count
    vpn_ticket_fail_count += 1
    logger.warning(f"🌐 VPN票据失效{('（' + msg + '）') if msg else ''}（第{vpn_ticket_fail_count}次）"
                   f"，将只刷新Cookie复用token，持久Authorization保持不动")

def mark_auth_ok(reason: str = ""):
    """接口业务成功(code=0)：记录最近可用时间并（节流60秒）落盘，用于判断token是否仍然有效"""
    global last_ok_at_ms, _last_ok_persist_ts
    last_ok_at_ms = int(time.time() * 1000)
    if time.time() - _last_ok_persist_ts < 60:
        return
    _last_ok_persist_ts = time.time()
    with cred_lock:
        data = _read_cred_file()
        if not data:
            return
        data["last_ok_at"] = last_ok_at_ms
        try:
            with open(CRED_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

def token_expired_locally(token: str, margin_sec: int = 60) -> bool:
    """若 Authorization 是 JWT，本地解析 exp 判断是否已过期。
    本系统 token 不带 exp（只有签名+业务字段），因此恒返回 False → 视为可长期复用，交给服务端判定。
    """
    try:
        parts = (token or "").split(".")
        if len(parts) != 3:
            return False
        import base64
        payload_b64 = parts[1] + "=" * (-len(parts[1]) % 4)
        payload = json.loads(base64.urlsafe_b64decode(payload_b64).decode("utf-8", "ignore"))
        exp = payload.get("exp")
        if isinstance(exp, (int, float)):
            return time.time() + margin_sec >= float(exp)
    except Exception:
        return False
    return False

def fmt_age(ts_ms) -> str:
    """把毫秒时间戳格式化成“已保存 N 天/小时/分钟”"""
    try:
        if not ts_ms or int(ts_ms) <= 0:
            return "保存时间未知"
        sec = time.time() - int(ts_ms) / 1000
        if sec < 0:
            return "时间异常"
        if sec < 3600:
            return f"已保存 {int(sec // 60)} 分钟"
        if sec < 86400:
            return f"已保存 {int(sec // 3600)} 小时"
        return f"已保存 {int(sec // 86400)} 天"
    except Exception:
        return "保存时间未知"

# ============= 业务工具函数 =============
def parse_vpn_base_from_url(full_url: str):
    url_no_hash = full_url.split("#")[0].rstrip("/")
    if "/https/" in url_no_hash:
        idx = url_no_hash.find("/https/")
        base_part = url_no_hash[:idx + len("/https/")] + url_no_hash[idx + len("/https/"):].split("/")[0]
        logger.info(f"✅ 自动解析WebVPN代理基础地址：{base_part}")
        return base_part
    logger.error(f"❌ URL解析失败，无法提取vpn base: {full_url}")
    return None

def save_cred(auth, cookie, vpn_base, store_stable_auth:bool=True):
    """保存凭证。
    store_stable_auth=True  ：完整登录拿到新 token，同时更新持久 Authorization
    store_stable_auth=False ：只是复用旧 token、刷新 Cookie 票据，持久 Authorization 必须原样保留（旧版这里被写成空串）
    """
    global ERKE_VPN_BASE, relogin_stable_auth_fail_count, reused_stable_auth, last_ok_at_ms
    ERKE_VPN_BASE = vpn_base
    with cred_lock:
        old = _read_cred_file()
        old_stored = (old.get("stored_authorization") or "")
        old_stored_at = old.get("stored_at") or 0
        old_last_ok = old.get("last_ok_at") or 0
        if store_stable_auth:
            stored_out = auth
            # 只有换成“不同的 token”才算新保存；同一 token 再走完整流程不重置保存时间
            if stored_out and stored_out != old_stored:
                stored_at = int(time.time() * 1000)
            else:
                stored_at = old_stored_at or int(time.time() * 1000)
        else:
            # 保留原持久令牌；万一旧文件里已经是空的，退回本次使用的 auth，保证下次仍有可复用令牌
            stored_out = old_stored or auth
            stored_at = old_stored_at or (int(time.time() * 1000) if stored_out else 0)
        data = {
            "Authorization": auth,
            "Cookie": cookie,
            "ERKE_VPN_BASE": vpn_base,
            "stored_authorization": stored_out,
            "stored_at": stored_at,
            "last_ok_at": last_ok_at_ms or old_last_ok
        }
        with open(CRED_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    if store_stable_auth:
        logger.info(f"✅ 凭证&VPN代理地址已保存，已持久化存储Authorization用于后续复用"
                    f"（fp:{token_fp(stored_out)}）")
        relogin_stable_auth_fail_count = 0 #完整抓取成功，重置失败计数器
        reused_stable_auth = False        # 当前 token 是全新抓取的，不再属于“复用”
    else:
        logger.info(f"✅ 凭证&VPN代理地址已保存（持久Authorization原样保留，仅刷新Cookie票据）"
                    f"（fp:{token_fp(stored_out)}，{fmt_age(stored_at)}）")

def load_cred():
    """读取本地凭证。stored_authorization 独立返回：Authorization/Cookie 缺失时也不要把它一起丢掉"""
    global ERKE_VPN_BASE, last_ok_at_ms
    try:
        with open(CRED_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception:
        logger.info("ℹ️ 无缓存凭证，需要手动登录抓取")
        return None, None, None
    auth = (data.get("Authorization") or "").strip()
    cookie = (data.get("Cookie") or "").strip()
    vpn_base = (data.get("ERKE_VPN_BASE") or "").strip()
    stored_auth = (data.get("stored_authorization") or "").strip()
    last_ok_at_ms = int(data.get("last_ok_at") or 0)
    if vpn_base:
        ERKE_VPN_BASE = vpn_base
    if auth and cookie and vpn_base:
        logger.info(f"✅ 读取本地缓存凭证，VPN_BASE:{ERKE_VPN_BASE}，token指纹:{token_fp(auth)}")
        return auth, cookie, (stored_auth or None)
    missing = []
    if not auth:
        missing.append("Authorization")
    if not cookie:
        missing.append("Cookie")
    if not vpn_base:
        missing.append("ERKE_VPN_BASE")
    logger.warning(f"⚠️本地凭证不完整（缺少 {','.join(missing)}），需要重新登录；"
                   f"持久Authorization仍保留（fp:{token_fp(stored_auth)}）可用于复用判定")
    return None, None, (stored_auth or None)

def get_api_url(api_path: str):
    if not ERKE_VPN_BASE:
        raise RuntimeError("ERKE_VPN_BASE未初始化，请先登录")
    return f"{ERKE_VPN_BASE}{api_path}"

def load_tasks():
    try:
        with open(TASK_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []

def save_tasks_atomic(task_list, lock: threading.Lock):
    with lock:
        with open(TASK_TMP, "w", encoding="utf-8") as f:
            json.dump(task_list, f, ensure_ascii=False, indent=2)
        os.replace(TASK_TMP, TASK_FILE)

def clean_expired_tasks(task_list, task_id_set, now_ts):
    new_list = []
    for t in task_list:
        end_ts = t.get("enrollEndTime", 0)
        if end_ts <= 0 or now_ts < end_ts:
            new_list.append(t)
        else:
            logger.warning(f"🗑️自动清理过期任务：{t['name']}")
    task_id_set.clear()
    for t in new_list:
        task_id_set.add(t["id"])
    return new_list

def get_thread_session(base_headers):
    if not hasattr(thread_local, "session"):
        s = requests.Session()
        thread_local.session = s
    thread_local.session.headers.update(base_headers)
    return thread_local.session

def bump_empty():
    global empty_count
    empty_count += 1
    if empty_count >= max_empty:
        logger.warning(f"⚠️ 连续异常/空返回达到 {empty_count}/{max_empty}，将触发重新登录")

def http_get(session: requests.Session, url, timeout=10):
    global empty_count, time_offset_ms
    time.sleep(random.uniform(0.01,0.06))
    try:
        resp = session.get(url, timeout=timeout)
        if resp.status_code == 429:
            logger.warning("⚠️收到429限流，短暂休眠2秒")
            time.sleep(2.0)
        if "Date" in resp.headers:
            try:
                server_dt = parsedate_to_datetime(resp.headers["Date"])
                server_ts_ms = int(server_dt.timestamp() * 1000)
                local_ts_ms = int(time.time() * 1000)
                delta = server_ts_ms - local_ts_ms
                if abs(delta) < MAX_TIME_OFFSET:
                    time_offset_ms = delta
            except Exception:
                pass
        # 检测WebVPN返回HTML登录页面
        txt_sample = resp.text[:300]
        if "<!DOCTYPE html>" in txt_sample or "<html" in txt_sample:
            logger.warning("❗检测返回HTML页面，判定VPN票据失效（token保持不动），需要重登录")
            mark_vpn_ticket_fail("GET 返回登录页")
            return resp, True
        if resp.status_code in (401, 403):
            logger.error("❗ 接口返回 401/403，VPN票据失效")
            mark_vpn_ticket_fail(f"GET {resp.status_code}")
            return resp, True
        empty_count = 0
        return resp, False
    except Exception as e:
        logger.error(f"GET 请求异常: {e}")
        bump_empty()
        return None, False

def http_post(session: requests.Session, url, json_data, timeout=3):
    time.sleep(random.uniform(0.01,0.05))
    try:
        resp = session.post(url, json=json_data, timeout=timeout)
        if resp.status_code ==429:
            logger.warning("⚠️收到429限流，短暂休眠2秒")
            time.sleep(2.0)
        txt_sample = resp.text[:300]
        if "<!DOCTYPE html>" in txt_sample or "<html" in txt_sample:
            logger.warning("❗POST检测返回HTML页面，VPN票据失效（token保持不动），需要重登录")
            mark_vpn_ticket_fail("POST 返回登录页")
            return resp, True
        if resp.status_code in (401, 403):
            logger.error("❗ POST 返回 401/403，VPN票据失效")
            mark_vpn_ticket_fail(f"POST {resp.status_code}")
            return resp, True
        return resp, False
    except Exception as e:
        logger.error(f"POST 请求异常: {e}")
        bump_empty()
        return None, False

def fetch_dept_dict(session):
    """获取部门，只保留名字以【学院】结尾的条目，过滤团委、学生会、部门、中心"""
    global all_college_list
    params = json.dumps({"nature": "1,2,3,4,7,19"})
    url = f"{get_api_url('/api/app/client/v1/organization/department')}?{VPN_QUERY_PARAM}&params={quote(params)}"
    resp, need_relogin = http_get(session, url)
    if need_relogin:
        return {}, True
    if resp is None:
        logger.warning("⚠️获取学院接口失败，将降级从活动提取学院")
        all_college_list = []
        return {}, False
    ret = safe_json_parse(resp)
    if ret is None:
        logger.warning("⚠️学院接口返回非JSON/空响应，降级从活动提取学院")
        all_college_list = []
        return {}, False
    if ret.get("code") == 0:
        mark_auth_ok("学院字典")
        d = {}
        all_college_list = []
        for item in ret["data"]:
            name = item.get("name","")
            if name.endswith("学院"):
                dept_id = int(item["id"])
                d[dept_id] = name
                all_college_list.append({"id":dept_id,"name":name})
        logger.info(f"✅ 学院字典加载成功，过滤后共 {len(d)} 个学院")
        return d, False
    else:
        logger.warning(f"部门字典接口返回异常: {ret}")
        all_college_list = []
        return {}, False

def manual_login_get_token():
    global relogin_stable_auth_fail_count, reused_stable_auth
    from selenium import webdriver
    from selenium.webdriver.edge.options import Options
    edge_options = Options()
    edge_options.add_argument("--start-maximized")
    edge_options.add_experimental_option("excludeSwitches", ["enable-automation"])
    edge_options.add_experimental_option("useAutomationExtension", False)
    driver = webdriver.Edge(options=edge_options)
    driver.execute_cdp_cmd("Page.addScriptToEvaluateOnNewDocument", {
        "source": "Object.defineProperty(navigator, 'webdriver', {get: () => undefined})"
    })
    auth_token = None
    vpn_base = None
    # 读取本地持久保存可复用token
    _, _, stored_stable_auth = load_cred()
    try:
        logger.info("正在打开WebVPN主页，请按下面操作：")
        logger.info("1、登录webvpn.sdust.edu.cn")
        logger.info("2、在webvpn主页手动点击【第二课堂信息化管理系统】（会新开标签页）")
        logger.info("3、确认新标签页成功进入二课首页 #/home！")
        driver.get("https://webvpn.sdust.edu.cn/")
        _ret = popup_input_dialog("浏览器操作确认", "请完成浏览器WebVPN登录并打开二课首页，完成后点【确定】")
        if _ret is None:
            raise Exception("用户取消登录")
        all_tabs = driver.window_handles
        if len(all_tabs) > 1:
            driver.switch_to.window(all_tabs[-1])
            logger.info("✅ 已切换至二课新开标签页")
        current_url = driver.current_url
        vpn_base = parse_vpn_base_from_url(current_url)
        if not vpn_base:
            raise Exception("解析WebVPN代理地址失败，请确认页面是二课系统页面")
        # 判断：有持久token 且 该token本地未过期 且 复用失败计数未超阈值，才复用token只刷cookie
        reuse_allowed = bool(
            stored_stable_auth
            and stored_stable_auth.strip()
            and relogin_stable_auth_fail_count < STABLE_AUTH_MAX_CONTINUE_FAIL
        )
        if reuse_allowed and token_expired_locally(stored_stable_auth.strip()):
            logger.warning("⚠️持久Authorization已过期（JWT exp 已过），跳过复用直接完整抓取")
            reuse_allowed = False
        if reuse_allowed:
            auth_token = stored_stable_auth.strip()
            # 不在此累加失败计数：只有“复用后业务层确认失效(10001)”才算一次失败（见 mark_reused_auth_fail）
            reused_stable_auth = True
            saved = _read_cred_file()
            logger.info(f"♻️ 复用持久token（fp:{token_fp(auth_token)}，{fmt_age(saved.get('stored_at'))}），"
                        f"仅刷新WebVPN Cookie票据；已确认失效计数:{relogin_stable_auth_fail_count}/{STABLE_AUTH_MAX_CONTINUE_FAIL}")
            cookies = driver.get_cookies()
            cookie_str = "; ".join([f"{c['name']}={c['value']}" for c in cookies])
            save_cred(auth_token, cookie_str, vpn_base, store_stable_auth=False)
            return auth_token.strip(), cookie_str
        else:
            # 条件不满足：计数超限 / 无持久token，完整抓取全新Authorization
            if relogin_stable_auth_fail_count >= STABLE_AUTH_MAX_CONTINUE_FAIL:
                logger.warning(f"⚠️已达到复用Authorization失败阈值{STABLE_AUTH_MAX_CONTINUE_FAIL}，强制完整抓取全新token")
                clear_stored_stable_auth()
            logger.info("⚠️执行完整页面抓取token流程")
            inject_script = """
            if(!window._auth_hijack_inited){
                window._auth = null;
                const originFetch = window.fetch;
                window.fetch = function(resource, init={}){
                    if(init.headers){
                        let h = new Headers(init.headers);
                        let token = h.get('Authorization');
                        if(token) window._auth = token;
                    }
                    return originFetch.apply(this, arguments);
                }
                window._auth_hijack_inited = true;
            }
            """
            driver.execute_script(inject_script)
            logger.info("⏳ 刷新页面触发接口请求，等待抓取Authorization...")
            driver.refresh()
            wait_times = 40
            for _ in range(wait_times):
                auth_token = driver.execute_script("return window._auth")
                if auth_token:
                    logger.info("✅ 自动抓取Authorization成功！")
                    break
                time.sleep(0.5)
            if not auth_token:
                logger.warning("⚠️ 自动抓取超时，请手动复制浏览器Network中的Authorization")
                manual_tip = """自动抓取Authorization超时，请按下面步骤手动复制：
1.浏览器保持停留在二课系统页面，按F12打开开发者工具
2.切换到【网络(Network)】标签，刷新当前页面
3.随便点开任意一条 list? 开头的请求
4.在【请求头(Request Headers)】找到 Authorization
5.完整复制整串字符串粘贴到下方输入框
"""
                auth_token = popup_input_dialog("手动粘贴Authorization", manual_tip)
                if auth_token is None:
                    raise Exception("用户取消输入Authorization")
                auth_token = auth_token.strip()
            cookies = driver.get_cookies()
            cookie_str = "; ".join([f"{c['name']}={c['value']}" for c in cookies])
            save_cred(auth_token, cookie_str, vpn_base, store_stable_auth=True)
            return auth_token.strip(), cookie_str
    except Exception as e:
        logger.error(f"登录过程出错：{e}")
        popup_input_dialog("登录异常", f"登录发生错误：{str(e)}\n点确定关闭浏览器")
        raise
    finally:
        driver.quit()

def day_to_ts(delta_day):
    today = datetime.date.today()
    target_day = today + datetime.timedelta(days=delta_day)
    dt = datetime.datetime.combine(target_day, datetime.time.min)
    local_ms = int(dt.timestamp() *1000)
    return local_ms + time_offset_ms

def get_url_by_day(delta_day):
    ts = day_to_ts(delta_day)
    path = "/api/app/client/v1/page/activity/list"
    params_json = f'{{"search":"","pageNum":1,"pageSize":10,"sortType":1,"activityTime":{ts},"classifyId":0,"status":"4,5,6,7","level":0,"organizationName":"","fieldType":"activity_iseErollment","keyWord":"switch"}}'
    return f"{get_api_url(path)}?params={quote(params_json)}"

def fetch_all_days(session, fetch_day_count):
    all_acts = []
    need_relogin_flag = False
    for d in range(fetch_day_count):
        url = get_url_by_day(d)
        resp, need_relogin = http_get(session, url, timeout=10)
        if need_relogin:
            need_relogin_flag = True
            continue
        if resp is None:
            logger.error(f"❌ 第{d}天返回空，连续空次数：{empty_count}/{max_empty}")
            continue
        data = safe_json_parse(resp)
        if data is None:
            logger.error(f"❌ 第{d}天接口返回非JSON/空响应")
            continue
        if data.get("code") != 0:
            logger.error(f"❌ 第{d}天业务异常 code={data.get('code')}, msg={data.get('msg')}")
            continue
        list_act = data.get("data", {}).get("list", [])
        mark_auth_ok("活动列表")
        all_acts.extend(list_act)
    unique_acts = {}
    for act in all_acts:
        aid = act.get("id")
        if aid:
            unique_acts[aid] = act
    return list(unique_acts.values()), need_relogin_flag

def get_activity_detail(session, act_id, detail_cache: dict):
    now = time.time()
    if len(detail_cache) > MAX_DETAIL_CACHE:
        remove_keys = sorted(detail_cache.keys(), key=lambda k: detail_cache[k]["cache_time"])[:20]
        for k in remove_keys:
            del detail_cache[k]
    if act_id in detail_cache:
        item = detail_cache[act_id]
        if now - item["cache_time"] < CACHE_TTL:
            return item["data"], False
    params = json.dumps({"id": str(act_id)})
    url = f"{get_api_url('/api/app/client/v1/activity/detail/non-member')}?{VPN_QUERY_PARAM}&params={quote(params)}"
    retry = 0
    while retry <= DETAIL_RETRY:
        resp, need_relogin = http_get(session, url, timeout=10)
        if need_relogin:
            return {}, True
        if resp is None:
            retry +=1
            if retry <= DETAIL_RETRY:
                time.sleep(0.3)
                continue
            else:
                logger.error(f"❌ 获取活动详情请求失败 aid={act_id}，已用尽重试")
                return {}, False
        ret = safe_json_parse(resp)
        if ret is None:
            retry +=1
            if retry <= DETAIL_RETRY:
                time.sleep(0.3)
                continue
            else:
                logger.warning(f"详情接口返回非JSON aid={act_id}，已用尽重试")
                return {}, False
        if ret.get("code") == 0:
            mark_auth_ok("活动详情")
            d = ret.get("data", {})
            detail_cache[act_id] = {"data": d, "cache_time": now}
            return d, False
        else:
            code = ret.get("code")
            msg = ret.get("msg", "")
            if is_auth_fail_code(code, msg):
                logger.warning(f"🔑 详情接口登录失效 aid={act_id} code={code} msg={msg}")
                mark_reused_auth_fail(f"详情接口 {code}")
                relogin_event.set()
                return {}, True
            logger.warning(f"详情接口返回错误 aid={act_id} code={code} msg={msg}")
            return {}, False
    return {}, False

def fmt_ts(ts):
    if not ts or ts <= 0:
        return "无"
    try:
        return datetime.datetime.fromtimestamp(ts / 1000).strftime("%m-%d %H:%M")
    except Exception:
        return "无效时间"

def sign_up(session, act_id, act_name, retry_count):
    """报名接口。返回 (ok, need_relogin)；登录失效时置位 relogin_event 交由后台统一重新登录"""
    payload = {"activityId": act_id}
    url = get_api_url("/api/app/client/v1/activity/enroll")
    backoff = min(BASE_BACKOFF * (2**retry_count), MAX_BACKOFF)
    time.sleep(random.uniform(backoff*0.6, backoff*1.2))
    resp, need_relogin = http_post(session, url, payload, timeout=3)
    if need_relogin:
        relogin_event.set()
        return False, True
    if resp is None:
        return False, False
    ret = safe_json_parse(resp)
    if ret is None:
        logger.warning(f"报名接口返回非JSON【{act_name}】")
        return False, False
    code = ret.get("code")
    msg = ret.get("msg", "")
    if code == 0:
        mark_auth_ok("报名")
        logger.info(f"✅【报名成功】{act_name} id:{act_id}")
        enqueue_user_event(("popup_msg","抢报成功",f"活动：{act_name}\nID:{act_id}"))
        return True, False
    if is_auth_fail_code(code, msg):
        # 凭证失效：只报一次，交给后台主循环重新登录，避免每 0.8s 反复刷同一条错误
        logger.warning(f"🔑【{act_name}】报名接口返回登录失效 code:{code} msg:{msg}，已请求重新登录")
        mark_reused_auth_fail(f"报名接口 {code}")
        relogin_event.set()
        return False, True
    if msg and ("已满" in msg or "名额" in msg):
        logger.warning(f"⚠️【报名失败】{act_name} | 名额已满（{msg}），等列表快照更新后再判")
        return False, False
    logger.warning(f"⚠️【报名失败】{act_name} | code:{code} msg:{msg}")
    return False, False

def sprint_worker(headers_ref, task, task_list_lock, task_list, task_id_set, stop_flag: threading.Event):
    aid = task["id"]
    name = task["name"]
    enroll_start_ts = task["enrollStartTime"]
    enroll_end_ts = task.get("enrollEndTime", 0)
    task_type = task.get("task_type","normal")
    logger.info(f"⏰ {'[普通抢报]' if task_type=='normal' else '[蹲守]'}开始盯防【{name}】，报名开始: {fmt_ts(enroll_start_ts)}")
    retry_cnt = 0
    watchdog_cnt = 0
    free_hit = False       # 蹲守：是否已检测到一次释放名额（用于二次确认）
    try:
        while not exit_flag.is_set() and not stop_flag.is_set():
            now_ts = int(time.time() * 1000) + time_offset_ms
            if enroll_end_ts and now_ts >= enroll_end_ts:
                logger.info(f"⏭️【{name}】报名截止，停止盯防")
                break
            if task_type == "normal":
                diff = enroll_start_ts - now_ts - SPRINT_ADVANCE_MS
                if diff <= 0:
                    sess = get_thread_session(headers_ref.copy())
                    ok, need_relogin = sign_up(sess, aid, name, retry_cnt)
                    if ok:
                        break
                    if need_relogin:
                        # 登录失效不算抢报重试次数，等后台主循环重新登录后再打
                        time.sleep(2.0)
                        continue
                    retry_cnt += 1
                    if retry_cnt >= SIGN_MAX_RETRY:
                        logger.warning(f"❌【{name}】抢报达到最大重试次数，放弃")
                        break
                    time.sleep(SPRINT_SLEEP)
                    continue
                diff_sec = diff / 1000
                if not QUIET_COUNTDOWN or diff_sec <= COUNTDOWN_ALERT_SEC:
                    logger.info(f"⌛【{name}】倒计时: {diff_sec:.1f}s")
                if diff_sec > 3:
                    time.sleep(1)
                else:
                    time.sleep(SPRINT_SLEEP)
            elif task_type == "watchdog":
                watchdog_cnt +=1
                if watchdog_cnt >= WATCHDOG_MAX_RETRY:
                    logger.warning(f"⚠️【{name}】蹲守达到最大轮询次数，结束蹲守")
                    enqueue_user_event(("popup_msg","蹲守任务结束",f"活动 {name}\n达到最大蹲守轮数，自动停止"))
                    break
                sess = get_thread_session(headers_ref.copy())
                # 用详情确认活动仍在报名期/未被下架（详情不含 peopleLimit、enrollCount）
                detail, relog = get_activity_detail(sess, aid, dict())
                if relog:
                    logger.warning(f"🔑【{name}】蹲守查询登录失效，暂停等待重新登录")
                    time.sleep(3.0)
                    continue
                if not detail:
                    time.sleep(WATCHDOG_INTERVAL)
                    continue
                # ★ 名额判定改用活动列表快照（与界面显示同源），不再从 detail 取 enrollCount
                with activity_snapshot_lock:
                    snap = dict(activity_snapshot.get(str(aid)) or {})
                if not snap:
                    # 列表里暂时没有这条活动（翻页/掉出抓取范围），本轮不判定，避免误报
                    free_hit = False
                    time.sleep(WATCHDOG_INTERVAL)
                    continue
                if time.time() - snap.get("update_time", 0) > SNAPSHOT_STALE_SEC:
                    free_hit = False
                    if watchdog_cnt % 20 == 1:
                        logger.info(f"ℹ️【{name}】列表快照超过 {SNAPSHOT_STALE_SEC}s 未更新，暂不判定名额（继续蹲守中）")
                    time.sleep(WATCHDOG_INTERVAL)
                    continue
                pl = to_int(snap.get("peopleLimit"), -1)
                ec = to_int(snap.get("enrollCount"), -1)
                able = to_int(snap.get("isAbleEnroll"), -1)
                if pl <= 0 or ec < 0:
                    # 字段缺失/不限人数：名额未知，不做判定
                    free_hit = False
                    time.sleep(WATCHDOG_INTERVAL)
                    continue
                if able == 0:
                    # 列表明确标记不可报名：即使 ec<pl 也不报
                    free_hit = False
                    if watchdog_cnt % 20 == 1:
                        logger.info(f"ℹ️【{name}】列表标记不可报名（{ec}/{pl}），继续蹲守")
                    time.sleep(WATCHDOG_INTERVAL)
                    continue
                if ec < pl:
                    if not free_hit:
                        # 第一次命中：只记录，下一轮再确认，避免单次脏数据误报
                        free_hit = True
                        logger.info(f"🔎【{name}】检测到名额 {ec}/{pl}，等待再次确认…")
                        time.sleep(WATCHDOG_INTERVAL)
                        continue
                    logger.info(f"🎉【{name}】二次确认有名额 {ec}/{pl}，立即发起报名")
                    ok, need_relogin = sign_up(sess, aid, name, 0)
                    if ok:
                        break
                    free_hit = False
                    if need_relogin:
                        logger.warning(f"🔑【{name}】报名被拒（登录失效），等待后台重新登录后再蹲守")
                        time.sleep(3.0)
                        continue
                    logger.info(f"⏳【{name}】报名未成功，退避后再判（可能是残余名额被抢走或接口拒绝）")
                    time.sleep(max(WATCHDOG_INTERVAL, 2.5))
                    continue
                free_hit = False
                time.sleep(WATCHDOG_INTERVAL)
    except Exception as e:
        logger.error(f"❌ sprint_worker 线程异常【{name}】: {e}")
    logger.info(f"🛑【{name}】盯防线程已退出")
    with task_list_lock:
        try:
            task_list.remove(task)
            task_id_set.discard(aid)
            save_tasks_atomic(task_list, task_list_lock)
        except ValueError:
            pass
    with task_stop_lock:
        if aid in task_stop_flags:
            del task_stop_flags[aid]
# ========== 后台业务主循环线程 ==========
def backend_loop():
    global empty_count
    global time_offset_ms
    try:
        task_list = load_tasks()
        task_id_set = {t["id"] for t in task_list}
        detail_cache = {}
        AUTHORIZATION, COOKIE_STR, STORED_STABLE_AUTH = load_cred()
        if not AUTHORIZATION or not COOKIE_STR:
            AUTHORIZATION, COOKIE_STR = manual_login_get_token()
        if STORED_STABLE_AUTH:
            saved = _read_cred_file()
            logger.info(f"ℹ️ 持久token：fp:{token_fp(STORED_STABLE_AUTH)}，{fmt_age(saved.get('stored_at'))}，"
                        f"最近可用 {fmt_ts(saved.get('last_ok_at'))}")
        HEADERS = {
            "Accept": "*/*",
            "Accept-Encoding": "gzip, deflate, br, zstd",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8,en-GB;q=0.7,en-US;q=0.6",
            "Authorization": AUTHORIZATION,
            "Cookie": COOKIE_STR,
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
            "Referer": f"{ERKE_VPN_BASE}/#/home"
        }
        main_session = requests.Session()
        main_session.headers.update(HEADERS)
        logger.info("✅【v0.2.6】后台监控启动（蹲守快照判定 / 持久token复用 / 失败来源分流）")
        dept_dict, need_relogin = fetch_dept_dict(main_session)
        if need_relogin:
            AUTHORIZATION, COOKIE_STR = manual_login_get_token()
            HEADERS["Authorization"] = AUTHORIZATION
            HEADERS["Cookie"] = COOKIE_STR
            main_session.headers.update(HEADERS)
            dept_dict, _ = fetch_dept_dict(main_session)
        now_ts_init = int(time.time()*1000)+time_offset_ms
        task_list = clean_expired_tasks(task_list, task_id_set, now_ts_init)
        save_tasks_atomic(task_list, threading.Lock())
        logger.info(f"✅ 当前待抢任务数：{len(task_list)}")
        logger.info(f"ℹ️ 时间偏移校准：{time_offset_ms} ms（服务器时间 - 本机时间）")
        task_list_lock = threading.Lock()
        worker_threads = []
        cached_raw_activities = []
        cached_dept_dict = dept_dict
        loop_counter =0
        while not exit_flag.is_set():
            loop_start = time.time()
            now_ts = int(time.time() * 1000) + time_offset_ms
            gui_event = None
            try:
                gui_event = user_event_queue.get_nowait()
            except Empty:
                pass
            loop_counter +=1
            # 定时持久化任务，防止程序被强杀丢失内存任务
            if loop_counter % TASK_SAVE_INTERVAL ==0:
                save_tasks_atomic(task_list, task_list_lock)

            # ★ 报名/详情接口报登录失效（code:10001）时，由后台统一重新登录一次，所有线程同步生效
            if relogin_event.is_set():
                relogin_event.clear()
                logger.warning("🔑 检测到登录失效，开始重新登录（请在弹出的浏览器窗口完成 WebVPN 操作）")
                try:
                    AUTHORIZATION, COOKIE_STR = manual_login_get_token()
                    HEADERS["Authorization"] = AUTHORIZATION
                    HEADERS["Cookie"] = COOKIE_STR
                    main_session.headers.update(HEADERS)
                    empty_count = 0
                    cached_dept_dict, _ = fetch_dept_dict(main_session)
                    detail_cache.clear()
                    logger.info(f"✅ 重新登录完成，盯防线程将自动恢复报名（当前token fp:{token_fp(AUTHORIZATION)}）")
                except Exception as e:
                    logger.error(f"❌ 重新登录失败：{e}，30秒后重试")
                    time.sleep(30)
                    relogin_event.set()
                    continue
            if empty_count >= max_empty:
                logger.warning(f"连续空返回达到 {max_empty} 次，尝试重新登录")
                AUTHORIZATION, COOKIE_STR = manual_login_get_token()
                HEADERS["Authorization"] = AUTHORIZATION
                HEADERS["Cookie"] = COOKIE_STR
                main_session.headers.update(HEADERS)
                empty_count = 0
                task_id_set = {t["id"] for t in task_list}
                cached_dept_dict, _ = fetch_dept_dict(main_session)
                detail_cache.clear()
            alive_workers = []
            for th in worker_threads:
                if th.is_alive():
                    alive_workers.append(th)
            worker_threads = alive_workers
            running_cnt = len(worker_threads)
            for tsk in list(task_list):
                tid = tsk["id"]
                is_running = any(th.name == f"task‑{tid}" for th in worker_threads)
                if not is_running and running_cnt < MAX_WORKER:
                    with task_stop_lock:
                        if tid not in task_stop_flags:
                            task_stop_flags[tid] = threading.Event()
                    stop_flag = task_stop_flags[tid]
                    th = threading.Thread(
                        target=sprint_worker,
                        args=(HEADERS, tsk, task_list_lock, task_list, task_id_set, stop_flag),
                        name=f"task‑{tid}",
                        daemon=True
                    )
                    th.start()
                    worker_threads.append(th)
                    running_cnt += 1
            fetch_day_count = FETCH_DAY_DEFAULT
            if gui_event and gui_event[0] == "refresh":
                fetch_day_count = gui_event[1]
            records, need_relogin = fetch_all_days(main_session, fetch_day_count)
            if need_relogin:
                AUTHORIZATION, COOKIE_STR = manual_login_get_token()
                HEADERS["Authorization"] = AUTHORIZATION
                HEADERS["Cookie"] = COOKIE_STR
                main_session.headers.update(HEADERS)
                empty_count = 0
                cached_dept_dict, _ = fetch_dept_dict(main_session)
                detail_cache.clear()
                continue
            valid_activities = []
            relogin_flag = False
            for item in records:
                aid = item.get("id")
                detail, need_relogin = get_activity_detail(main_session, aid, detail_cache)
                if need_relogin:
                    relogin_flag = True
                    break
                if not detail:
                    logger.warning(f"aid:{aid} 详情为空！")
                    continue
                valid_activities.append(item)
            if relogin_flag:
                AUTHORIZATION, COOKIE_STR = manual_login_get_token()
                HEADERS["Authorization"] = AUTHORIZATION
                HEADERS["Cookie"] = COOKIE_STR
                main_session.headers.update(HEADERS)
                empty_count = 0
                cached_dept_dict, _ = fetch_dept_dict(main_session)
                detail_cache.clear()
                continue
            cached_raw_activities = valid_activities
            # ★ 发布活动列表快照（与界面/加入队列同源），供蹲守线程判定名额
            #   合并更新而非整体清空：蹲守中的活动即使本轮掉出抓取列表，也能保留最近一次可信数据
            snap_now = time.time()
            with activity_snapshot_lock:
                for it in valid_activities:
                    activity_snapshot[str(it.get("id"))] = {
                        "peopleLimit": it.get("peopleLimit", None),
                        "enrollCount": it.get("enrollCount", None),
                        "isAbleEnroll": it.get("isAbleEnroll", None),
                        "enrollEndTime": it.get("enrollEndTime", 0),
                        "name": it.get("name", ""),
                        "update_time": snap_now,
                    }
                for k in list(activity_snapshot.keys()):
                    if snap_now - activity_snapshot[k].get("update_time", 0) > 600:
                        del activity_snapshot[k]
            if gui_event is not None:
                ev_type, ev_data = gui_event
                if ev_type == "refresh":
                    act_table_queue.put((cached_raw_activities, cached_dept_dict, detail_cache, task_list, worker_threads, time_offset_ms))
                elif ev_type == "add":
                    # ev_data 为界面显示序号映射后的活动ID列表（已按筛选后列表换算）
                    sel_ids = ev_data
                    act_by_id = {str(it.get("id")): it for it in cached_raw_activities}
                    for sel_id in sel_ids:
                        selected = act_by_id.get(str(sel_id))
                        if selected is None:
                            logger.warning(f"活动ID {sel_id} 不在当前活动列表中（列表可能已刷新），请重新加入")
                            continue
                        aid = selected.get("id")
                        name = selected.get("name")
                        # 二次网络拉取详情，不使用缓存，校验真实状态
                        real_detail, relog_check = get_activity_detail(main_session, aid, dict())
                        if relog_check or not real_detail:
                            logger.warning(f"⛔【{name}】二次校验详情获取失败，跳过加入队列")
                            continue
                        enroll_start_ts = selected.get("enrollStartTime")
                        enroll_end_ts = real_detail.get("enrollEndTime", selected.get("enrollEndTime",0))
                        # 名额数据以活动列表项为准（详情接口不返回 peopleLimit/enrollCount）
                        peopleLimit = to_int(selected.get("peopleLimit"), 0)
                        enrollCount = to_int(selected.get("enrollCount"), 0)
                        if peopleLimit <= 0:
                            logger.warning(f"⚠️【{name}】列表未返回有效人数上限（peopleLimit={selected.get('peopleLimit')}），按普通抢报处理")
                        now_ts_local = int(time.time()*1000)+time_offset_ms
                        is_end = bool(enroll_end_ts and now_ts_local >= enroll_end_ts)
                        if is_end:
                            logger.warning(f"⛔【{name}】报名已截止，不允许加入任务")
                            continue
                        if aid in task_id_set:
                            logger.info(f"ℹ️ {name} 已在队列中")
                            continue
                        is_full = bool(peopleLimit>0 and enrollCount >= peopleLimit)
                        task_type = "normal"
                        if is_full:
                            task_type = "watchdog"
                            logger.info(f"⚠️【{name}】名额已满（{enrollCount}/{peopleLimit}），将作为蹲守任务，等待有人退报释放名额")
                        else:
                            logger.info(f"✅【{name}】加入普通抢报队列（名额 {enrollCount}/{peopleLimit}）")
                        # 同步刷新快照，蹲守线程启动即可拿到可信数据
                        with activity_snapshot_lock:
                            activity_snapshot[str(aid)] = {
                                "peopleLimit": selected.get("peopleLimit", None),
                                "enrollCount": selected.get("enrollCount", None),
                                "isAbleEnroll": selected.get("isAbleEnroll", None),
                                "enrollEndTime": enroll_end_ts,
                                "name": name,
                                "update_time": time.time(),
                            }
                        new_task = {
                            "id":aid,
                            "name":name,
                            "enrollStartTime":enroll_start_ts,
                            "enrollEndTime":enroll_end_ts,
                            "task_type":task_type
                        }
                        task_list.append(new_task)
                        save_tasks_atomic(task_list, task_list_lock)
                        task_id_set.add(aid)
                    act_table_queue.put((cached_raw_activities, cached_dept_dict, detail_cache, task_list, worker_threads, time_offset_ms))
                elif ev_type == "del":
                    del_indexes = sorted(ev_data, reverse=True)
                    queue_len_now = len(task_list)
                    for d_idx in del_indexes:
                        if 0<= d_idx < len(task_list):
                            removed = task_list.pop(d_idx)
                            aid = removed["id"]
                            task_id_set.discard(aid)
                            with task_stop_lock:
                                if aid in task_stop_flags:
                                    task_stop_flags[aid].set()
                            save_tasks_atomic(task_list, task_list_lock)
                            logger.info(f"🗑️ 已删除队列任务：{removed['name']}，已通知盯防线程停止")
                        else:
                            logger.warning(f"删除队列：序号 {d_idx + 1} 超出范围（当前队列共 {queue_len_now} 条，序号从1开始）")
                    act_table_queue.put((cached_raw_activities, cached_dept_dict, detail_cache, task_list, worker_threads, time_offset_ms))
                elif ev_type == "popup_msg":
                    pass
            elapsed = time.time() - loop_start
            sleep_t = max(0, LOOP_SLEEP - elapsed)
            time.sleep(sleep_t)
        logger.info("后台线程收到退出信号，结束")
    except Exception as e:
        logger.error(f"🔥后台主循环发生未捕获异常 {e}", exc_info=True)
        time.sleep(2)
# ================= GUI 双窗口 =================
class DualWindowGUI:
    def __init__(self, root_main):
        # 日志窗口
        self.win_log = tk.Toplevel(root_main)
        self.win_log.title("【日志窗口】仅输出日志")
        self.win_log.geometry(f"{LOG_W}x{LOG_H}+{LOG_X}+{LOG_Y}")
        self.win_log.attributes("-topmost", LOG_TOPMOST)
        self.win_log.protocol("WM_DELETE_WINDOW", self.on_close_all)
        frm_log_cfg = ttk.Frame(self.win_log)
        frm_log_cfg.pack(fill=tk.X, padx=5, pady=3)
        row1 = ttk.Frame(frm_log_cfg)
        row1.pack(fill=tk.X)
        ttk.Label(row1, text="最大日志条数：").pack(side=tk.LEFT)
        self.var_max_log = tk.StringVar(value=str(MAX_LOG_ITEMS))
        ttk.Entry(row1, textvariable=self.var_max_log, width=8).pack(side=tk.LEFT, padx=2)
        ttk.Label(row1, text=" 刷新间隔(ms)：").pack(side=tk.LEFT)
        self.var_log_interval = tk.StringVar(value=str(LOG_POLL_INTERVAL))
        ttk.Entry(row1, textvariable=self.var_log_interval, width=8).pack(side=tk.LEFT, padx=2)
        row2 = ttk.Frame(frm_log_cfg)
        row2.pack(fill=tk.X, pady=3)
        ttk.Button(row2, text="应用", command=self.apply_log_cfg).pack()
        self.txt_log = scrolledtext.ScrolledText(self.win_log, wrap=tk.WORD, font=("Consolas",9))
        self.txt_log.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.log_deque = deque(maxlen=MAX_LOG_ITEMS)
        self.log_poll_interval = LOG_POLL_INTERVAL
        # 活动主窗口
        self.win_act = root_main
        self.win_act.title("【活动列表窗口】操作面板")
        self.win_act.geometry(f"{ACT_W}x{ACT_H}+{ACT_X}+{ACT_Y}")
        self.win_act.attributes("-topmost", ACT_TOPMOST)
        self.win_act.protocol("WM_DELETE_WINDOW", self.on_close_all)
        frm_filter = ttk.LabelFrame(self.win_act, text="筛选设置（点刷新生效 / 下拉切换自动刷新）")
        frm_filter.pack(fill=tk.X, padx=8, pady=4)
        ttk.Label(frm_filter, text="抓取天数:").pack(side=tk.LEFT, padx=4)
        self.var_fetch_day = tk.StringVar(value=str(FETCH_DAY_DEFAULT))
        ttk.Spinbox(frm_filter, from_=1, to=FETCH_DAY_MAX, textvariable=self.var_fetch_day, width=5).pack(side=tk.LEFT, padx=2)
        ttk.Label(frm_filter, text=" 学院筛选:").pack(side=tk.LEFT, padx=(12,2))
        self.var_college_filter = tk.StringVar(value="全部")
        self.cb_college = ttk.Combobox(frm_filter, textvariable=self.var_college_filter, state="readonly", width=22)
        self.cb_college["values"] = ["全部"]
        self.cb_college.pack(side=tk.LEFT)
        self.cb_college.bind("<<ComboboxSelected>>",lambda e:self.on_refresh())
        ttk.Label(frm_filter, text=" 活动类型:").pack(side=tk.LEFT, padx=(12,2))
        self.var_cat_filter = tk.StringVar(value="全部")
        self.cb_cat = ttk.Combobox(frm_filter, textvariable=self.var_cat_filter, state="readonly", width=26)
        self.cb_cat["values"] = FIX_CATEGORY_LIST
        self.cb_cat.pack(side=tk.LEFT)
        self.cb_cat.bind("<<ComboboxSelected>>",lambda e:self.on_refresh())
        frm_top = ttk.Frame(self.win_act)
        frm_top.pack(fill=tk.X, padx=8, pady=4)
        frm1 = ttk.Frame(frm_top)
        frm1.pack(side=tk.LEFT, padx=4)
        ttk.Button(frm1, text="①刷新活动列表", command=self.on_refresh).pack()
        frm2 = ttk.Frame(frm_top)
        frm2.pack(side=tk.LEFT, padx=12)
        ttk.Label(frm2, text="②加入队列(序号空格分隔):").pack(side=tk.LEFT)
        self.var_add = tk.StringVar()
        ttk.Entry(frm2, textvariable=self.var_add, width=22).pack(side=tk.LEFT, padx=4)
        ttk.Button(frm2, text="加入", command=self.on_add_task).pack(side=tk.LEFT)
        frm3 = ttk.Frame(frm_top)
        frm3.pack(side=tk.LEFT, padx=12)
        ttk.Label(frm3, text="③删除队列(序号空格分隔):").pack(side=tk.LEFT)
        self.var_del = tk.StringVar()
        ttk.Entry(frm3, textvariable=self.var_del, width=22).pack(side=tk.LEFT, padx=4)
        ttk.Button(frm3, text="删除", command=self.on_del_task).pack(side=tk.LEFT)
        frm_split = ttk.Frame(self.win_act)
        frm_split.pack(fill=tk.BOTH, expand=True, padx=6, pady=4)
        frm_left = ttk.Frame(frm_split)
        frm_left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        ttk.Label(frm_left, text="📋 可报名活动列表").pack()
        self.txt_act = scrolledtext.ScrolledText(frm_left, wrap=tk.WORD, font=("Consolas",9))
        self.txt_act.pack(fill=tk.BOTH, expand=True)
        frm_right = ttk.Frame(frm_split)
        frm_right.pack(side=tk.RIGHT, fill=tk.BOTH, expand=False, padx=(6,0))
        ttk.Label(frm_right, text="✅ 已加入抢报队列（删除看这里）").pack()
        self.txt_queue = scrolledtext.ScrolledText(frm_right, wrap=tk.WORD, font=("Consolas",9))
        self.txt_queue.pack(fill=tk.BOTH, expand=True)
        # 当前界面展示（筛选后）的活动列表快照，加入队列时序号以它为准
        self.current_show_list = []
        self.poll_log()
        self.poll_act_table()
    def apply_log_cfg(self):
        try:
            new_max = int(self.var_max_log.get())
            new_int = int(self.var_log_interval.get())
            if new_max > 0 and new_int > 20:
                self.log_deque = deque(self.log_deque, maxlen=new_max)
                self.log_poll_interval = new_int
                logger.info(f"✅ 日志配置更新：最大条数={new_max}, 刷新间隔={new_int}ms")
            else:
                logger.warning("❌ 数值必须大于0，间隔至少20ms")
        except ValueError:
            logger.warning("❌ 输入必须是数字")
    def on_close_all(self):
        exit_flag.set()
        self.win_log.destroy()
        self.win_act.destroy()
    def on_refresh(self):
        try:
            day_cnt = int(self.var_fetch_day.get())
        except ValueError:
            day_cnt = FETCH_DAY_DEFAULT
        day_cnt = max(1, min(day_cnt, FETCH_DAY_MAX))
        self.var_fetch_day.set(str(day_cnt))
        enqueue_user_event(("refresh", day_cnt))
    def on_add_task(self):
        raw = self.var_add.get().strip()
        if not raw:
            return
        show_list = getattr(self, "current_show_list", []) or []
        if not show_list:
            logger.warning("加入队列：当前还没有活动列表，请先点【①刷新活动列表】")
            self.var_add.set("")
            return
        try:
            idx_list = [int(x) for x in raw.split()]
        except ValueError:
            logger.warning("加入队列：输入必须是数字，多个用空格隔开")
            self.var_add.set("")
            return
        # 按界面上看到的序号（从1开始）取活动，再转成活动ID传给后台，避免筛选后序号错位
        ids = []
        bad_idx = []
        for idx in idx_list:
            pos = idx - 1
            if 0 <= pos < len(show_list):
                aid = show_list[pos].get("id")
                if aid is not None:
                    ids.append(aid)
            else:
                bad_idx.append(idx)
        if bad_idx:
            logger.warning(f"加入队列：序号 {bad_idx} 超出范围（当前筛选列表共 {len(show_list)} 条，序号从1开始）")
        if ids:
            enqueue_user_event(("add", ids))
        self.var_add.set("")
    def on_del_task(self):
        raw = self.var_del.get().strip()
        if not raw:
            return
        try:
            idx_list = [int(x) for x in raw.split()]
        except ValueError:
            logger.warning("删除队列：输入必须是数字，多个用空格隔开")
            self.var_del.set("")
            return
        # 界面上队列序号从1开始，这里换算成任务列表下标
        enqueue_user_event(("del", [x - 1 for x in idx_list]))
        self.var_del.set("")
    def poll_log(self):
        while True:
            try:
                line = gui_log_queue.get_nowait()
                self.log_deque.append(line)
            except Empty:
                break
        # 处理弹窗消息
        while True:
            try:
                item = user_event_queue.get_nowait()
                if item[0] == "popup_msg":
                    _, title, msg = item
                    tk.messagebox.showinfo(title,msg)
                else:
                    user_event_queue.put(item)
                    break
            except Empty:
                break
        self.txt_log.config(state=tk.NORMAL)
        self.txt_log.delete("1.0", tk.END)
        self.txt_log.insert(tk.END, "\n".join(self.log_deque))
        self.txt_log.see(tk.END)
        self.txt_log.config(state=tk.DISABLED)
        self.win_log.after(self.log_poll_interval, self.poll_log)
    def poll_act_table(self):
        payload = None
        try:
            payload = act_table_queue.get_nowait()
        except Empty:
            pass
        if payload is not None:
            valid_activities_raw, dept_dict, detail_cache, task_list, worker_threads, time_offset_ms = payload
            global all_college_list
            if len(all_college_list) >0:
                college_names = ["全部"] + [item["name"] for item in all_college_list]
                self.cb_college["values"] = college_names
            else:
                college_set = {"全部"}
                for it in valid_activities_raw:
                    d = detail_cache[it["id"]]["data"]
                    clist = d.get("collegeList",[])
                    for c in clist:
                        cname = c.get("name","未知学院")
                        if cname.endswith("学院"):
                            college_set.add(cname)
                self.cb_college["values"] = sorted(list(college_set))
            sel_college = self.var_college_filter.get()
            sel_cat = self.var_cat_filter.get()
            sel_college_strip = sel_college.strip()
            show_list = []
            for it in valid_activities_raw:
                d = detail_cache[it["id"]]["data"]
                clist_name = [x.get("name","").strip() for x in d.get("collegeList",[])]
                sign_limit = d.get("signLimit", 0)
                ok_college = True
                if sel_college != "全部":
                    # signLimit=0不限学院 / collegeList为空也视为不限学院
                    if sign_limit == 0 or len(clist_name) == 0:
                        ok_college = True
                    else:
                        ok_college = sel_college_strip in clist_name
                ok_cat = True
                if sel_cat != "全部":
                    act_cat = d.get("classifyName") or d.get("categoryName","无分类")
                    ok_cat = (act_cat == sel_cat)
                if ok_college and ok_cat:
                    show_list.append(it)
            # 保存界面可见（筛选后）列表，供【②加入队列】按显示序号索引
            self.current_show_list = list(show_list)
            lines = []
            lines.append("="*85)
            lines.append(f"📊 状态｜队列:{len(task_list)} 活跃线程:{len(worker_threads)} 偏移:{time_offset_ms}ms")
            lines.append(f"🎯筛选｜学院:{sel_college} | 类型:{sel_cat}")
            if not show_list:
                lines.append("本轮没有活动")
            else:
                now_ts_local = int(time.time()*1000)+time_offset_ms
                for index, item in enumerate(show_list, start=1):
                    aid = item.get("id")
                    name = item.get("name")
                    enrollable = item.get("isAbleEnroll", 0)
                    enroll_start_ts = item.get("enrollStartTime")
                    peopleLimit = item.get("peopleLimit", 0)
                    enrollCount = item.get("enrollCount", 0)
                    detail = detail_cache[aid]["data"]
                    enroll_end_ts = detail.get("enrollEndTime", item.get("enrollEndTime",0))
                    is_end = bool(enroll_end_ts and now_ts_local >= enroll_end_ts)
                    is_full = bool(peopleLimit>0 and enrollCount >= peopleLimit)
                    status_mark = ""
                    if is_end:
                        status_mark += "⛔已截止 "
                    if is_full and not is_end:
                        status_mark += "⚠名额已满 "
                    sign_limit = detail.get("signLimit", 0)
                    college_raw_list = detail.get("collegeList", [])
                    college_show = []
                    for c in college_raw_list:
                        cid = c.get("id")
                        cname = c.get("name")
                        if cname:
                            college_show.append(cname)
                        elif cid and int(cid) in dept_dict:
                            college_show.append(dept_dict[int(cid)])
                        else:
                            college_show.append(f"未知({cid})")
                    limit_str = f"限院:{','.join(college_show)}" if (sign_limit ==1 and college_show) else "不限学院"
                    audit_str = "审核" if detail.get("signAudit") ==1 else "免审"
                    work_str = "交作业" if detail.get("isSubmitWork") ==1 else "无作业"
                    org_str = detail.get("organizationName", "未知")
                    act_start_ts = detail.get("startTime", item.get("startTime"))
                    act_end_ts = detail.get("endTime", item.get("endTime"))
                    act_start = fmt_ts(act_start_ts)
                    act_end = fmt_ts(act_end_ts)
                    enroll_end = fmt_ts(enroll_end_ts)
                    enroll_start_show = fmt_ts(enroll_start_ts)
                    address = detail.get("address", item.get("address", "无地点"))
                    credit_raw = detail.get("credit",0)
                    credit = credit_raw /100 if credit_raw else 0
                    cat = detail.get("classifyName") or detail.get("categoryName", "无分类")
                    base_status = "🟢可报" if enrollable ==1 else ("🟡倒计时" if enroll_start_ts else "⚪未开")
                    in_queue = " [队列]" if aid in {t["id"] for t in task_list} else ""
                    lines.append(f"[{index}] {base_status} {status_mark}{name}{in_queue}")
                    lines.append(f"    名额：{enrollCount}/{peopleLimit} | {limit_str} | {audit_str} | {work_str}")
                    lines.append(f"    类型：{cat} | 学分：{credit} | 地点：{address}")
                    lines.append(f"    承办：{org_str}")
                    lines.append(f"    报名：{enroll_start_show} ~ {enroll_end}")
                    lines.append(f"    活动：{act_start} ~ {act_end}")
                    lines.append("")
            lines.append("="*85)
            lines.append("说明：序号从1开始，输入多个序号用空格隔开；下拉筛选框切换自动刷新生效；⚠满额活动自动作为蹲守任务")
            self.txt_act.config(state=tk.NORMAL)
            self.txt_act.delete("1.0", tk.END)
            self.txt_act.insert(tk.END, "\n".join(lines))
            self.txt_act.see("1.0")
            self.txt_act.config(state=tk.DISABLED)
            q_lines = []
            q_lines.append("序号 | 类型 | 活动名称（序号从1开始）")
            q_lines.append("-"*50)
            if not task_list:
                q_lines.append("暂无任务")
            else:
                for q_idx, tsk in enumerate(task_list, start=1):
                    ttype = tsk.get("task_type","normal")
                    ttag = "[普通]" if ttype=="normal" else "[蹲守]"
                    q_lines.append(f"[{q_idx}] {ttag}  {tsk['name']}")
            q_lines.append("\n👉 删除队列填此处左边序号！")
            self.txt_queue.config(state=tk.NORMAL)
            self.txt_queue.delete("1.0", tk.END)
            self.txt_queue.insert(tk.END, "\n".join(q_lines))
            self.txt_queue.see("1.0")
            self.txt_queue.config(state=tk.DISABLED)
        self.win_act.after(180, self.poll_act_table)
if __name__ == "__main__":
    backend_th = threading.Thread(target=backend_loop, daemon=True)
    backend_th.start()
    rt = tk.Tk()
    app = DualWindowGUI(rt)
    rt.mainloop()
    exit_flag.set()
    backend_th.join(timeout=3)
#因为pyinstaller打包有问题（浏览器打不开），所以只能用python跑了。致歉
