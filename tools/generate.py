#!/usr/bin/env python3
"""HOT 站点生成器：拉取 RSS -> 去重 -> 规则打分 -> 生成静态站。

只用 Python 标准库（urllib + xml.etree），不依赖任何外部包，也不依赖
大模型 API 或数据库；数据层就是 data/ 下的 JSON 文件。

流水线（参考 AIHOT 的信息架构：采集 -> 判重 -> 评分 -> 精选 -> 日报，
但全部落成静态文件，供 GitHub Pages 托管、定时任务驱动更新）：
  1. 拉取 sources.json 里的公开 RSS/Atom（只读标题+摘要+链接，不转载全文）
  2. 按规范化链接去重，与 data/store.json 里的本地历史合并（增量更新；store.json 不推送）
  3. 规则打分：时间新鲜度 + 信源分级 + 主题关键词（config.json 可调）
  4. 产出 data/hot.json（热点榜 Top 20）、data/days/（按天分块）与 index.html
  5. 带 --daily 时额外产出 data/daily.json 与 daily.html（当日日报）

可选 LLM 打分：只有同时设置 HOT_LLM_API_KEY、HOT_LLM_BASE_URL、
HOT_LLM_MODEL 三个环境变量时才启用；任何失败都静默回退到规则分，
且绝不把 Key 写进代码、配置或输出文件。
"""

import argparse
import hashlib
import html
import json
import os
import re
import sys
import time
import urllib.request
import urllib.error
import urllib.parse
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime

CST = timezone(timedelta(hours=8))
UA = {"User-Agent": "HOTBot/1.0"}

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# ---- 双语（中/英）全局状态：每写一页前由 main() 按语言与深度设置 ----
PAGE_LANG = "zh"       # "zh" | "en"
ASSET_BASE = ""        # 到站根的资源前缀：根页 ""，中文子目录 "../"，en 根页 "../"，en 子目录 "../../"
PAGE_BASE = ""         # 到本语言根的页面前缀：根页 ""，子目录 "../"
CAT_LABEL_EN = {}      # 分类 key -> label_en，main() 里由 config 填
CAT_LABEL_EN_BY_ZH = {}  # 分类中文 label -> label_en，main() 里由 config 填


# ---------------------------------------------------------------- 工具函数

def load_json(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def save_json(path, data, compact=False):
    # 写 JSON（原子替换）。compact=True 时写紧凑单行，省体积（分块数据与 hot.json 用）。
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        if compact:
            json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
        else:
            json.dump(data, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


def strip_html(text):
    if not text:
        return ""
    text = re.sub(r"<[^>]+>", " ", text)
    text = html.unescape(text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def title_from_text(text, limit=70):
    """无 <title> 的 feed（如 Mastodon 标签 RSS）用正文首句作标题：
    去掉开头的 Re: 与裸链接/域名串、去掉末尾的 hashtag 串，截到词边界；
    剩不下有效文字时返回空（调用方跳过该条）。"""
    text = (text or "").strip()
    text = re.sub(r"^(re:\s*)?(https?://\s*)?", "", text, flags=re.I)
    toks = text.split(" ")
    drop = 0
    for t in toks:
        if (t.startswith("http") or "://" in t
                or re.match(r"^[\w-]+(\.[\w-]+)+/\S*$", t)
                or "%3A" in t or "%2F" in t or t.startswith("www.")):
            drop += 1
        else:
            break
    text = " ".join(toks[drop:]).strip()
    text = re.sub(r"(?:\s+#[^\s#]+)+\s*$", "", text)
    text = re.sub(r"\s+", " ", text).strip()
    if len(text) < 8:
        return ""
    if len(text) <= limit:
        return text
    cut = text[:limit]
    for sep in (" ", "，", "、", "。"):
        i = cut.rfind(sep)
        if i > limit // 2:
            return cut[:i].rstrip()
    return cut.rstrip()


def shorten(text, limit=200):
    if len(text) <= limit:
        return text
    return text[:limit].rstrip() + "…"


SENT_END = "。！？.!?"
CLAUSE_END = "，、；：,;:；"
CLOSE_CHARS = "）】」』\"'”’"


def complete_para(text, limit=1500):
    """把一段摘要收成完整的一段话：不超过 limit，以句末标点收尾，不加省略号。
    详情页导读/正文摘要用：不允许截断到半句、末尾挂 …。
    已在限制内且以句末标点结尾的原样返回；否则退到 limit 内最后一个完整句；
    无完整句时退到最后一个分句标点；再无则硬截（仍不加 …）。"""
    text = (text or "").strip()
    if not text:
        return ""
    if text.endswith("…"):
        text = text[:-1].rstrip()
    if not text:
        return ""
    if len(text) <= limit and text[-1] in SENT_END:
        return text
    cut = text[:limit] if len(text) > limit else text
    best = -1
    for i, ch in enumerate(cut):
        if ch not in SENT_END:
            continue
        # ASCII 句点夹在数字之间是版本号/小数（如 4.8），不是句末
        if ch == "." and i > 0 and i + 1 < len(cut) \
                and cut[i - 1].isdigit() and cut[i + 1].isdigit():
            continue
        j = i + 1
        while j < len(cut) and cut[j] in CLOSE_CHARS:
            j += 1
        best = j
    if best > 0:
        return cut[:best].rstrip()
    for i in range(len(cut) - 1, -1, -1):
        if cut[i] in CLAUSE_END:
            return cut[:i + 1].rstrip()
    return cut.rstrip()


def norm_link(link):
    """去 fragment 与 utm_* 追踪参数，供去重用。"""
    link = (link or "").strip().split("#")[0]
    if "?" in link:
        base, qs = link.split("?", 1)
        kept = [p for p in qs.split("&") if p and not p.lower().startswith("utm_")]
        link = base + ("?" + "&".join(kept) if kept else "")
    return link.rstrip("/")


def parse_date(text):
    """RSS 的 RFC 2822 与 Atom 的 ISO 8601 都接受；失败返回 None。"""
    if not text:
        return None
    text = text.strip()
    try:
        dt = parsedate_to_datetime(text)
        if dt is not None:
            return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
    except (TypeError, ValueError):
        pass
    try:
        dt = datetime.fromisoformat(text.replace("Z", "+00:00"))
        return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def fmt_cst(dt):
    dt = dt.astimezone(CST)
    if PAGE_LANG == "en":
        return f"{MONTHS_EN[dt.month - 1]} {dt.day} {dt.strftime('%H:%M')}"
    return dt.strftime("%m月%d日 %H:%M")


def disp_zh_date(s):
    """把中文日期串翻成英文（英文站用）：'2026年11月17日 09:07' -> 'Nov 17, 2026 09:07'，
    '2026年11月17日' -> 'Nov 17, 2026'，'2026年第47周' -> 'Week 47, 2026'，
    '2026年11月' -> 'November 2026'，'11月16日' -> 'Nov 16'；中文站原样返回。"""
    if PAGE_LANG == "zh":
        return s
    for fmt, out in (("%Y年%m月%d日 %H:%M", lambda d: f"{MONTHS_EN[d.month - 1]} {d.day}, {d.year} {d.strftime('%H:%M')}"),
                     ("%Y年%m月%d日", lambda d: f"{MONTHS_EN[d.month - 1]} {d.day}, {d.year}"),
                     ("%Y年%m月", lambda d: f"{MONTHS_EN[d.month - 1]} {d.year}"),
                     ("%m月%d日", lambda d: f"{MONTHS_EN[d.month - 1]} {d.day}")):
        try:
            return out(datetime.strptime(s, fmt))
        except ValueError:
            continue
    if "年第" in s and s.endswith("周"):
        y, rest = s.split("年第", 1)
        return f"Week {int(rest[:-1])}, {y}"
    return s


def local_name(tag):
    return tag.rsplit("}", 1)[-1]


# ---------------------------------------------------------------- 抓取与解析

def fetch(url, timeout=25, attempts=2):
    last_err = None
    for i in range(attempts):
        try:
            req = urllib.request.Request(url, headers=UA)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except (urllib.error.URLError, TimeoutError, OSError) as e:
            last_err = e
            if i < attempts - 1:
                time.sleep(5)
    raise last_err


def parse_feed(body, source):
    """RSS 2.0 与 Atom 1.0 都解析，返回条目 dict 列表。"""
    try:
        root = ET.fromstring(body)
    except ET.ParseError:
        return []
    items = []
    for el in root.iter():
        name = local_name(el.tag)
        if name not in ("item", "entry"):
            continue
        fields = {}
        for child in el:
            cn = local_name(child.tag)
            if cn in ("title", "link", "pubDate", "published", "updated",
                      "description", "summary", "content", "encoded"):
                if cn == "link":
                    href = child.get("href")
                    # Atom: <link href="..."/>；RSS: <link>url</link>
                    fields.setdefault("link", href or (child.text or "").strip())
                else:
                    fields.setdefault(cn, (child.text or "").strip())
        title = fields.get("title", "").strip()
        link = norm_link(fields.get("link", ""))
        summary = strip_html(fields.get("description") or fields.get("summary") or "")
        if not summary:
            summary = strip_html(fields.get("content") or fields.get("encoded") or "")
        if not title:
            # 无 <title> 的 feed（如 Mastodon 标签 RSS）：用正文首句作标题
            title = title_from_text(summary)
        if not title or not link:
            continue
        # 完整摘要：详情页用（卡片仍用 200 字短摘要）。只有比短摘要明显更长时
        # 才存，短摘要本身已完整的条目不存，省体积。收成完整的一段话，
        # 不截断到半句、不挂省略号（导读/正文摘要不允许截断）。
        summary_full = complete_para(summary, 1500) if len(summary) > 200 else ""
        pub = parse_date(fields.get("pubDate") or fields.get("published")
                         or fields.get("updated"))
        item = {
            "title": title,
            "link": link,
            "source": source["name"],
            "source_id": source["id"],
            "published": pub,  # datetime 或 None（调用方补抓取时间）
            "summary": shorten(summary),
        }
        if summary_full:
            item["summary_full"] = summary_full
        items.append(item)
    return items


# ---------------------------------------------------------------- 分类与打分

def classify(item, categories, fallback):
    text = (item["title"] + " " + item["summary"]).lower()
    for cat in categories:
        for kw in cat["keywords"]:
            if kw.lower() in text:
                return cat["key"]
    return fallback


def score(item, cfg, now):
    sc = cfg["scoring"]
    total = sc["base"]
    age_h = (now - item["_pub"]).total_seconds() / 3600.0
    for rule in sc["recency"]:
        if age_h <= rule["max_hours"]:
            total += rule["bonus"]
            break
    total += sc["tier_bonus"].get(item["_tier"], 0)
    text = (item["title"] + " " + item["summary"]).lower()
    dev_hits = sum(1 for kw in sc["dev_keywords"] if kw.lower() in text)
    total += min(dev_hits * sc["dev_keyword_bonus"], sc["dev_keyword_cap"])
    noise_hits = sum(1 for kw in sc["noise_keywords"] if kw.lower() in text)
    total += max(noise_hits * sc["noise_keyword_penalty"], sc["noise_keyword_floor"])
    return max(0, min(100, total))


# 主题关键词 -> 中文标签（推荐理由里只出现中文，不漏英文关键词）
REASON_LABELS = {
    "教程": "教程", "tutorial": "教程",
    "工具": "工具", "tool": "工具",
    "数据": "数据", "data": "数据",
    "案例": "案例", "case study": "案例",
    "开源": "开源", "open source": "开源",
    "指南": "指南", "guide": "指南",
    "复盘": "复盘", "postmortem": "复盘",
    "引擎": "引擎", "engine": "引擎",
    "优化": "优化", "optimization": "优化",
    "性能": "性能", "performance": "性能",
    "收入": "营收", "revenue": "营收",
    "销量": "销量", "sales": "销量",
    "经验": "经验教训", "教训": "经验教训", "lesson": "经验教训",
    "源码": "源码", "source code": "源码",
    "工作流": "工作流", "workflow": "工作流",
}


# 中文标签 -> 主题页 slug（B11/B16；与 REASON_LABELS 的值一一对应）
TAG_SLUGS = {
    "教程": "tutorial", "工具": "tools", "数据": "data", "案例": "case-study",
    "开源": "open-source", "指南": "guide", "复盘": "postmortem",
    "引擎": "engine", "优化": "optimization", "性能": "performance",
    "营收": "revenue", "销量": "sales", "经验教训": "lessons",
    "源码": "source-code", "工作流": "workflow",
}


# 中文标签 -> 英文显示（推荐理由 / 主题标签的英文版；英文标签本身不在表里，原样显示）
LABEL_EN = {
    "教程": "Tutorials", "工具": "Tools", "数据": "Data", "案例": "Case studies",
    "开源": "Open source", "指南": "Guides", "复盘": "Postmortems",
    "引擎": "Engines", "优化": "Optimization", "性能": "Performance",
    "营收": "Revenue", "销量": "Sales", "经验教训": "Lessons",
    "源码": "Source code", "工作流": "Workflows",
    "模型": "Model", "电话": "Call", "订阅": "Subscription", "隐私": "Privacy",
    "手表": "Watch", "安全": "Security", "语音": "Voice",
    "评测": "Reviews", "实测": "Hands-on tests", "体验": "Experiences", "提示词": "Prompts",
}


# 信源英文名（sources.json 不动，英文名放这里；en 页来源行 / JSON-LD / 搜索数据用）
SOURCE_NAME_EN = {
    "meta-newsroom": "Meta Newsroom",
    "techcrunch-muse": "TechCrunch: Muse",
    "hnrss-muse": "Hacker News: Muse",
    "hnrss-muse-agent": "Hacker News: Muse agent",
    "ars-muse": "Ars Technica: Muse",
    "medium-muse": "Medium: Muse",
    "medium-meta-muse": "Medium: Meta Muse",
    "googlenews-muse-meta-en": "Google News: Muse Meta AI",
    "googlenews-meta-muse-en": "Google News: Meta Muse",
    "googlenews-muse-meta-zh": "Google News: Muse Meta (Chinese)",
    "reddit-museagent": "Reddit: r/MuseAgent",
    "reddit-museassistant": "Reddit: r/MuseAssistant",
    "hn-show-muse": "Hacker News: Show HN Muse",
    "hn-ask-muse": "Hacker News: Ask HN Muse",
    "the-decoder-muse": "The Decoder: Muse",
    "zenn-muse": "Zenn: Muse",
    "qiita-muse": "Qiita: Muse",
    "simonwillison-muse": "Simon Willison: Muse",
    "unite-ai": "Unite.AI",
    "ship-with-muse": "Ship with Muse",
    "awesome-muse-commits": "awesome-muse commits",
    "gizmodo-muse": "Gizmodo: Muse",
    "siliconangle-muse": "SiliconANGLE: Muse",
    "hnrss-muse-ember": "Hacker News: Muse Ember",
    "reddit-museai": "Reddit: r/MuseAI",
    "muse-gadget-sdk-commits": "Muse gadget SDK commits",
    "googlenews-muse-ember-en": "Google News: Muse Ember",
    "googlenews-muse-spaces-en": "Google News: Muse Spaces",
    "googlenews-muse-app-en": "Google News: Muse app",
    "youtube-muse-official": "YouTube: Muse official channel",
    "404media-muse": "404 Media: Muse",
    "the-product-channel": "The Product Channel",
    "ai-supremacy": "AI Supremacy",
    "interconnects": "Interconnects",
    "latent-space": "Latent Space",
    "googlenews-muse-ai-assistant-en": "Google News: Muse AI assistant",
    "googlenews-muse-ai-agent-en": "Google News: Muse AI agent",
    "googlenews-muse-zhushou-zh": "Google News: Muse assistant (Chinese)",
    "googlenews-muse-zhinengti-zh": "Google News: Muse AI agent (Chinese)",
    "googlenews-muse-whatsapp-en": "Google News: Muse WhatsApp",
    "sgl-muse-mega-commits": "sgl-muse-mega commits",
    "youtube-setup-your-ai-assistant": "YouTube: Setup Your AI Assistant",
}


def disp_source(it):
    """来源显示名：英文站用英文名，中文站用源站名。"""
    if PAGE_LANG == "en":
        return SOURCE_NAME_EN.get(it.get("source_id", ""), it.get("source", ""))
    return it.get("source", "")


def disp_label(t):
    """标签显示：英文站用英文标签，中文站用原文。"""
    if PAGE_LANG == "en":
        return LABEL_EN.get(t, t)
    return t


def disp_site_title(site):
    """站标题：英文站用 config 的 title_en（未配时只留站名），中文站用 title。"""
    if PAGE_LANG == "en":
        return site.get("title_en") or site.get("name", "")
    return site.get("title", "")


def labels_for(item, cfg):
    """标题+摘要命中主题关键词 -> 去重后的中文标签（B16/C1 共用）。"""
    text = (item["title"] + " " + (item.get("summary") or "")).lower()
    labels = []
    for kw in cfg["scoring"]["dev_keywords"]:
        if kw.lower() in text:
            lab = REASON_LABELS.get(kw, kw)
            if lab not in labels:
                labels.append(lab)
    return labels


def reason_for(item, cfg, now):
    """从打分信号拼一句推荐理由（只用真实派生出的事实，不编造）：
    T1 信源 -> 官方来源；命中主题关键词 -> 中文标签（去重，最多两个）；
    6/24 小时内发布 -> 新鲜度；只有一条理由时补一条默认理由，保证每卡
    至少有两条可读信息。"""
    parts = []
    if item.get("_tier") == "T1":
        parts.append("官方来源")
    labels = labels_for(item, cfg)
    if labels:
        parts.append("涉及" + "与".join(labels[:2]))
    age_h = (now - item["_pub"]).total_seconds() / 3600.0
    if age_h <= 6:
        parts.append("6 小时内发布")
    elif age_h <= 24:
        parts.append("24 小时内发布")
    if len(parts) < 2:
        parts.append("与本主题相关")
    return " · ".join(parts)


def reason_for_en(item, cfg, now):
    """reason_for 的英文版：同一规则、同一信号，只换语言。"""
    parts = []
    if item.get("_tier") == "T1":
        parts.append("Official source")
    labels = labels_for(item, cfg)
    if labels:
        en_labels = [LABEL_EN.get(l, l) for l in labels[:2]]
        parts.append("About " + " and ".join(en_labels))
    age_h = (now - item["_pub"]).total_seconds() / 3600.0
    if age_h <= 6:
        parts.append("Published within 6 hours")
    elif age_h <= 24:
        parts.append("Published within 24 hours")
    if len(parts) < 2:
        parts.append("Related to this topic")
    return " · ".join(parts)


def translate_reason(reason):
    """把已存的中文推荐理由逐段译成英文（旧存档报告没有 reason_en 时用；新条目直接存 reason_en）。"""
    mapping = {
        "官方来源": "Official source",
        "6 小时内发布": "Published within 6 hours",
        "24 小时内发布": "Published within 24 hours",
        "与本主题相关": "Related to this topic",
    }
    out = []
    for part in (reason or "").split(" · "):
        if part in mapping:
            out.append(mapping[part])
        elif part.startswith("涉及"):
            labs = [LABEL_EN.get(l, l) for l in part[len("涉及"):].split("与") if l]
            out.append("About " + " and ".join(labs) if labs else part)
        else:
            out.append(part)
    return " · ".join(out)


def maybe_llm_rerank(items, site):
    """可选 LLM 打分：三个环境变量缺一即跳过；任何异常都回退规则分。"""
    key = os.environ.get("HOT_LLM_API_KEY", "")
    base = os.environ.get("HOT_LLM_BASE_URL", "").rstrip("/")
    model = os.environ.get("HOT_LLM_MODEL", "")
    if not (key and base and model):
        return items
    cands = items[:30]
    if not cands:
        return items
    try:
        import urllib.request as u
        listing = "\n".join(
            f'{i}. [{c["id"][:8]}] {c["title"]}（{c["source"]}）' for i, c in enumerate(cands))
        audience = site.get("audience", "读者")
        prompt = (f"你是{audience}社区的编辑。给下面每条动态按对{audience}的实用价值"
                  "打 0-100 分（教程、工具、数据、案例、深度分析高分；"
                  "纯资讯、促销低分）。只输出 JSON 数组，形如 "
                  '[{"id": "前8位id", "score": 82}]，不要其他文字。\n' + listing)
        payload = json.dumps({
            "model": model,
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0,
        }).encode("utf-8")
        req = u.Request(base + "/chat/completions", data=payload,
                        headers={"Authorization": "Bearer " + key,
                                 "Content-Type": "application/json"})
        with u.urlopen(req, timeout=60) as r:
            body = json.loads(r.read().decode("utf-8"))
        text = body["choices"][0]["message"]["content"]
        m = re.search(r"\[.*\]", text, re.S)
        if not m:
            return items
        for entry in json.loads(m.group(0)):
            for c in cands:
                if c["id"].startswith(entry.get("id", "x")) and \
                        isinstance(entry.get("score"), (int, float)):
                    c["score"] = max(0, min(100, int(entry["score"])))
                    c["scored_by"] = "llm"
        print("LLM rerank applied to %d items" % len(cands))
    except Exception as e:  # noqa: BLE001 - 任何 LLM 失败都回退规则分
        print("LLM rerank skipped (%s)" % e, file=sys.stderr)
    return items


# ---------------------------------------------------------------- 渲染

LOGO_SVG = """<svg width="44" height="44" viewBox="0 0 48 48" aria-hidden="true">
<defs><linearGradient id="lg" x1="0" y1="0" x2="1" y2="1">
<stop offset="0" stop-color="#ff6b35"/><stop offset="1" stop-color="#f7b733"/>
</linearGradient></defs>
<rect x="2" y="2" width="44" height="44" rx="11" fill="url(#lg)"/>
<rect x="14" y="14" width="20" height="20" rx="3" transform="rotate(45 24 24)" fill="#fff"/>
<rect x="20" y="20" width="8" height="8" rx="1.5" transform="rotate(45 24 24)" fill="#ff6b35"/>
</svg>"""

CSS = """
/* 设计语言：暖纸底色、青色点缀、细线边框、无渐变；
   侧栏导航、热点条、时间线时间轨、评分徽章均为其组件的静态化移植。品牌与 logo 由本站自己定义。 */
:root{
  --bg:#faf9f6; --bg-sunk:#f3f3ef; --bg-muted:#e9ede9; --well:var(--bg-sunk);
  --surface:#fff; --surface-2:#fdfdfb; --sidebar:#fdfdfb; --daybar:#f0f2ee;
  --ink:#202a30; --ink-2:#303c42; --ink-3:#59656b; --ink-4:#657176;
  --line:#dfe4e1; --line-strong:#d1d9d5; --line-soft:#e9ede9;
  --accent:#176b75; --accent-strong:#0f565e; --accent-ink:#145f68; --accent-soft:rgba(23,107,117,.08); --accent-softer:rgba(23,107,117,.05);
  --note:#526f72; --hot:#b3402a; --hot-soft:rgba(179,64,42,.08);
  --amber:#b8873a; --amber-ink:#7c5a24; --amber-soft:rgba(184,135,58,.1); --ok:#2f7d5c;
  --rank-1:#b3402a; --rank-2:#a3642f; --rank-3:#96702e; --rank-rest:#6b7684;
  --shadow-card:0 1px 2px rgba(32,42,48,.025);
  --shadow-card-hover:0 3px 12px rgba(32,42,48,.055);
  --shadow-thumb:0 1px 2px rgba(28,39,51,.1),0 1px 1px rgba(28,39,51,.04);
  --raised:#ffffff; --selection:rgba(23,107,117,.16); --shadow-soft:0 4px 12px rgba(28,39,51,.06);
  --accent-contrast:#ffffff; --ok-soft:rgba(47,125,92,.1); --ok-ink:#2a6e51;
  --shadow-pop:0 12px 32px rgba(28,39,51,.12); --prose-ink:#26323a;
  --code-bg:#f6f7f4; --code-keyword:#006d77; --code-string:#2f6f44; --code-number:#9a6700;
  --code-title:#6f42c1; --code-variable:#a13d10; --code-meta:#b42348;
  --page-max-wide:max(1200px,calc(270dvh - 236px));
  --page-max-reading:max(1100px,calc(200dvh - 236px));
  --bar-h:48px; color-scheme:light;
}
@media(min-width:700px){:root{--bar-h:0px}}
[data-theme="dark"]{
  color-scheme:dark;
  --bg:#13191c; --bg-sunk:#182024; --bg-muted:#202a2f; --well:color-mix(in oklab, var(--bg-muted) 60%, transparent);
  --surface:#1a2226; --surface-2:#1d272b; --sidebar:#161e21; --daybar:#182024;
  --ink:#e7eceb; --ink-2:#d2dada; --ink-3:#a5b0b3; --ink-4:#89979d;
  --line:rgba(255,255,255,.08); --line-strong:rgba(255,255,255,.12); --line-soft:rgba(255,255,255,.06);
  --accent:#12ccd8; --accent-strong:#0db2bd; --accent-ink:#2ce2e8; --accent-soft:rgba(18,204,216,.12); --accent-softer:rgba(18,204,216,.06);
  --note:#8fb8a8; --hot:#d86a52; --hot-soft:rgba(216,106,82,.12);
  --amber:#d3b26a; --amber-ink:#d3b26a; --amber-soft:rgba(211,178,106,.12); --ok:#5fc79a;
  --rank-1:#d86a52; --rank-2:#d18a5e; --rank-3:#d3b26a; --rank-rest:#7b869a;
  --shadow-card:none; --shadow-card-hover:none;
  --raised:#202a2f; --selection:rgba(18,204,216,.22); --shadow-soft:0 6px 18px rgba(0,0,0,.35);
  --shadow-thumb:0 1px 2px rgba(0,0,0,.45);
  --accent-contrast:#000000; --ok-soft:rgba(95,199,154,.12); --ok-ink:#7fd1ad;
  --shadow-pop:0 16px 40px rgba(0,0,0,.45); --prose-ink:#d7dfdf;
  --code-bg:#10151c; --code-keyword:#78dce8; --code-string:#a9dc76; --code-number:#ffd866;
  --code-title:#ab9df2; --code-variable:#fc9867; --code-meta:#ff6188;
}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%;text-rendering:optimizeLegibility;-webkit-font-smoothing:antialiased;text-autospace:normal}
body{margin:0;background:var(--bg);color:var(--ink);
  font-family:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI","PingFang SC","Hiragino Sans GB","HarmonyOS Sans SC","Microsoft YaHei",sans-serif;
  font-size:14px;line-height:1.5}
:root:not([data-theme="dark"]) body:has(.report-shell){background:color-mix(in srgb, var(--bg) 60%, var(--surface))}
::selection{background:var(--selection)}
a{color:inherit;text-decoration:none}
button{cursor:pointer;font:inherit}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px;border-radius:5px}
.num{font-variant-numeric:tabular-nums}
.mono{font-family:ui-monospace,SFMono-Regular,"SF Mono",Menlo,Consolas,monospace;font-variant-numeric:tabular-nums}

/* ---- 壳：侧栏 / 窄轨 / 主列 / 手机顶栏与底栏 ---- */
.shell{display:flex;min-height:100dvh}
.sidebar,aside.rail{display:none}
.main{flex:1;min-width:0}
/* 列表宽度：桌面撑满主列，上限 max(1200px, 270dvh-236px)，超宽屏再居中 */
.page{max-width:640px;width:100%;margin:0 auto;padding:0 16px 96px}
@media(min-width:700px){
  .page{max-width:var(--page-max-wide);padding:0 20px 48px}
}
@media(min-width:700px){
  aside.rail{display:flex;position:sticky;top:0;height:100dvh;width:64px;flex-shrink:0;
    flex-direction:column;align-items:center;border-right:1px solid var(--line);
    background:var(--sidebar);padding:20px 6px 14px}
}
@media(min-width:941px){
  .page{padding:0 28px 48px}
  aside.rail{display:none}
  .sidebar{display:flex;position:sticky;top:0;height:100dvh;width:180px;flex-shrink:0;
    flex-direction:column;border-right:1px solid var(--line);background:var(--sidebar);
    padding:24px 12px 14px}
}
.brand{display:flex;align-items:center;gap:10px;color:var(--ink)}
.brand b{font-size:20px;font-weight:700;letter-spacing:.01em}
.brand small{display:block;font-size:11px;color:var(--ink-4);font-weight:400}
.nav-sec{margin-top:14px}
.nav-sec h3{margin:0;padding:14px 10px 4px;font-size:11px;font-weight:400;color:var(--ink-4)}
.side-link{display:flex;height:40px;align-items:center;gap:10px;padding:0 10px;border-radius:8px;
  font-size:14px;font-weight:500;color:var(--ink-3)}
.side-link svg{flex-shrink:0}
.side-link:hover{background:var(--bg-sunk);color:var(--ink)}
.side-link.on{background:rgba(23,107,117,.10);font-weight:600;color:var(--ink)}
.side-link.on svg{color:var(--accent)}
.side-foot{margin-top:auto;padding-top:12px}
.side-foot .gh{display:flex;height:34px;align-items:center;justify-content:center;gap:6px;
  border:1px solid var(--line);border-radius:9999px;font-size:12.5px;color:var(--ink-3)}
.side-foot .gh:hover{background:var(--bg-sunk);color:var(--ink)}
.side-foot .theme-btn{width:100%;height:34px;margin-top:8px;border:1px solid var(--line);
  border-radius:9999px;background:transparent;color:var(--ink-3);font-size:12.5px}
.side-foot .theme-btn:hover{background:var(--bg-sunk);color:var(--ink)}
.side-foot .note{margin:10px 4px 0;font-size:11.5px;color:var(--ink-4);text-align:center}
.rail-link{display:flex;width:100%;height:56px;flex-direction:column;align-items:center;justify-content:center;
  gap:3px;border-radius:8px;font-size:11px;font-weight:500;color:var(--ink-3)}
.rail-link:hover{background:var(--bg-sunk);color:var(--ink)}
.rail-link.on{background:rgba(23,107,117,.10);font-weight:600;color:var(--ink)}
[data-theme="dark"] .side-link.on,[data-theme="dark"] .rail-link.on{background:var(--accent-soft)}
.rail-link.on svg{color:var(--accent)}
aside.rail .brand{margin-bottom:12px}

/* 手机顶栏：品牌 + 精选|全部切换 + 外观按钮 */
.topbar{position:sticky;top:0;z-index:30;display:flex;height:var(--bar-h);align-items:center;gap:8px;
  padding:0 8px;background:var(--bg);border-bottom:1px solid var(--line)}
.topbar .brand b{font-size:17px}
.switch{display:flex;margin:0 auto;background:var(--well);border-radius:9999px;padding:2px;box-shadow:inset 0 0 0 1px var(--line-soft)}
.switch a{padding:3px 14px;border-radius:9999px;font-size:13px;font-weight:500;color:var(--ink-3)}
.switch a.on{background:var(--surface);color:var(--ink);font-weight:600;box-shadow:var(--shadow-card)}
.topbar .title{margin:0 auto;font-size:15px;font-weight:600}
/* 语言切换：仿 .switch 药丸样式，顶栏与页脚共用 */
.lang-switch{display:inline-flex;align-items:center;gap:2px;padding:2px;border-radius:9999px;
  background:var(--well);box-shadow:inset 0 0 0 1px var(--line-soft);font-size:12.5px;font-weight:500;white-space:nowrap}
.lang-switch .on{padding:2px 10px;border-radius:9999px;background:var(--surface);color:var(--ink);
  font-weight:600;box-shadow:var(--shadow-card)}
.lang-switch a{padding:2px 10px;border-radius:9999px;color:var(--ink-3)}
.lang-switch a:hover{color:var(--accent)}
.topbar .lang-switch{flex-shrink:0}
.foot-links .lang-switch{margin-right:4px}
.icon-btn{display:inline-flex;width:36px;height:36px;align-items:center;justify-content:center;
  border:0;border-radius:8px;background:transparent;color:var(--ink-3)}
.icon-btn:hover{background:var(--bg-sunk);color:var(--ink)}
.ic-sun,.ic-monitor{display:none}

/* 手机底栏 */
.tabbar{position:fixed;left:0;right:0;bottom:0;z-index:30;display:flex;background:var(--surface);
  border-top:1px solid var(--line);padding-bottom:env(safe-area-inset-bottom)}
.tabbar a{flex:1;display:flex;flex-direction:column;align-items:center;gap:2px;padding:7px 0 6px;
  font-size:11px;font-weight:500;color:var(--ink-3)}
.tabbar a.on{color:var(--accent);font-weight:600}
/* 桌面（≥700px）只留侧栏/窄轨，手机顶栏与底栏隐藏（须放在基础规则之后，否则同优先级后规则覆盖） */
@media(min-width:700px){.topbar,.tabbar{display:none}}

/* ---- 通用组件 ---- */
h1{font-size:24px;font-weight:600;line-height:1.3;margin:22px 0 0}
h2.sec{font-size:19px;font-weight:600;margin:30px 0 12px}
.lede{font-size:13px;color:var(--ink-4);margin:8px 0 0}
.card{background:var(--surface);border:1px solid var(--line);border-radius:12px;box-shadow:var(--shadow-card)}
.chip{display:inline-flex;align-items:center;height:26px;padding:0 10px;border-radius:9999px;
  border:1px solid var(--line-soft);background:var(--bg-sunk);font-size:12px;color:var(--ink-4)}
button.chip:hover{color:var(--accent);border-color:var(--line-strong)}
.chip.on{background:var(--accent-soft);border-color:transparent;color:var(--accent-ink);font-weight:600}
.tabs{position:relative;display:inline-flex;gap:2px;overflow-x:auto;scrollbar-width:none;
  margin:0;padding:3px;border-radius:9999px;background:var(--well);box-shadow:inset 0 0 0 1px var(--line-soft)}
.tabs::-webkit-scrollbar{display:none}
.tabs .chip{position:relative;z-index:1;flex-shrink:0;height:36px;padding:0 16px;border:0;
  background:transparent;font-size:14px;font-weight:500;color:var(--ink-3);border-radius:9999px}
.tabs .chip:hover{color:var(--ink)}
.tabs .chip.on{color:var(--ink);font-weight:600}
.tabs-thumb{position:absolute;top:3px;bottom:3px;left:3px;width:0;border-radius:9999px;
  background:var(--surface);box-shadow:var(--shadow-thumb),inset 0 0 0 1px var(--line);
  transition:left 300ms cubic-bezier(.25,1,.5,1),width 300ms cubic-bezier(.25,1,.5,1)}
[data-theme="dark"] .tabs-thumb{background:var(--raised)}
[data-theme="dark"] .switch a.on{background:var(--raised)}
/* 筛选行：左侧分类分段控件，右侧搜索框 */
.filter-row{display:flex;flex-wrap:wrap;align-items:center;gap:12px;margin:16px 0 4px}
.filter-row .tabs{max-width:100%}
.search{position:relative;width:100%}
@media(min-width:700px){.search{width:240px;flex-shrink:0}}
.search svg{position:absolute;left:16px;top:50%;transform:translateY(-50%);color:var(--ink-4);pointer-events:none}
.search:focus-within svg{color:var(--ink-3)}
.search input{width:100%;height:42px;border:0;border-radius:9999px;background:var(--well);
  padding:0 40px 0 40px;font:inherit;font-size:16px;color:var(--ink);outline:none;
  box-shadow:inset 0 0 0 1px var(--line-soft)}
@media(min-width:640px){.search input{font-size:14px}}
.search input::placeholder{color:var(--ink-4)}
.search input:hover{box-shadow:inset 0 0 0 1px var(--line-strong)}
.search input:focus{background:var(--surface);box-shadow:0 0 0 3px var(--accent-soft),inset 0 0 0 1px var(--accent)}
.search .clear{position:absolute;right:12px;top:50%;transform:translateY(-50%);
  display:none;width:24px;height:24px;align-items:center;justify-content:center;
  border:0;border-radius:9999px;background:transparent;color:var(--ink-4)}
.search .clear:hover{background:var(--bg-sunk);color:var(--ink)}
.search.has-value .clear{display:inline-flex}
.search kbd{position:absolute;right:16px;top:50%;transform:translateY(-50%);display:none;
  font-family:ui-monospace,Menlo,Consolas,monospace;font-size:10.5px;line-height:16px;
  padding:0 6px;border:1px solid var(--line-strong);border-radius:5px;background:var(--surface);color:var(--ink-4)}
@media(min-width:700px){.search:not(.has-value) kbd{display:block}}
/* 只看未读：独立小开关（首个日期行右侧 / 手机单独一行） */
.toggle-chip{display:inline-flex;min-height:28px;align-items:center;gap:6px;padding:0 12px;
  border-radius:9999px;border:1px solid var(--line-soft);background:var(--bg-sunk);
  font-size:12.5px;font-weight:500;color:var(--ink-3)}
.toggle-chip:hover{color:var(--ink);border-color:var(--line-strong)}
.toggle-chip.on{background:var(--accent-soft);border-color:transparent;color:var(--accent-ink);font-weight:600}
.unread-row{display:flex;justify-content:flex-end;margin:10px 0 2px}
@media(min-width:700px){.unread-row{display:none}}
.well{background:var(--well);box-shadow:inset 0 0 0 1px var(--line-soft);border-radius:14px;padding:14px 16px}
.well .kicker{font-size:12px;font-weight:600;color:var(--accent-ink)}
.well p{margin:6px 0 0;font-size:14.5px;line-height:1.75;color:var(--ink-2)}

/* 评分徽章（按档位着色的小药丸，85+ 红、70+ 青、其余安静） */
.score-pill{display:inline-flex;height:20px;align-items:center;gap:6px;white-space:nowrap;
  border-radius:9999px;padding:0 8px;box-shadow:inset 0 0 0 1px var(--ring,rgba(0,0,0,0))}
.score-pill .lbl{font-size:11px;font-weight:500;opacity:.8}
.score-pill .sep{width:1px;height:10px;background:currentColor;opacity:.25}
.score-pill .num{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
  font-size:12.5px;font-weight:700;font-variant-numeric:tabular-nums}
.score-pill.t-hot{background:color-mix(in srgb, var(--hot) 10%, transparent);color:var(--hot);--ring:color-mix(in srgb, var(--hot) 25%, transparent)}
.score-pill.t-acc{background:var(--accent-soft);color:var(--accent);--ring:color-mix(in srgb, var(--accent) 20%, transparent)}
.score-pill.t-quiet{color:var(--ink-4);--ring:var(--line-soft)}
@media(max-width:640px){.score-pill .lbl,.score-pill .sep{display:none}}
/* 精选徽章：琥珀底 + 圆点（不是青色） */
.pick{display:inline-flex;height:18px;align-items:center;gap:4px;padding:0 8px;border-radius:9999px;
  background:var(--amber-soft);color:var(--amber-ink);font-size:11px;font-weight:500}
.pick::before{content:"";width:5px;height:5px;border-radius:9999px;background:currentColor}
/* 当日新到徽章：趋势列的“新”样式 */
.new-pill{display:inline-flex;height:18px;align-items:center;padding:0 6px;border-radius:9999px;
  background:var(--accent-soft);color:var(--accent);font-size:10.5px;font-weight:600;line-height:16px}
.rank{font-weight:800;color:var(--rank-rest)}
.rank.r1{color:var(--rank-1)}.rank.r2{color:var(--rank-2)}.rank.r3{color:var(--rank-3)}

/* ---- 动态卡片（桌面白卡、手机行；来源行 + 标题 + 摘要 + 分类） ---- */
.feed-item{padding:14px 0;border-bottom:1px solid var(--line-soft)}
.feed-item:last-child{border-bottom:0}
@media(min-width:700px){
  .feed-item{padding:15px 18px 14px;background:var(--surface);border:1px solid var(--line);
    border-radius:12px;box-shadow:var(--shadow-card);margin-bottom:12px;
    transition:box-shadow 200ms,border-color 200ms,transform 200ms}
  .feed-item:hover{box-shadow:var(--shadow-card-hover);border-color:var(--line-strong);transform:translateY(-1px)}
}
.fi-head{display:flex;min-height:20px;align-items:center;gap:8px;font-size:12.5px;color:var(--ink-4)}
.fi-head .src{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.fi-head .pt{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12px}
@media(min-width:700px){.fi-head .pt{display:none}}
.fi-head .sp{margin-left:auto;display:flex;align-items:center;gap:6px;flex-shrink:0}
.star-btn{display:inline-flex;width:44px;height:44px;align-items:center;justify-content:center;
  margin:-11px -12px -11px 0;border:0;border-radius:8px;background:transparent;color:var(--ink-4)}
.star-btn:hover{background:var(--bg-sunk);color:var(--ink-2)}
.star-btn.on{color:var(--accent)}
.star-btn.on svg{fill:currentColor}
@media(min-width:700px){.star-btn{width:26px;height:26px;margin:-1px 0}}
.feed-item h3{margin:6px 0 0;font-size:17px;font-weight:650;line-height:1.5}
@media(min-width:700px){.feed-item h3{line-height:1.55}}
.feed-item.is-read h3 a{color:var(--ink-4)}
.feed-item h3 a:hover{color:var(--accent)}
.feed-item h3 .rank{margin-right:8px;font-size:17px}
.feed-item .sum{margin:4px 0 0;font-size:14.5px;line-height:1.7;color:var(--ink-3);
  display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
@media(min-width:700px){.feed-item .sum{-webkit-line-clamp:3;font-size:15px;line-height:1.75}}
.fi-foot{margin-top:8px;display:flex;gap:8px;align-items:center}
.fi-foot .when{font-size:12.5px;color:var(--ink-4)}
/* 推荐理由：13px、注色，桌面加顶线与间距 */
.fi-reason{margin-top:4px;font-size:13px;line-height:1.65;color:var(--note);
  display:-webkit-box;-webkit-line-clamp:1;-webkit-box-orient:vertical;overflow:hidden}
@media(min-width:700px){
  .fi-reason{margin-top:12px;padding-top:12px;border-top:1px solid var(--line-soft);
    -webkit-line-clamp:unset;line-height:1.75}
}

/* ---- 热点条（右上热色晕染 + 跳动 live 点 + 排名行） ---- */
.hot-card{position:relative;overflow:hidden;margin:16px 0 0;padding:10px 14px 4px;
  background:radial-gradient(120% 90% at 100% 0%,var(--hot-soft),transparent 55%),var(--surface)}
@media(min-width:700px){.hot-card{margin:18px 0 24px;padding:14px 20px 8px}}
.hot-head{display:flex;align-items:center;justify-content:space-between}
.hot-head h2{display:flex;align-items:center;gap:8px;margin:0;font-size:14px;font-weight:600}
.live{position:relative;display:inline-flex;width:8px;height:8px}
.live .ping{position:absolute;width:100%;height:100%;border-radius:9999px;background:var(--hot);opacity:.4;animation:ping 1.6s ease-out infinite}
.live .dot{position:relative;width:8px;height:8px;border-radius:9999px;background:var(--hot)}
@keyframes ping{0%{transform:scale(1);opacity:.4}80%,100%{transform:scale(2.4);opacity:0}}
.hot-more{display:inline-flex;align-items:center;gap:4px;border:0;background:transparent;
  font-size:12.5px;color:var(--ink-3);padding:6px 0}
.hot-more:hover{color:var(--accent)}
.hot-list{list-style:none;margin:2px 0 0;padding:0}
.hot-row{display:grid;grid-template-columns:20px minmax(0,1fr) 64px 20px;align-items:center;gap:12px;
  padding:7px 8px;margin:0 -8px;border-radius:10px}
.hot-row:hover{background:rgba(243,243,239,.7)}
[data-theme="dark"] .hot-row:hover{background:rgba(32,42,47,.4)}
.hot-row .rank{font-size:14px;font-weight:700;text-align:center}
.hot-row .rank.r1,.hot-row .rank.r2,.hot-row .rank.r3{font-size:15px;font-weight:900}
.hot-row .t{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:14.5px;font-weight:600}
@media(min-width:700px){.hot-row .t{font-size:14px}}
.hot-row:hover .t{color:var(--accent)}
.hot-heat{white-space:nowrap;font-size:12.5px;color:var(--ink-4);text-align:right}
.hot-heat b{font-size:13.5px;font-weight:600;color:var(--ink-2)}
.hot-trend{display:flex;width:20px;justify-content:center;color:var(--ink-4)}
.hot-trend .up{color:var(--hot)}
.hot-trend .flat{color:var(--ink-4)}
/* 手机只留前 3 名进榜，让动态流尽快出现在首屏 */
@media(max-width:639px){.hot-top5 li:nth-child(n+4){display:none}}

/* ---- 时间线（按天分组，桌面时间轨 + 青点，手机灰色日栏） ---- */
.day-head{position:sticky;top:var(--bar-h);z-index:20;display:flex;height:44px;align-items:center;gap:8px;
  margin:0 -16px;padding:0 16px;background:var(--daybar)}
.day-head .dh-name{font-size:14px;font-weight:700}
.day-head .dh-date{font-size:12.5px;color:var(--ink-4)}
.day-head .dh-wd{font-size:12.5px;color:var(--ink-4)}
.day-head .dh-count{margin-left:auto;font-size:12.5px;color:var(--ink-4)}
.day-head .dh-wd-full{display:none}
.day-head .dh-aside{display:none}
.day-head .dh-toggle{display:inline-flex;width:24px;height:24px;align-items:center;justify-content:center;
  flex-shrink:0;border:0;border-radius:9999px;background:transparent;color:var(--ink-4)}
.day-head .dh-toggle:hover{background:var(--bg-sunk);color:var(--ink)}
.day-head .dh-toggle svg{transition:transform 200ms}
.day-sec.collapsed .day-list{display:none}
.day-sec.collapsed .dh-toggle svg{transform:rotate(-90deg)}
@media(min-width:700px){
  .day-head{position:sticky;top:0;height:44px;margin:0;padding:0;background:var(--bg)}
  .day-head .dh-name{display:none}
  .day-head .dh-date{font-size:18px;font-weight:600;color:var(--ink)}
  .day-head .dh-wd{font-size:13px}
  .day-head .dh-wd-short{display:none}
  .day-head .dh-wd-full{display:inline}
  .day-head .dh-count{margin-left:0}
  .day-head .dh-aside{display:block;margin-left:auto}
}
.day-head:not(.is-today) .dh-date{display:none}
@media(min-width:700px){.day-head:not(.is-today) .dh-date{display:inline;font-size:18px;font-weight:600}}
.day-sec{margin-top:8px}
.day-list{list-style:none;margin:0;padding:0}
.slot{padding:14px 0;border-bottom:1px solid var(--line-soft)}
.slot:last-child{border-bottom:0}
.slot .slot-time,.slot .rail{display:none}
@media(min-width:700px){
  .slot{display:grid;grid-template-columns:64px 22px minmax(0,1fr);padding:0 0 12px;border-bottom:0}
  .slot .slot-time{display:block;padding-top:17px;font-family:ui-monospace,Menlo,Consolas,monospace;
    font-size:12.5px;font-weight:600;color:var(--ink-3)}
  .slot .rail{display:block;position:relative;width:auto;height:auto;background:transparent;padding:0;border:0}
  .slot .rail::before{content:"";position:absolute;left:10.5px;top:29px;bottom:-41px;width:1px;background:var(--line-strong)}
  .slot:last-child .rail::before{display:none}
  .slot .rail::after{content:"";position:absolute;left:7.5px;top:25.5px;width:7px;height:7px;
    border-radius:9999px;background:var(--accent);box-shadow:0 0 0 4px var(--bg)}
  .slot .feed-item{margin-bottom:0}
}

.foot{margin-top:36px;padding-top:14px;border-top:1px solid var(--line);font-size:13px;color:var(--ink-4)}
.foot p{margin:0 0 8px}
@media(max-width:699px){.foot{padding-bottom:8px}}
.tip{margin-top:20px;padding-top:16px;border-top:1px dashed var(--line);text-align:center}
.tip-cards{display:flex;flex-wrap:wrap;gap:8px 32px;justify-content:center}
.tip-card{max-width:300px}
.tip-title{font-size:13px;color:var(--ink-3)}
.tip-qr{width:150px;height:150px;border-radius:8px;background:#fff}
.tip-label{font-size:13px;color:var(--ink-3)}
.tip-addr{font-size:12px;color:var(--ink-4);word-break:break-all;font-family:ui-monospace,SFMono-Regular,Menlo,monospace}
/* 回到顶部：圆按钮，滚过一屏多再出现（仅桌面） */
.to-top{position:fixed;right:max(24px,env(safe-area-inset-right));bottom:max(24px,env(safe-area-inset-bottom));
  z-index:30;display:none;width:44px;height:44px;align-items:center;justify-content:center;
  border-radius:9999px;border:1px solid var(--line);background:var(--surface);color:var(--ink-2);
  box-shadow:var(--shadow-soft);transition:opacity 200ms,transform 200ms;
  opacity:0;transform:translateY(8px);pointer-events:none}
.to-top.show{opacity:1;transform:none;pointer-events:auto}
.to-top:hover{color:var(--ink)}
@media(min-width:700px){.to-top{display:flex}}
/* 列表到底 */
.feed-end{padding:24px 0;text-align:center;font-size:12px;color:var(--ink-4)}
/* 日报名头：大字名 + 双线，照报纸的版头 */
.masthead{margin-top:24px;padding-bottom:16px;border-bottom:3px double var(--line-strong)}
.masthead .mp-brand{display:flex;align-items:center;gap:14px}
.masthead .mp-meta{margin:10px 0 0;font-size:13px;color:var(--ink-4)}
.masthead .mp-issue{display:inline-flex;height:20px;align-items:center;padding:0 8px;border-radius:9999px;
  background:var(--accent-soft);color:var(--accent-ink);font-size:12px;font-weight:600;margin-left:10px}

/* ---- v9：视觉打磨与新页面（颜色 token 不动） ---- */
/* A2：标题手机 2 行截断；摘要桌面上边距 8px；头部行手机 22px/6px */
@media(max-width:699px){.feed-item h3{display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}}
@media(min-width:700px){.feed-item .sum{margin-top:8px}}
@media(max-width:699px){.fi-head{min-height:22px;gap:6px}}
/* A3：手机隐藏 h1，lede 只留“更新于 …” */
@media(max-width:699px){h1{display:none}.lede-rest{display:none}}
/* A4：手机大标题（与 A3 联动） */
.m-title{display:none}
@media(max-width:699px){.m-title{display:block;font-size:30px;font-weight:800;line-height:1.25;margin:18px 0 0}}
/* A4：顶栏/底栏毛玻璃；顶栏滚动阴影 */
.topbar{background:color-mix(in srgb, var(--bg) 85%, transparent);
  backdrop-filter:blur(20px) saturate(1.5);-webkit-backdrop-filter:blur(20px) saturate(1.5)}
.topbar.scrolled{box-shadow:0 1px 0 var(--line),0 6px 16px rgba(28,39,51,.08)}
.tabbar{background:color-mix(in srgb, var(--surface) 90%, transparent);
  backdrop-filter:blur(20px) saturate(1.5);-webkit-backdrop-filter:blur(20px) saturate(1.5)}
.tabbar-in{display:flex;width:100%;max-width:640px;margin:0 auto}
.tabbar-in a{flex:1}
/* A6：圆点悬停放大；卡片按压态 */
.slot .rail::after{transition:transform 300ms}
.slot:hover .rail::after{transform:scale(1.15)}
.feed-item:active{transform:scale(0.995)}
/* A7：手机 chip 44px；热点条“完整榜单”整行 40px */
@media(max-width:699px){.tabs .chip{height:44px}}
.hot-more{display:flex;min-height:40px;align-items:center;justify-content:center;gap:6px;
  border-top:1px solid var(--line-soft);margin-top:6px;padding:0;font-size:13px;color:var(--ink-3)}
/* A8：减弱动效时关掉动画 */
@media (prefers-reduced-motion: reduce){
  *,*::before,*::after{animation-duration:.01ms !important;animation-iteration-count:1 !important;
    transition-duration:.01ms !important;scroll-behavior:auto !important}
}
/* A10：日报页用更窄的阅读宽度 */
@media(min-width:700px){.page.page-reading{max-width:var(--page-max-reading)}}
/* B1：热点榜头条大卡 / 次卡 / Delta / 方法说明 */
.hot-hero{padding:18px 20px 16px;margin:16px 0 0}
.hot-hero-top{display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.no-tag{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12px;font-weight:800;
  letter-spacing:.06em;color:var(--rank-1)}
.hot-badge{display:inline-flex;height:18px;align-items:center;padding:0 8px;border-radius:9999px;
  font-size:11px;font-weight:600}
.hot-badge.b-new{background:var(--accent-soft);color:var(--accent)}
.hot-badge.b-hot{background:var(--hot-soft);color:var(--hot)}
.hot-badge.b-up{background:var(--amber-soft);color:var(--amber-ink)}
.hot-hero h2{margin:10px 0 0;font-size:20px;font-weight:700;line-height:1.45}
.hot-hero h2 a:hover{color:var(--accent)}
.hot-hero-meta{margin:6px 0 0;font-size:12.5px;color:var(--ink-4)}
.hot-hero-latest{margin:10px 0 0;font-size:14px;line-height:1.7;color:var(--ink-2)}
.hot-hero-latest .k{font-size:12px;font-weight:600;color:var(--accent-ink);margin-right:6px}
.hot-hero-foot{display:flex;align-items:flex-end;gap:14px;margin-top:14px;padding-top:12px;border-top:1px solid var(--line-soft)}
.hot-big{font-size:13px;color:var(--ink-4)}
.hot-big b{font-size:34px;font-weight:800;line-height:1;color:var(--ink);margin-right:4px;
  font-variant-numeric:tabular-nums}
.hot-hero-foot .score-pill{margin-left:auto}
.hot-sub-grid{display:grid;gap:12px;margin-top:12px}
@media(min-width:700px){.hot-sub-grid{grid-template-columns:1fr 1fr}}
.hot-sub{padding:14px 16px}
.hot-sub-top{display:flex;align-items:center;gap:8px}
.hot-sub h3{margin:8px 0 0;font-size:16px;font-weight:650;line-height:1.5}
.hot-sub h3 a:hover{color:var(--accent)}
.hot-sub-meta{margin:4px 0 0;font-size:12.5px;color:var(--ink-4)}
.hot-sub-foot{display:flex;align-items:center;gap:10px;margin-top:10px}
.hot-num{font-size:12.5px;color:var(--ink-4)}
.hot-num b{font-size:16px;font-weight:700;color:var(--ink-2);font-variant-numeric:tabular-nums}
.hot-delta{font-size:12.5px;font-weight:600;white-space:nowrap;font-variant-numeric:tabular-nums}
.hot-delta.up{color:var(--hot)}
.hot-delta.down{color:var(--ink-4)}
.hot-delta.new{color:var(--accent)}
.hot-delta.flat{color:var(--ink-4)}
.hot-row{grid-template-columns:20px minmax(0,1fr) 64px 56px 20px}
.hot-row .hot-delta{text-align:right}
.hot-method{margin-top:20px}
.hot-method p{margin:6px 0 0;font-size:13.5px;line-height:1.75;color:var(--ink-3)}
/* B19：卡片式空状态 */
.empty-state{margin:24px 0;padding:32px 20px;text-align:center;
  background:var(--surface);border:1px solid var(--line);border-radius:12px;box-shadow:var(--shadow-card)}
.empty-icon{display:flex;justify-content:center;color:var(--ink-4);margin-bottom:12px}
.empty-title{margin:0;font-size:16px;font-weight:650}
.empty-text{margin:8px 0 0;font-size:13.5px;color:var(--ink-4)}
.empty-actions{display:flex;gap:10px;justify-content:center;margin-top:18px;flex-wrap:wrap}
.empty-btn{display:inline-flex;min-height:36px;align-items:center;padding:0 18px;border-radius:9999px;
  border:1px solid var(--line-strong);background:var(--surface);font-size:13.5px;font-weight:500;color:var(--ink-2)}
.empty-btn:hover{border-color:var(--accent);color:var(--accent)}
.empty-btn.primary{background:var(--accent);border-color:transparent;color:var(--accent-contrast);font-weight:600}
.empty-btn.primary:hover{color:var(--accent-contrast);opacity:.9}
/* B14：手机搜索浮层（触发按钮只在手机显示） */
.search-trigger{display:flex;width:100%;height:42px;align-items:center;gap:10px;padding:0 16px;
  border:0;border-radius:9999px;background:var(--well);box-shadow:inset 0 0 0 1px var(--line-soft);
  font-size:16px;color:var(--ink-4);text-align:left}
@media(min-width:700px){.search-trigger{display:none}}
@media(max-width:699px){.filter-row .search{display:none}}
.search-overlay{position:fixed;inset:0;z-index:60;overflow-y:auto;background:var(--bg);padding:0 16px 48px}
.search-overlay .overlay-bar{position:sticky;top:0;z-index:1;display:flex;align-items:center;gap:8px;
  padding:12px 0;background:color-mix(in srgb, var(--bg) 90%, transparent);
  backdrop-filter:blur(20px) saturate(1.5);-webkit-backdrop-filter:blur(20px) saturate(1.5)}
.overlay-search{flex:1}
.overlay-sec{margin-top:20px}
.overlay-sec h3{margin:0 0 10px;font-size:13px;font-weight:600;color:var(--ink-4)}
.overlay-sec .recent-row{display:flex;align-items:center;gap:8px;margin-bottom:8px}
.overlay-sec .recent-row button{flex:1;text-align:left}
.overlay-sec .recent-clear{font-size:12.5px;color:var(--ink-4);border:0;background:transparent;padding:4px 0}
.overlay-sec .recent-clear:hover{color:var(--accent)}
.overlay-cats{display:flex;flex-wrap:wrap;gap:8px}
.overlay-hot{list-style:none;margin:0;padding:0}
.overlay-hot li{border-bottom:1px solid var(--line-soft)}
.overlay-hot li:last-child{border-bottom:0}
.overlay-hot a{display:flex;gap:10px;align-items:baseline;padding:10px 0;font-size:14.5px;font-weight:600}
.overlay-hot a:hover{color:var(--accent)}
.overlay-hot .rank{flex-shrink:0}
/* B15：三向主题切换（带滑动 thumb） */
.theme-seg{position:relative;display:inline-flex;gap:2px;padding:3px;border-radius:9999px;
  background:var(--well);box-shadow:inset 0 0 0 1px var(--line-soft)}
.theme-seg button{position:relative;z-index:1;display:inline-flex;height:36px;align-items:center;gap:6px;
  padding:0 14px;border:0;border-radius:9999px;background:transparent;font-size:13.5px;font-weight:500;color:var(--ink-3)}
.theme-seg button.on{color:var(--ink);font-weight:600}
.theme-seg-thumb{position:absolute;top:3px;bottom:3px;left:3px;width:0;border-radius:9999px;
  background:var(--surface);box-shadow:var(--shadow-thumb),inset 0 0 0 1px var(--line);
  transition:left 300ms cubic-bezier(.25,1,.5,1),width 300ms cubic-bezier(.25,1,.5,1)}
[data-theme="dark"] .theme-seg-thumb{background:var(--raised)}
/* B4/B6：我的页行 + 红点 */
.more-sec{margin-top:24px}
.more-sec h2{margin:0 0 8px;font-size:15px;font-weight:600}
.more-row{display:flex;align-items:center;gap:12px;width:100%;min-height:52px;padding:10px 14px;
  border:0;border-bottom:1px solid var(--line-soft);background:var(--surface);text-align:left;
  font-size:14.5px;font-weight:500;color:var(--ink)}
.more-row:first-of-type{border-top:1px solid var(--line-soft)}
.more-row:hover{background:var(--bg-sunk)}
.more-row svg{color:var(--ink-4);flex-shrink:0}
.more-row .m-label{flex:1}
.more-row .m-val{font-size:13px;color:var(--ink-4);font-weight:400}
.more-row .m-arrow{color:var(--ink-4)}
.dot-red{position:relative;display:inline-flex;width:8px;height:8px}
.dot-red::after{content:"";width:8px;height:8px;border-radius:9999px;background:var(--hot)}
.more-note{margin:10px 0 0;font-size:13px;line-height:1.7;color:var(--ink-4)}
.more-note a{color:var(--accent);text-decoration:underline}
/* B6/B8：更新日志与存档 */
.cl-item{padding:16px 0;border-bottom:1px solid var(--line-soft)}
.cl-item:last-child{border-bottom:0}
.cl-item h3{margin:0;font-size:16px;font-weight:650}
.cl-item .cl-date{font-size:12.5px;color:var(--ink-4);margin:4px 0 0}
.cl-item ul{margin:8px 0 0;padding-left:18px;font-size:14px;line-height:1.75;color:var(--ink-2)}
.arch-month{margin-top:20px}
.arch-month h3{margin:0 0 8px;font-size:15px;font-weight:600}
.arch-list{list-style:none;margin:0;padding:0}
.arch-list li{border-bottom:1px solid var(--line-soft)}
.arch-list li:last-child{border-bottom:0}
.arch-list a{display:flex;align-items:baseline;gap:10px;padding:10px 0;font-size:14.5px}
.arch-list a:hover{color:var(--accent)}
.arch-list .a-date{font-weight:600}
.arch-list .a-issue{font-size:12.5px;color:var(--ink-4)}
.arch-list .a-count{margin-left:auto;font-size:12.5px;color:var(--ink-4)}
/* 日报上下期导航 */
.daily-nav{display:flex;justify-content:space-between;gap:12px;margin-top:28px;padding-top:16px;border-top:1px solid var(--line)}
.daily-nav a{display:inline-flex;align-items:center;gap:6px;font-size:14px;font-weight:500;color:var(--ink-2)}
.daily-nav a:hover{color:var(--accent)}
.daily-nav .dn-next{margin-left:auto}
/* B3：收藏页下架条目置灰 */
.starred-item.is-gone{opacity:.55}
.starred-item .gone-tag{display:inline-flex;height:18px;align-items:center;padding:0 8px;border-radius:9999px;
  background:var(--bg-muted);color:var(--ink-4);font-size:11px;font-weight:500}
.starred-item .starred-at{font-size:12.5px;color:var(--ink-4)}
/* B13：同事件归组展开 */
.slot .group-toggle{grid-column:3;justify-self:start;margin:2px 0 0;padding:4px 10px;border:1px solid var(--line-soft);
  border-radius:9999px;background:var(--bg-sunk);font-size:12.5px;color:var(--ink-3)}
.slot .group-toggle:hover{color:var(--accent);border-color:var(--line-strong)}
.slot .group-extra{grid-column:3;margin-top:8px}
.group-extra-list{list-style:none;margin:0;padding:0}
.group-extra-list li{display:flex;gap:10px;align-items:baseline;padding:7px 0;border-top:1px solid var(--line-soft)}
.group-extra-list li:first-child{border-top:0}
.group-extra-list a{font-size:13.5px;font-weight:500}
.group-extra-list a:hover{color:var(--accent)}
.group-extra-list .ge-time{margin-left:auto;font-size:12px;color:var(--ink-4);white-space:nowrap}
/* B16：卡片标签 */
.fi-tags{display:flex;flex-wrap:wrap;gap:6px;margin-top:8px}
.fi-tags .tag{font-size:12px;color:var(--accent-ink);background:var(--accent-softer);
  border-radius:9999px;padding:2px 8px}
.fi-tags .tag:hover{background:var(--accent-soft)}
/* 详情页（items/:id）：阅读宽度 + 大标题 + 导读 + 操作行 */
.item-back{display:inline-flex;align-items:center;gap:6px;margin:4px 0 14px;padding:6px 12px 6px 8px;
  border:1px solid var(--line-soft);border-radius:9999px;background:var(--surface);
  font-size:13.5px;color:var(--ink-3)}
.item-back:hover{color:var(--accent);border-color:var(--line-strong)}
.item-meta{display:flex;flex-wrap:wrap;align-items:center;gap:10px;font-size:13px;color:var(--ink-4);margin-bottom:12px}
.item-meta .src{font-weight:600;color:var(--ink-2)}
.item-h1{font-size:32px;line-height:1.35;margin:0 0 10px}
.item-en-title{font-size:15px;line-height:1.6;color:var(--ink-4);margin:0 0 16px}
.item-guide{margin:16px 0}
.item-guide p{font-size:18px;line-height:1.7;margin:0}
.item-guide .guide-note{font-size:13px;color:var(--ink-4);margin-bottom:6px}
.item-actions{display:flex;flex-wrap:wrap;gap:10px;margin:18px 0}
.item-open-btn{display:inline-flex;align-items:center;gap:8px;min-height:44px;padding:0 20px;
  border-radius:9999px;background:var(--accent);color:#fff;font-size:15px;font-weight:600}
.item-open-btn:hover{background:var(--accent-strong)}
.item-open-btn:visited,.item-open-btn:active{color:#fff}
.item-ghost-btn{display:inline-flex;align-items:center;gap:6px;min-height:44px;padding:0 16px;
  border-radius:9999px;border:1px solid var(--line-strong);background:var(--surface);
  font-size:14px;color:var(--ink-2)}
.item-ghost-btn:hover{border-color:var(--accent);color:var(--accent)}
.item-ghost-btn.on{color:var(--accent);border-color:var(--accent)}
.item-source-line{font-size:13.5px;color:var(--ink-4);margin:6px 0 16px}
.item-source-line b{color:var(--ink-2)}
.item-sec{margin-top:28px}
.item-sec h2{font-size:17px;margin:0 0 10px}
.item-related-list{display:flex;flex-direction:column;gap:10px}
.item-related-list a{font-size:14.5px;font-weight:500;line-height:1.5}
.item-related-list a:hover{color:var(--accent)}
.item-related-list .rel-meta{font-size:12.5px;color:var(--ink-4)}
@media(max-width:699px){.item-h1{font-size:26px}}
/* B2：加载更多 */
.load-more-wrap{text-align:center;padding:16px 0 4px}
.load-more-btn{display:inline-flex;min-height:40px;align-items:center;gap:8px;padding:0 22px;
  border-radius:9999px;border:1px solid var(--line-strong);background:var(--surface);
  font-size:14px;font-weight:500;color:var(--ink-2)}
.load-more-btn:hover{border-color:var(--accent);color:var(--accent)}
.load-more-btn:disabled{opacity:.6;cursor:default}
.load-more-btn .spin{width:14px;height:14px;border:2px solid var(--line-strong);border-top-color:var(--accent);
  border-radius:9999px;animation:spin 0.8s linear infinite}
@keyframes spin{to{transform:rotate(360deg)}}
.load-more-state{margin:10px 0 0;font-size:12.5px;color:var(--ink-4)}
/* B2/B17：搜索结果区 */
.search-results-head{display:flex;align-items:baseline;gap:10px;margin:16px 0 4px}
.search-results-head h2{margin:0;font-size:17px;font-weight:600}
.search-results-head .sr-count{font-size:13px;color:var(--ink-4)}
/* C3：页脚链接行 */
.foot-links{display:flex;flex-wrap:wrap;gap:4px 16px;margin-top:4px;font-size:13px}
.foot-links a{color:var(--ink-3)}
.foot-links a:hover{color:var(--accent)}
/* 官方标记：T1 信源卡片头部的小标签 */
.off-tag{display:inline-flex;height:18px;align-items:center;padding:0 6px;border-radius:9999px;
  background:var(--accent-soft);color:var(--accent);font-size:11px;font-weight:600}
"""


def esc(s):
    return html.escape(s or "", quote=True)


def tr(zh, en=None):
    """界面文案翻译：英文站返回 en（未给 en 时返回中文原文），中文站返回中文。"""
    if PAGE_LANG == "en":
        return en if en is not None else zh
    return zh


def disp_title(it):
    """页面上显示的标题：英文站优先 en_title（原标题非英文时才有），否则源站原文标题；中文站优先中文翻译。"""
    if PAGE_LANG == "en":
        return it.get("en_title") or it["title"]
    return it.get("zh_title") or it["title"]


def disp_oneliner(it):
    """一句话简介：英文站用 en_oneliner（缺失返回空，不回落中文），中文站用 zh_oneliner。"""
    if PAGE_LANG == "en":
        return it.get("en_oneliner") or ""
    return it.get("zh_oneliner") or ""


def disp_reason(it):
    """推荐理由：英文站优先 reason_en，旧存档没有时把已存中文理由逐段翻译；中文站用 reason。"""
    if PAGE_LANG == "en":
        return it.get("reason_en") or translate_reason(it.get("reason", ""))
    return it.get("reason", "")


def cat_label(it):
    """分类标签：英文站用 label_en，中文站用中文标签。"""
    if PAGE_LANG == "en":
        return CAT_LABEL_EN.get(it.get("category", ""), it.get("category_label", ""))
    return it.get("category_label", "")


def _en_url(site_url, url):
    """中文版绝对 URL -> 对应的英文版绝对 URL（site_url 后插入 en/）。"""
    if url == site_url + "/":
        return site_url + "/en/"
    if url.startswith(site_url + "/"):
        return site_url + "/en/" + url[len(site_url) + 1:]
    return url


def _enc_url(url):
    """把完整 URL 里的非 ASCII 字符按 UTF-8 做 percent-encoding，保留 :/?# 等结构字符。
    Google 要求 sitemap / canonical / hreflang 里的 URL 用编码后的形式；
    只影响对外输出的 URL 文本，不改磁盘文件名。"""
    return urllib.parse.quote(url, safe=":/?#[]@!$&'()*+,;=%")


def lang_counterpart_href(rel_path):
    """当前页在另一语言下的对应页相对路径（切换链接与自动跳转共用）。
    空 rel_path（404 / geo-audit 等无英文版的页）返回空。"""
    if not rel_path:
        return ""
    if PAGE_LANG == "zh":
        return ("en/" if ASSET_BASE == "" else "../en/") + rel_path
    return ("../" if ASSET_BASE == "../" else "../../") + rel_path


def lang_switch_html(rel_path):
    """语言切换：rel_path 是页面相对本语言根的路径（如 "hot.html"、"daily/2026-11-17.html"）。
    空 rel_path（404 / geo-audit 等无英文版的页）返回空。"""
    href = lang_counterpart_href(rel_path)
    if not href:
        return ""
    if PAGE_LANG == "zh":
        return (f'<span class="lang-switch" role="group" aria-label="语言">'
                f'<span class="on" aria-current="true">中文</span>'
                f'<a href="{href}" data-lang="en">EN</a></span>')
    return (f'<span class="lang-switch" role="group" aria-label="Language">'
            f'<span class="on" aria-current="true">EN</span>'
            f'<a href="{href}" data-lang="zh">中文</a></span>')


def lang_redirect_script(site, rel_path):
    """浏览器语言自动跳转（与 tool-hot / ecommerce-hot 同款）：
    首次访问且未手动选过语言时，按 navigator.language 跳到对应语言版并记住选择；
    爬虫不跳。空 rel_path（无英文版的页）不注入。"""
    target = lang_counterpart_href(rel_path)
    if not target:
        return ""
    key = _storage_prefix(site) + "-lang"
    cur = "zh" if PAGE_LANG == "zh" else "en"
    return ("<script>(function(){try{var k='" + key + "';"
            "if(localStorage.getItem(k))return;"
            "if(/bot|crawler|spider|crawling|slurp|facebookexternal|preview/i.test(navigator.userAgent||''))return;"
            "var want=(navigator.language||navigator.userLanguage||'en').toLowerCase().indexOf('zh')===0?'zh':'en';"
            "localStorage.setItem(k,want);"
            "if(want!==\"" + cur + "\")location.replace(\"" + target + "\");"
            "}catch(e){}})();</script>")


WEEKDAYS = ["星期一", "星期二", "星期三", "星期四", "星期五", "星期六", "星期日"]
WEEKDAYS_SHORT = ["周一", "周二", "周三", "周四", "周五", "周六", "周日"]
WEEKDAYS_EN = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
WEEKDAYS_SHORT_EN = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
MONTHS_EN = ["January", "February", "March", "April", "May", "June",
             "July", "August", "September", "October", "November", "December"]

# 线性描边小图标（feather 风格；不引入任何外部资源）
ICONS = {
    "zap": '<polygon points="13 2 3 14 12 14 11 22 21 10 12 10 13 2"/>',
    "list": '<line x1="8" y1="6" x2="21" y2="6"/><line x1="8" y1="12" x2="21" y2="12"/>'
            '<line x1="8" y1="18" x2="21" y2="18"/><line x1="3" y1="6" x2="3.01" y2="6"/>'
            '<line x1="3" y1="12" x2="3.01" y2="12"/><line x1="3" y1="18" x2="3.01" y2="18"/>',
    "trend": '<polyline points="23 6 13.5 15.5 8.5 10.5 1 18"/><polyline points="17 6 23 6 23 12"/>',
    "doc": '<path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/>'
           '<polyline points="14 2 14 8 20 8"/><line x1="16" y1="13" x2="8" y2="13"/>'
           '<line x1="16" y1="17" x2="8" y2="17"/>',
    "code": '<polyline points="16 18 22 12 16 6"/><polyline points="8 6 2 12 8 18"/>',
    "bookmark": '<path d="M19 21l-7-5-7 5V5a2 2 0 0 1 2-2h10a2 2 0 0 1 2 2z"/>',
    "search": '<circle cx="11" cy="11" r="8"/><line x1="21" y1="21" x2="16.65" y2="16.65"/>',
    "chevron-down": '<polyline points="6 9 12 15 18 9"/>',
    "trend-up": '<polyline points="23 6 13.5 15.5 8.5 10.5 1 18"/><polyline points="17 6 23 6 23 12"/>',
    "trend-down": '<polyline points="23 18 13.5 8.5 8.5 13.5 1 6"/><polyline points="17 18 23 18 23 12"/>',
    "minus": '<line x1="5" y1="12" x2="19" y2="12"/>',
    "arrow-up": '<line x1="12" y1="19" x2="12" y2="5"/><polyline points="5 12 12 5 19 12"/>',
    "monitor": '<rect x="2" y="3" width="20" height="14" rx="2"/><line x1="8" y1="21" x2="16" y2="21"/>'
               '<line x1="12" y1="17" x2="12" y2="21"/>',
    "user": '<path d="M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"/>'
            '<circle cx="12" cy="7" r="4"/>',
    "rss": '<path d="M4 11a9 9 0 0 1 9 9"/><path d="M4 4a16 16 0 0 1 16 16"/>'
           '<circle cx="5" cy="19" r="1"/>',
    "message": '<path d="M21 11.5a8.38 8.38 0 0 1-.9 3.8 8.5 8.5 0 0 1-7.6 4.7 8.38 8.38 0 0 1-3.8-.9L3 21l1.9-5.7a8.38 8.38 0 0 1-.9-3.8 8.5 8.5 0 0 1 4.7-7.6 8.38 8.38 0 0 1 3.8-.9h.5a8.48 8.48 0 0 1 8 8v.5z"/>',
    "x": '<line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/>',
    "calendar": '<rect x="3" y="4" width="18" height="18" rx="2"/><line x1="16" y1="2" x2="16" y2="6"/>'
                '<line x1="8" y1="2" x2="8" y2="6"/><line x1="3" y1="10" x2="21" y2="10"/>',
    "check": '<polyline points="20 6 9 17 4 12"/>',
    "moon": '<path d="M21 12.79A9 9 0 1 1 11.21 3 7 7 0 0 0 21 12.79z"/>',
    "sun": '<circle cx="12" cy="12" r="5"/><line x1="12" y1="1" x2="12" y2="3"/>'
           '<line x1="12" y1="21" x2="12" y2="23"/><line x1="4.22" y1="4.22" x2="5.64" y2="5.64"/>'
           '<line x1="18.36" y1="18.36" x2="19.78" y2="19.78"/><line x1="1" y1="12" x2="3" y2="12"/>'
           '<line x1="21" y1="12" x2="23" y2="12"/><line x1="4.22" y1="19.78" x2="5.64" y2="18.36"/>'
           '<line x1="18.36" y1="5.64" x2="19.78" y2="4.22"/>',
}


def icon(name, size=17):
    return (f'<svg width="{size}" height="{size}" viewBox="0 0 24 24" fill="none" '
            f'stroke="currentColor" stroke-width="2" stroke-linecap="round" '
            f'stroke-linejoin="round" aria-hidden="true">{ICONS[name]}</svg>')


def score_pill(score):
    """AIHOT Score 的分档药丸：85+ 红、70+ 青、其余安静；手机只留数字。"""
    tier = "t-hot" if score >= 85 else ("t-acc" if score >= 70 else "t-quiet")
    lbl = tr("评分", "Score")
    return (f'<span class="score-pill {tier}" title="{lbl} {score}/100">'
            f'<span class="lbl">{lbl}</span><span class="sep"></span>'
            f'<span class="num">{score}</span></span>')


def _pub_dt(it):
    pub = it.get("_pub")
    if pub is None:  # daily.json 里的条目只有 ISO 字符串，没有 _pub
        pub = datetime.fromisoformat(it["published"])
        if pub.tzinfo is None:
            pub = pub.replace(tzinfo=timezone.utc)
    return pub


def feed_item(it, rank=None, badge=False, base=""):
    """AIHOT FeedItem 的静态版：来源行 + 标题 + 一句话简介 + 分类 + 推荐理由 + 星标。
    标题：中文站优先中文翻译，英文站优先 en_title、否则源站原文标题；简介是本站自己写的一句话
    （中文站 zh_oneliner，英文站 en_oneliner，缺失时省略简介行），不展示源站摘要原文。
    base 参数保留兼容：页面链接用 PAGE_BASE（到本语言根），资源链接用 ASSET_BASE。"""
    pub = _pub_dt(it)
    rank_html = ""
    if rank:
        cls = "r1" if rank == 1 else ("r2" if rank == 2 else ("r3" if rank == 3 else ""))
        rank_html = f'<span class="rank {cls}">{rank}</span>'
    badge_html = f'<span class="pick">{tr("精选", "Featured")}</span>' if badge else ""
    new_html = f'<span class="new-pill">{tr("新", "New")}</span>' if it.get("is_new") else ""
    off_html = f'<span class="off-tag">{tr("官方", "Official")}</span>' if it.get("_tier") == "T1" else ""
    reason_html = (f'<p class="fi-reason">{tr("推荐理由：", "Why it matters: ")}{esc(disp_reason(it))}</p>'
                   if disp_reason(it) else "")
    tags_html = ""
    tags = it.get("tags") or []
    if tags:
        tags_html = ('<div class="fi-tags">' + "".join(
            f'<a class="tag" href="{PAGE_BASE}topics/{TAG_SLUGS.get(t, t)}.html">#{esc(disp_label(t))}</a>'
            for t in tags[:3]) + '</div>')
    title = disp_title(it)
    summary = disp_oneliner(it)
    en_text = disp_title(it) if PAGE_LANG == "en" else it["title"]
    sum_attr = ' lang="en"' if (PAGE_LANG == "en" and summary) else ""
    save_lbl = tr("收藏", "Save")
    return (f'<article class="feed-item" data-id="{esc(it["id"])}" data-category="{esc(it["category"])}"'
            f' data-official="{"1" if it.get("_tier") == "T1" else "0"}"'
            f' data-en="{esc(en_text)}">'
            f'<header class="fi-head"><span class="src">{esc(disp_source(it))}</span>{off_html}'
            f'<time class="pt">· {esc(pub.astimezone(CST).strftime("%H:%M"))}</time>'
            f'{badge_html}{new_html}'
            f'<span class="sp">{score_pill(it["score"])}'
            f'<button type="button" class="star-btn" aria-label="{save_lbl}" title="{save_lbl}">'
            f'{icon("bookmark", 16)}</button></span></header>'
            f'<h3>{rank_html}<a href="{PAGE_BASE}items/{esc(it["id"])}.html">{esc(title)}</a></h3>'
            + (f'<p class="sum"{sum_attr}>{esc(summary)}</p>' if summary else "")
            + f'<div class="fi-foot"><button type="button" class="chip cat" data-filter="{esc(it["category"])}">'
            f'{esc(cat_label(it))}</button>'
            f'<span class="when">{esc(fmt_cst(pub))}</span></div>'
            + tags_html
            + reason_html
            + "</article>")


def hot_delta_html(it):
    """Delta：对照上一轮热度（prev_hot_score），带 %；首次上榜标“新”。"""
    prev = it.get("prev_hot_score")
    cur = it.get("hot_score")
    if prev is None or cur is None:
        return f'<span class="hot-delta new">{tr("新", "New")}</span>'
    if prev <= 0:
        return '<span class="hot-delta flat">–</span>'
    d = (cur - prev) / prev * 100.0
    if abs(d) < 0.5:
        return '<span class="hot-delta flat">–</span>'
    cls = "up" if d > 0 else "down"
    arrow = "▲" if d > 0 else "▼"
    return f'<span class="hot-delta {cls}">{arrow} {abs(d):.0f}%</span>'


def hot_badges(it):
    """头条/次卡徽章：热度 ≥90 为“爆”，首次上榜为“新”，名次上升为“发酵中”。"""
    out = []
    if it.get("trend") == "new":
        out.append(f'<span class="hot-badge b-new">{tr("新", "New")}</span>')
    if (it.get("hot_score") or 0) >= 90:
        out.append(f'<span class="hot-badge b-hot">{tr("爆", "Hot")}</span>')
    if it.get("trend") == "up":
        out.append(f'<span class="hot-badge b-up">{tr("发酵中", "Rising")}</span>')
    return "".join(out[:2])


def hot_row(it, rank, pad=False):
    """AIHOT HotTopics 的排名行：彩色名次 + 标题 + 热度分 + Delta + 趋势（升/降/新/持平）。"""
    cls = "r1" if rank == 1 else ("r2" if rank == 2 else ("r3" if rank == 3 else ""))
    num = f"{rank:02d}" if pad else str(rank)
    trend = it.get("trend", "same")
    if trend == "up":
        trend_html = f'<span class="hot-trend"><span class="up" title="{tr("热度上升", "Heat rising")}">{icon("trend-up", 14)}</span></span>'
    elif trend == "down":
        trend_html = f'<span class="hot-trend"><span title="{tr("热度回落", "Heat falling")}">{icon("trend-down", 14)}</span></span>'
    elif trend == "new":
        trend_html = f'<span class="hot-trend"><span class="new-pill">{tr("新", "New")}</span></span>'
    else:
        trend_html = f'<span class="hot-trend"><span class="flat" title="{tr("热度持平", "Heat flat")}">{icon("minus", 14)}</span></span>'
    return (f'<li><a class="hot-row" href="{PAGE_BASE}items/{esc(it["id"])}.html">'
            f'<span class="rank {cls}">{num}</span>'
            f'<span class="t">{esc(disp_title(it))}</span>'
            f'<span class="hot-heat"><b class="num">{round(it["hot_score"])}</b> {tr("热度", "Heat")}</span>'
            f'{hot_delta_html(it)}'
            f'{trend_html}'
            f'</a></li>')


THEME_BOOT = """<script>(function(){try{var k='__SLUG__-theme';function sys(){return window.matchMedia&&matchMedia('(prefers-color-scheme: dark)').matches?'dark':'light';}function apply(t){document.documentElement.setAttribute('data-theme',t==='dark'?'dark':'light');}var saved=localStorage.getItem(k);if(saved==='dark'||saved==='light'){apply(saved);}else{apply(sys());var mq=window.matchMedia&&matchMedia('(prefers-color-scheme: dark)');if(mq&&mq.addEventListener){mq.addEventListener('change',function(){try{if(!localStorage.getItem(k))apply(sys());}catch(e){}});}}}catch(e){}})();</script>"""

CF_BEACON = """<!-- Cloudflare Web Analytics --><script type='module' src='https://static.cloudflareinsights.com/beacon.min.js' data-cf-beacon='{"token": "faf0f409e3ee4f429210e586a98b58bd"}'></script><!-- End Cloudflare Web Analytics -->"""
def clarity_snippet(site):
    """Microsoft Clarity 统计代码：项目 ID 取自 config.json 的 site.clarity_id，未配则不输出。"""
    cid = (site or {}).get("clarity_id", "")
    if not cid:
        return ""
    return ("<script type=\"text/javascript\">(function(c,l,a,r,i,t,y){c[a]=c[a]||function(){(c[a].q=c[a].q||[]).push(arguments)};"
            "t=l.createElement(r);t.async=1;t.src=\"https://www.clarity.ms/tag/\"+i;"
            "y=l.getElementsByTagName(r)[0];y.parentNode.insertBefore(t,y);})"
            f"(window, document, \"clarity\", \"script\", \"{esc(cid)}\");</script>")

SCRIPT = """
<script>
(function(){
var LS_READ='__SLUG__-read',LS_STAR='__SLUG__-starred',LS_STAR_META='__SLUG__-starred-meta',
    LS_THEME='__SLUG__-theme',LS_RECENT='__SLUG__-recent-search',LS_CL_READ='__SLUG__-changelog-read';
var IS_EN=document.documentElement.lang==='en';
var DATA_BASE=document.documentElement.getAttribute('data-base')||'';
function pickTitle(it){return IS_EN?(it.en_title||it.title||''):(it.zh_title||it.title);}
function T(zh,en){return IS_EN?en:zh;}
function loadSet(k){try{return new Set(JSON.parse(localStorage.getItem(k)||'[]'));}catch(e){return new Set();}}
function saveSet(k,s){try{localStorage.setItem(k,JSON.stringify(Array.from(s)));}catch(e){}}
function loadObj(k){try{return JSON.parse(localStorage.getItem(k)||'{}')||{};}catch(e){return {};}}
function saveObj(k,o){try{localStorage.setItem(k,JSON.stringify(o));}catch(e){}}
var readSet=loadSet(LS_READ),starSet=loadSet(LS_STAR),starMeta=loadObj(LS_STAR_META);
function sysTheme(){return window.matchMedia&&matchMedia('(prefers-color-scheme: dark)').matches?'dark':'light';}
function currentTheme(){var s=null;try{s=localStorage.getItem(LS_THEME);}catch(e){}return (s==='dark'||s==='light')?s:'system';}
function applyTheme(mode){
  var t=mode==='system'?sysTheme():mode;
  var done=function(){
    document.documentElement.setAttribute('data-theme',t);
    try{
      if(mode==='system'){localStorage.removeItem(LS_THEME);}
      else{localStorage.setItem(LS_THEME,mode);}
    }catch(e){}
    syncThemeUI();
  };
  if(document.startViewTransition){try{document.startViewTransition(done);return;}catch(e){}}
  done();
}
function syncThemeUI(){
  var mode=currentTheme();
  document.querySelectorAll('.theme-cycle').forEach(function(b){
    b.setAttribute('data-mode',mode);
    var ic=b.querySelector('.ic-moon'),is=b.querySelector('.ic-sun'),im=b.querySelector('.ic-monitor');
    if(ic)ic.style.display=mode==='dark'?'inline-flex':'none';
    if(is)is.style.display=mode==='light'?'inline-flex':'none';
    if(im)im.style.display=mode==='system'?'inline-flex':'none';
    b.setAttribute('aria-label',IS_EN?('Appearance: '+(mode==='dark'?'dark':mode==='light'?'light':'system')+' (click to switch)'):('外观：'+(mode==='dark'?'深色':mode==='light'?'浅色':'跟随系统')+'（点击切换）'));
  });
  document.querySelectorAll('.theme-seg button').forEach(function(b){
    b.classList.toggle('on',b.getAttribute('data-theme-opt')===mode);
  });
  moveThemeThumb();
}
document.querySelectorAll('.theme-btn').forEach(function(b){b.addEventListener('click',function(){
  var order=['system','dark','light'],cur=currentTheme();
  applyTheme(order[(order.indexOf(cur)+1)%order.length]);
});});
document.querySelectorAll('.theme-seg button').forEach(function(b){b.addEventListener('click',function(){
  applyTheme(b.getAttribute('data-theme-opt'));
});});
/* 语言切换：点顶栏/页脚的切换时记住选择，自动跳转不再覆盖手动选择 */
document.querySelectorAll('.lang-switch a[data-lang]').forEach(function(a){a.addEventListener('click',function(){try{localStorage.setItem('__SLUG__-lang',a.getAttribute('data-lang'));}catch(e){}});});
/* 三向切换的滑动 thumb：量一下当前选中项的位置 */
var themeSegEl=document.querySelector('.theme-seg');
var themeThumb=document.getElementById('themeSegThumb');
function moveThemeThumb(){
  if(!themeSegEl||!themeThumb)return;
  var on=themeSegEl.querySelector('button.on');
  if(!on){themeThumb.style.width='0px';return;}
  themeThumb.style.left=(on.offsetLeft)+'px';
  themeThumb.style.width=(on.offsetWidth)+'px';
}
window.addEventListener('resize',moveThemeThumb);
window.addEventListener('load',moveThemeThumb);
syncThemeUI();
/* 已读：点开标题即记已读，标题变灰；星标：本地收藏，可再筛出来。
   bindFeedItem 供动态加载的卡片复用（B2 分页/搜索结果）。 */
function bindFeedItem(el){
  if(el.getAttribute('data-bound'))return;
  el.setAttribute('data-bound','1');
  var id=el.getAttribute('data-id');
  if(!id)return;
  if(readSet.has(id))el.classList.add('is-read');
  var star=el.querySelector('.star-btn');
  if(star){
    if(starSet.has(id)){star.classList.add('on');star.setAttribute('aria-label',IS_EN?'Unsave':'取消收藏');star.title=IS_EN?'Unsave':'取消收藏';}
    star.addEventListener('click',function(){
      if(starSet.has(id)){
        starSet.delete(id);delete starMeta[id];
        star.classList.remove('on');star.setAttribute('aria-label',IS_EN?'Save':'收藏');star.title=IS_EN?'Save':'收藏';
      }else{
        starSet.add(id);
        /* 收藏快照：标题/链接/来源/时间，供收藏页离线展示与下架置灰用 */
        var a=el.querySelector('h3 a'),src=el.querySelector('.fi-head .src');
        starMeta[id]={title:a?a.textContent.trim():'',link:a?a.getAttribute('href'):'',
          source:src?src.textContent.trim():'',at:new Date().toISOString()};
        star.classList.add('on');star.setAttribute('aria-label',IS_EN?'Unsave':'取消收藏');star.title=IS_EN?'Unsave':'取消收藏';
      }
      saveSet(LS_STAR,starSet);saveObj(LS_STAR_META,starMeta);applyFilters();
    });
  }
  var a=el.querySelector('h3 a');
  if(a)a.addEventListener('click',function(){
    if(!readSet.has(id)){readSet.add(id);saveSet(LS_READ,readSet);el.classList.add('is-read');applyFilters();}
  });
}
document.querySelectorAll('.feed-item').forEach(bindFeedItem);
/* 筛选状态：分类 + 只看收藏 + 只看未读 + 搜索词，四者叠加 */
var state={cat:'all',star:false,unread:false,q:''};
function itemVisible(el){
  var id=el.getAttribute('data-id')||'';
  if(state.cat==='official'&&el.getAttribute('data-official')!=='1')return false;
  if(state.cat!=='all'&&state.cat!=='starred'&&state.cat!=='official'&&el.getAttribute('data-category')!==state.cat)return false;
  if(state.cat==='starred'&&!starSet.has(id))return false;
  if(state.star&&!starSet.has(id))return false;
  if(state.unread&&readSet.has(id))return false;
  if(state.q){
    var t=((el.textContent||'')+' '+(el.getAttribute('data-en')||'')).toLowerCase();
    if(t.indexOf(state.q)===-1)return false;
  }
  return true;
}
function applyFilters(){
  /* 有搜索词时进入全量搜索模式（B2/B17）：对 data/days/ 30 天分块检索并排序，
     隐藏正常的精选/热点/时间线，显示搜索结果区。 */
  if(state.q){enterSearchMode();return;}
  exitSearchMode();
  var hot=document.getElementById('hot');
  if(hot)hot.style.display=(state.cat==='all')?'':'none';
  var shown=0;
  document.querySelectorAll('#featured .feed-item').forEach(function(el){
    var ok=itemVisible(el);el.style.display=ok?'':'none';if(ok)shown++;
  });
  document.querySelectorAll('#timeline .slot').forEach(function(li){
    var card=li.querySelector('.feed-item');
    var ok=card?itemVisible(card):true;
    li.style.display=ok?'':'none';if(ok)shown++;
  });
  document.querySelectorAll('#timeline .day-sec').forEach(function(sec){
    var vis=sec.querySelectorAll('.slot:not([style*="none"])').length;
    sec.style.display=vis?'':'none';
  });
  var nr=document.getElementById('noResult');
  if(nr){
    nr.hidden=!!shown;nr.style.display='';
    var t=document.getElementById('noResultTitle'),x=document.getElementById('noResultText');
    if(state.cat==='starred'||state.star){
      if(t)t.textContent=IS_EN?'No saved items yet':'还没有收藏';
      if(x)x.textContent=IS_EN?'Tap the bookmark on a card and it will show up here.':'去点卡片右上角的书签，喜欢的动态就会出现在这里。';
    }else if(state.unread){
      if(t)t.textContent=IS_EN?'You have read this batch':'这批都读过了';
      if(x)x.textContent=IS_EN?'Turn off "Unread only" to see everything.':'关掉「只看未读」可以看到全部动态。';
    }else if(state.q){
      if(t)t.textContent=IS_EN?('No items matching "'+state.q+'".'):('没有匹配「'+state.q+'」的动态。');
      if(x)x.textContent=IS_EN?'Try another keyword, or clear the search to see everything.':'换个关键词试试，或者清除搜索看看全部。';
    }else{
      if(t)t.textContent=IS_EN?'No items in this category yet.':'这个分类下暂无动态。';
      if(x)x.textContent=IS_EN?'Try another category, or go back to all updates.':'换个分类看看，或者回到全部动态。';
    }
  }
  var sc=document.getElementById('starCount');
  if(sc)sc.textContent=starSet.size?('（'+starSet.size+'）'):'';
  if(typeof updateStarCounts==='function')updateStarCounts();
}
var filterTimer=null;
function scheduleFilter(){
  if(filterTimer)clearTimeout(filterTimer);
  filterTimer=setTimeout(applyFilters,150);
}
function setCat(f){
  state.cat=f;state.star=(f==='starred');
  document.querySelectorAll('.tabs .chip').forEach(function(x){
    x.classList.toggle('on',x.getAttribute('data-filter')===f);
  });
  document.querySelectorAll('[data-filter="starred"]').forEach(function(x){
    x.classList.toggle('on',f==='starred');
  });
  moveThumb();applyFilters();
}
/* 分类 chips：用事件委托，动态加载的卡片里的分类 chip 也能点（B2） */
document.addEventListener('click',function(e){
  var b=e.target.closest('[data-filter]');
  if(!b)return;
  if(b.closest('#searchOverlay'))return; /* 浮层里的 chips 有自己的处理 */
  setCat(b.getAttribute('data-filter'));
});
/* 分段控件的白色滑块：量一下当前选中项的位置，滑动过去 */
var tabsEl=document.querySelector('.tabs');
var thumb=document.getElementById('tabsThumb');
function moveThumb(){
  if(!tabsEl||!thumb)return;
  var on=tabsEl.querySelector('.chip.on');
  if(!on){thumb.style.width='0px';return;}
  thumb.style.left=(on.offsetLeft)+'px';
  thumb.style.width=(on.offsetWidth)+'px';
}
window.addEventListener('resize',moveThumb);
window.addEventListener('load',moveThumb);
moveThumb();
/* 搜索：标题+摘要+来源即时过滤；“/” 聚焦；× 清空 */
var searchInput=document.getElementById('siteSearch');
if(searchInput){
  var box=searchInput.closest('.search');
  searchInput.addEventListener('input',function(){
    state.q=searchInput.value.trim().toLowerCase();
    if(box)box.classList.toggle('has-value',!!searchInput.value);
    scheduleFilter();
  });
  var clr=document.getElementById('searchClear');
  if(clr)clr.addEventListener('click',function(){searchInput.value='';state.q='';if(box)box.classList.remove('has-value');searchInput.focus();applyFilters();});
  document.addEventListener('keydown',function(e){
    if(e.key==='/'&&!(e.target instanceof HTMLInputElement||e.target instanceof HTMLTextAreaElement)){
      e.preventDefault();searchInput.focus();
    }
  });
}
/* 只看未读（桌面在首个日期行右侧，手机在单独一行） */
document.querySelectorAll('.unread-toggle').forEach(function(b){
  b.addEventListener('click',function(){
    state.unread=!state.unread;
    document.querySelectorAll('.unread-toggle').forEach(function(x){x.classList.toggle('on',state.unread);});
    applyFilters();
  });
});
/* 日期折叠：事件委托，动态加载的日期区也能折（B2） */
document.addEventListener('click',function(e){
  var b=e.target.closest('.dh-toggle');
  if(!b)return;
  var sec=b.closest('.day-sec');
  if(sec)sec.classList.toggle('collapsed');
});
/* 回到顶部 */
var toTop=document.getElementById('toTop');
if(toTop){
  toTop.addEventListener('click',function(){window.scrollTo({top:0,behavior:'smooth'});});
  window.addEventListener('scroll',function(){
    toTop.classList.toggle('show',window.scrollY>window.innerHeight*1.2);
  },{passive:true});
}
/* #starred 直达收藏视图（加载时与 hash 变化时都生效） */
if(location.hash==='#starred'){setCat('starred');}
window.addEventListener('hashchange',function(){
  if(location.hash==='#starred'){setCat('starred');}
});
/* 顶栏滚动阴影（A4）：滚出一点就加阴影 */
var topbar=document.querySelector('.topbar');
function syncTopbar(){if(topbar)topbar.classList.toggle('scrolled',window.scrollY>8);}
window.addEventListener('scroll',syncTopbar,{passive:true});syncTopbar();
/* 底栏点当前 tab：回顶；已在顶部则刷新（A5） */
document.querySelectorAll('.tabbar a').forEach(function(a){
  if(!a.classList.contains('on'))return;
  a.addEventListener('click',function(e){
    e.preventDefault();
    if(window.scrollY<10){location.reload();}
    else{window.scrollTo({top:0,behavior:'smooth'});}
  });
});
/* 收藏数量：侧栏/我的页/底栏都显示（B3/B4） */
function updateStarCounts(){
  document.querySelectorAll('[data-star-count]').forEach(function(el){el.textContent=starSet.size?('（'+starSet.size+'）'):(el.getAttribute('data-star-count-empty')||'');});
}
updateStarCounts();
/* 空状态操作按钮（B19）：清除筛选 / 去看精选（事件委托，搜索结果里的空状态也生效） */
document.addEventListener('click',function(e){
  var b=e.target.closest('[data-empty-action]');
  if(!b)return;
  var act=b.getAttribute('data-empty-action');
  state.q='';state.unread=false;
  var si=document.getElementById('siteSearch');
  if(si){si.value='';var bx=si.closest('.search');if(bx)bx.classList.remove('has-value');}
  var oi=document.getElementById('overlaySearch');
  if(oi)oi.value='';
  document.querySelectorAll('.unread-toggle').forEach(function(x){x.classList.remove('on');});
  setCat('all');
  if(act==='featured'){
    var f=document.getElementById('featured');
    if(f){f.scrollIntoView();}
    else{var br=document.querySelector('.topbar .brand')||document.querySelector('.sidebar .brand');if(br)location.href=br.getAttribute('href');}
  }
});
/* 手机搜索浮层（B14）：全屏层 + 最近搜索 + 分类 chips + 热议 */
var overlay=document.getElementById('searchOverlay');
var overlayInput=document.getElementById('overlaySearch');
function isMobile(){return window.matchMedia&&window.matchMedia('(max-width: 699px)').matches;}
function openOverlay(){
  if(!overlay)return;
  if(!isMobile()){var si=document.getElementById('siteSearch');if(si)si.focus();return;}
  overlay.hidden=false;document.body.style.overflow='hidden';
  renderRecent();
  if(overlayInput)setTimeout(function(){overlayInput.focus();},50);
}
function closeOverlay(){
  if(!overlay)return;
  overlay.hidden=true;document.body.style.overflow='';
}
document.querySelectorAll('.search-trigger').forEach(function(b){b.addEventListener('click',openOverlay);});
var ovClose=document.getElementById('overlayClose');
if(ovClose)ovClose.addEventListener('click',closeOverlay);
document.addEventListener('keydown',function(e){if(e.key==='Escape'&&overlay&&!overlay.hidden)closeOverlay();});
if(overlayInput){
  overlayInput.addEventListener('input',function(){
    state.q=overlayInput.value.trim().toLowerCase();
    var si=document.getElementById('siteSearch');if(si)si.value=overlayInput.value;
    scheduleFilter();
  });
  overlayInput.addEventListener('keydown',function(e){
    if(e.key==='Enter'){
      var q=overlayInput.value.trim();
      if(q)saveRecent(q);
      closeOverlay();
      var tl=document.getElementById('timeline');if(tl)tl.scrollIntoView();
    }
  });
}
function loadRecent(){try{return JSON.parse(localStorage.getItem(LS_RECENT)||'[]')||[];}catch(e){return [];}}
function saveRecent(q){
  var list=loadRecent().filter(function(x){return x!==q;});
  list.unshift(q);list=list.slice(0,8);
  try{localStorage.setItem(LS_RECENT,JSON.stringify(list));}catch(e){}
}
function renderRecent(){
  var box=document.getElementById('recentList');if(!box)return;
  var list=loadRecent();
  box.innerHTML=list.length?list.map(function(q){
    return '<div class="recent-row"><button type="button" class="chip" data-recent="'+q.replace(/"/g,'&quot;')+'">'+q.replace(/</g,'&lt;')+'</button></div>';
  }).join(''):'<p class="more-note">'+(IS_EN?'No searches yet.':'还没有搜索过。')+'</p>';
  box.querySelectorAll('[data-recent]').forEach(function(b){
    b.addEventListener('click',function(){
      var q=b.getAttribute('data-recent');
      if(overlayInput)overlayInput.value=q;
      state.q=q.toLowerCase();
      var si=document.getElementById('siteSearch');if(si)si.value=q;
      applyFilters();closeOverlay();
      var tl=document.getElementById('timeline');if(tl)tl.scrollIntoView();
    });
  });
}
var clrRecent=document.getElementById('clearRecent');
if(clrRecent)clrRecent.addEventListener('click',function(){
  try{localStorage.removeItem(LS_RECENT);}catch(e){}renderRecent();
});
document.querySelectorAll('#searchOverlay [data-filter]').forEach(function(b){
  b.addEventListener('click',function(){setCat(b.getAttribute('data-filter'));closeOverlay();});
});
/* 我的页：收藏数量 + 更新日志红点（B4/B6） */
(function(){
  var dot=document.getElementById('changelogDot');
  if(dot){
    var latest=dot.getAttribute('data-changelog-version')||'';
    var read='';
    try{read=localStorage.getItem(LS_CL_READ)||'';}catch(e){}
    dot.hidden=!!(read&&read===latest);
  }
  var mc=document.getElementById('moreStarCount');
  if(mc)mc.textContent=starSet.size?String(starSet.size):'0';
})();
/* 更新日志页：打开即记为已读（B6） */
(function(){
  var pg=document.getElementById('changelogPage');
  if(pg){
    var v=pg.getAttribute('data-changelog-version')||'';
    if(v){try{localStorage.setItem(LS_CL_READ,v);}catch(e){}}
  }
})();
/* ============ 客户端数据层：按天分块（data/days/） ============ */
/* 首页首屏由服务端渲染；浏览器只在需要时才按天取分块：分页一次取一天，
   搜索与收藏页在用户操作时才并行取全部天（仍按天分块，不再拉 30 天单文件）。 */
var dayIndexPromise=null;
var dayCache={};
function getDayIndex(){
  if(dayIndexPromise)return dayIndexPromise;
  dayIndexPromise=fetch(DATA_BASE+'data/days/index.json').then(function(r){
    if(!r.ok)throw new Error('HTTP '+r.status);return r.json();
  }).then(function(d){
    return (d.days||[]).map(function(x){return x.date;});
  }).catch(function(e){dayIndexPromise=null;throw e;});
  return dayIndexPromise;
}
function getDay(date){
  if(dayCache[date])return dayCache[date];
  dayCache[date]=fetch(DATA_BASE+'data/days/'+date+'.json').then(function(r){
    if(!r.ok)throw new Error('HTTP '+r.status);return r.json();
  }).then(function(d){
    return (d.items||[]).sort(function(a,b){return new Date(b.published)-new Date(a.published);});
  }).catch(function(e){delete dayCache[date];throw e;});
  return dayCache[date];
}
/* 全量：只在搜索 / 收藏页按需调用（并行取各天分块并缓存），首页加载时不调用 */
function getStore(){
  return getDayIndex().then(function(days){
    return Promise.all(days.map(getDay));
  }).then(function(lists){
    var all=[];
    lists.forEach(function(l){all=all.concat(l);});
    return all.sort(function(a,b){return new Date(b.published)-new Date(a.published);});
  });
}
/* 收藏页：从本地快照渲染，查 data/days/ 分块判断是否下架（B3） */
(function(){
  var list=document.getElementById('starList');
  if(!list)return;
  var empty=document.getElementById('starEmpty');
  var ids=Array.from(starSet);
  if(!ids.length){if(empty)empty.hidden=false;return;}
  getStore().then(function(items){
    var live={};
    items.forEach(function(it){live[it.id]=it;});
    var html=ids.map(function(id){
      var m=starMeta[id]||{};
      var it=live[id];
      var gone=!it;
      var title=it?pickTitle(it):(m.title||(IS_EN?'(Unknown title)':'（标题未知）'));
      var link=m.link||(it?it.link:'#');
      var source=it?(IS_EN?(it.source_en||it.source):it.source):(m.source||'');
      var at=m.at?new Date(m.at):null;
      var atStr=at?(IS_EN?('Saved on '+at.getFullYear()+'-'+(at.getMonth()+1)+'-'+at.getDate()):('收藏于 '+at.getFullYear()+'年'+(at.getMonth()+1)+'月'+at.getDate()+'日')):'';
      return '<article class="feed-item starred-item'+(gone?' is-gone':'')+'">'
        +'<header class="fi-head"><span class="src">'+source.replace(/</g,'&lt;')+'</span>'
        +(gone?'<span class="gone-tag">'+(IS_EN?'Removed':'已下架')+'</span>':'')
        +'<span class="sp"><button type="button" class="star-btn on" data-unstar="'+id+'" aria-label="'+(IS_EN?'Unsave':'取消收藏')+'" title="'+(IS_EN?'Unsave':'取消收藏')+'">'
        +'<svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M19 21l-7-5-7 5V5a2 2 0 0 1 2-2h10a2 2 0 0 1 2 2z"/></svg>'
        +'</button></span></header>'
        +'<h3><a href="items/'+id+'.html">'+title.replace(/</g,'&lt;')+'</a></h3>'
        +(gone?'<p class="sum">'+(IS_EN?'This item is no longer in the 30-day data (it may have been removed or expired); only the title and link from when you saved it are kept.':'这条动态已不在本站 30 天数据里（可能已下架或超出保存期），只保留了你收藏时的标题与链接。')+'</p>':'')
        +(atStr?'<p class="starred-at">'+atStr+'</p>':'')
        +'</article>';
    }).join('');
    list.innerHTML=html;
    list.querySelectorAll('[data-unstar]').forEach(function(b){
      b.addEventListener('click',function(){
        var id=b.getAttribute('data-unstar');
        starSet.delete(id);delete starMeta[id];
        saveSet(LS_STAR,starSet);saveObj(LS_STAR_META,starMeta);
        updateStarCounts();
        b.closest('.starred-item').remove();
        if(!list.querySelector('.starred-item')&&empty)empty.hidden=false;
      });
    });
  }).catch(function(){
    if(empty)empty.hidden=false;
  });
})();
/* ============ B2 分页 + B17 全量搜索 + B18 滚动恢复 ============ */
function escHtml(s){return String(s==null?'':s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');}
var SEARCH_ICON_SVG='<svg width="40" height="40" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="11" cy="11" r="8"/><line x1="21" y1="21" x2="16.65" y2="16.65"/></svg>';
var BOOKMARK_SVG='<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M19 21l-7-5-7 5V5a2 2 0 0 1 2-2h10a2 2 0 0 1 2 2z"/></svg>';
var CHEV_SVG='<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><polyline points="6 9 12 15 18 9"/></svg>';
var IH_CFG=null;
try{var cfgEl=document.getElementById('ihConfig');if(cfgEl)IH_CFG=JSON.parse(cfgEl.textContent);}catch(e){IH_CFG=null;}
/* getStore() 见上方的客户端数据层（按天分块取 data/days/）。 */
/* 北京时间的年月日时分（用 UTC+8 换算，不依赖浏览器时区） */
function cstParts(date){
  var c=new Date(date.getTime()+8*3600000);
  var p=function(n){return String(n).padStart(2,'0');};
  return {y:c.getUTCFullYear(),m:c.getUTCMonth()+1,d:c.getUTCDate(),
    hh:c.getUTCHours(),mm:c.getUTCMinutes(),wd:c.getUTCDay(),
    iso:c.getUTCFullYear()+'-'+p(c.getUTCMonth()+1)+'-'+p(c.getUTCDate()),
    hm:p(c.getUTCHours())+':'+p(c.getUTCMinutes())};
}
function todayCST(){return cstParts(new Date()).iso;}
function fmtCST(iso){
  var p=cstParts(new Date(iso));
  if(IS_EN)return ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'][p.m-1]+' '+p.d+' '+p.hm;
  return p.m+'月'+p.d+'日 '+p.hm;
}
/* 与 Python score()/reason_for() 同规则的客户端版（动态卡片用） */
function computeMeta(it){
  var tier=it.tier||(IH_CFG?IH_CFG.tiers[it.source_id]:null)||'T2';
  var labels=it.tags||[];
  var score=0,reason='';
  if(IH_CFG){
    var pub=new Date(it.published);
    var ageH=(Date.now()-pub.getTime())/3600000;
    score=IH_CFG.base;
    for(var i=0;i<IH_CFG.recency.length;i++){
      var r=IH_CFG.recency[i];
      if(ageH<=r.max_hours){score+=r.bonus;break;}
    }
    score+=((IH_CFG.tierBonus||{})[tier]||0);
    var text=((it.title||'')+' '+(it.en_title||'')+' '+(it.zh_title||'')+' '+(it.zh_oneliner||'')+' '+(it.en_oneliner||'')).toLowerCase();
    var devHits=0;
    Object.keys(IH_CFG.devLabels||{}).forEach(function(kw){
      if(text.indexOf(kw.toLowerCase())>-1)devHits++;
    });
    score+=Math.min(devHits*IH_CFG.devBonus,IH_CFG.devCap);
    var noiseHits=0;
    (IH_CFG.noiseKw||[]).forEach(function(kw){
      if(text.indexOf(kw.toLowerCase())>-1)noiseHits++;
    });
    score+=Math.max(noiseHits*IH_CFG.noisePenalty,IH_CFG.noiseFloor);
    score=Math.max(0,Math.min(100,score));
    if(!labels.length){
      var seen={};
      Object.keys(IH_CFG.devLabels||{}).forEach(function(kw){
        if(text.indexOf(kw.toLowerCase())>-1){
          var lab=IH_CFG.devLabels[kw];
          if(!seen[lab]){seen[lab]=1;labels.push(lab);}
        }
      });
      labels=labels.slice(0,3);
    }
    var parts=[];
    if(tier==='T1')parts.push(IS_EN?'Official source':'官方来源');
    if(labels.length){
      var labs=labels.slice(0,2).map(function(l){return (IH_CFG&&IH_CFG.labelEn&&IH_CFG.labelEn[l])||l;});
      parts.push(IS_EN?('About '+labs.join(' and ')):('涉及'+labels.slice(0,2).join('与')));
    }
    if(ageH<=6)parts.push(IS_EN?'Published within 6 hours':'6 小时内发布');else if(ageH<=24)parts.push(IS_EN?'Published within 24 hours':'24 小时内发布');
    if(parts.length<2)parts.push(IS_EN?'Related to this topic':'与本主题相关');
    reason=parts.join(' · ');
  }else{
    score=it.score||0;reason=it.reason||'';
  }
  return {score:score,reason:reason,labels:labels,tier:tier};
}
function cardHTML(it){
  var m=computeMeta(it);
  var title=pickTitle(it);
  var summary=IS_EN?(it.en_oneliner||''):(it.zh_oneliner||'');
  var en=pickTitle(it);
  var pub=cstParts(new Date(it.published));
  var off=m.tier==='T1'?'<span class="off-tag">'+(IS_EN?'Official':'官方')+'</span>':'';
  var isNew=false;
  if(it.fetched_at){
    isNew=cstParts(new Date(it.fetched_at)).iso===todayCST()
      &&(Date.now()-new Date(it.published).getTime())<=86400000;
  }
  var newHtml=isNew?'<span class="new-pill">'+(IS_EN?'New':'新')+'</span>':'';
  var tagsHtml=m.labels.length?'<div class="fi-tags">'+m.labels.map(function(t){
    return '<a class="tag" href="topics/'+((IH_CFG&&IH_CFG.tagSlugs[t])||t)+'.html">#'+escHtml(IS_EN?((IH_CFG&&IH_CFG.labelEn&&IH_CFG.labelEn[t])||t):t)+'</a>';
  }).join('')+'</div>':'';
  var scoreCls=m.score>=85?'t-hot':(m.score>=70?'t-acc':'t-quiet');
  return '<article class="feed-item" data-id="'+escHtml(it.id)+'" data-category="'+escHtml(it.category||'')+'"'
    +' data-official="'+(m.tier==='T1'?'1':'0')+'" data-en="'+escHtml(en)+'">'
    +'<header class="fi-head"><span class="src">'+escHtml(IS_EN?(it.source_en||it.source):it.source)+'</span>'+off
    +'<time class="pt">· '+pub.hm+'</time>'+newHtml
    +'<span class="sp"><span class="score-pill '+scoreCls+'" title="'+(IS_EN?'Score ':'评分 ')+m.score+'/100">'
    +'<span class="lbl">'+(IS_EN?'Score':'评分')+'</span><span class="sep"></span><span class="num">'+m.score+'</span></span>'
    +'<button type="button" class="star-btn" aria-label="'+(IS_EN?'Save':'收藏')+'" title="'+(IS_EN?'Save':'收藏')+'">'+BOOKMARK_SVG+'</button></span></header>'
    +'<h3><a href="items/'+escHtml(it.id)+'.html">'+escHtml(title)+'</a></h3>'
    +(summary?'<p class="sum"'+(IS_EN?' lang="en"':'')+'>'+escHtml(summary)+'</p>':'')
    +'<div class="fi-foot"><button type="button" class="chip cat" data-filter="'+escHtml(it.category||'')+'">'
    +escHtml(IS_EN?(it.category_label_en||it.category_label||it.category||''):(it.category_label||it.category||''))+'</button>'
    +'<span class="when">'+escHtml(fmtCST(it.published))+'</span></div>'
    +tagsHtml
    +'<p class="fi-reason">'+(IS_EN?'Why it matters: ':'推荐理由：')+escHtml(m.reason)+'</p>'
    +'</article>';
}
function slotHTML(it){
  var pub=cstParts(new Date(it.published));
  return '<li class="slot" data-category="'+escHtml(it.category||'')+'">'
    +'<time class="slot-time" datetime="'+escHtml(it.published)+'">'+pub.hm+'</time>'
    +'<span class="rail" aria-hidden="true"></span>'
    +cardHTML(it)+'</li>';
}
function normTitle(t){
  return (t||'').toLowerCase().replace(/[\\s\\-_·•|/\\:;,.!?？！。、，；：（）()\\[\\]{}“”"'‘’<>《》]+/g,'');
}
function stripOutlet(t){
  t=(t||'').trim();
  var seps=[' ——《',' —— ',' - ',' | ',' — '];
  for(var i=0;i<seps.length;i++){
    var idx=t.lastIndexOf(seps[i]);
    if(idx<0)continue;
    var head=t.slice(0,idx),tail=t.slice(idx+seps[i].length);
    if(head.length>=15&&tail.length<=25)return head.trim();
  }
  return t;
}
function groupSimilarJS(items){
  var groups=[];
  items.forEach(function(it){
    var norm=normTitle(stripOutlet(pickTitle(it)));
    var date=cstParts(new Date(it.published)).iso;
    var merged=false;
    if(norm.length>=10){
      for(var i=0;i<groups.length;i++){
        var g=groups[i],m=g.main;
        if(cstParts(new Date(m.published)).iso!==date)continue;
        var mn=normTitle(stripOutlet(pickTitle(m)));
        if(mn.length<10)continue;
        if(norm===mn||((norm.indexOf(mn)===0||mn.indexOf(norm)===0)
            &&Math.min(norm.length,mn.length)/Math.max(norm.length,mn.length)>=0.8)){
          g.extra.push(it);merged=true;break;
        }
      }
    }
    if(!merged)groups.push({main:it,extra:[]});
  });
  return groups;
}
function groupSlotHTML(g){
  var slot=slotHTML(g.main);
  if(!g.extra.length)return slot;
  var rows=g.extra.map(function(e){
    var p=cstParts(new Date(e.published));
    return '<li><a href="items/'+escHtml(e.id)+'.html">'+escHtml(pickTitle(e))+'</a>'
      +'<span class="ge-time">'+p.hm+'</span></li>';
  }).join('');
  var toggle='<button type="button" class="group-toggle" aria-expanded="false">'+(IS_EN?('Show '+g.extra.length+' more reports '):('另有 '+g.extra.length+' 篇报道 '))+'<span aria-hidden="true">▾</span></button>';
  var extra='<div class="group-extra" hidden><ul class="group-extra-list">'+rows+'</ul></div>';
  return slot.slice(0,-5)+toggle+extra+'</li>';
}
function dayHeaderHTML(dateISO,count){
  var parts=dateISO.split('-');
  var wd=new Date(+parts[0],+parts[1]-1,+parts[2]).getDay();
  var isToday=dateISO===todayCST();
  var name=isToday?(IS_EN?'Today':'今天'):(IS_EN?(+parts[1]+'/'+(+parts[2])):(+parts[1]+'月'+(+parts[2])+'日'));
  var wdShort=(IS_EN?['Sun','Mon','Tue','Wed','Thu','Fri','Sat']:['周日','周一','周二','周三','周四','周五','周六'])[wd];
  var wdFull=(IS_EN?['Sunday','Monday','Tuesday','Wednesday','Thursday','Friday','Saturday']:['星期日','星期一','星期二','星期三','星期四','星期五','星期六'])[wd];
  return '<header class="day-head'+(isToday?' is-today':'')+'">'
    +'<span class="dh-name">'+name+'</span>'
    +'<span class="dh-date">'+(IS_EN?((+parts[1])+'/'+(+parts[2])):((+parts[1])+'月'+(+parts[2])+'日'))+'</span>'
    +'<button type="button" class="dh-toggle" aria-label="'+(IS_EN?'Collapse/expand this day':'收起/展开这一天')+'">'+CHEV_SVG+'</button>'
    +'<span class="dh-wd dh-wd-short">'+wdShort+'</span>'
    +'<span class="dh-wd dh-wd-full">'+wdFull+'</span>'
    +'<span class="dh-count"><b class="num">'+count+'</b> '+(IS_EN?'items':'条')+'</span></header>';
}
function renderBatch(items){
  var groups=groupSimilarJS(items);
  var days={},order=[];
  groups.forEach(function(g){
    var d=cstParts(new Date(g.main.published)).iso;
    if(!days[d]){days[d]=[];order.push(d);}
    days[d].push(g);
  });
  var tl=document.getElementById('timeline');
  if(!tl)return;
  order.forEach(function(d){
    var html=days[d].map(groupSlotHTML).join('');
    var count=days[d].reduce(function(n,g){return n+1+g.extra.length;},0);
    var sec=tl.querySelector('.day-sec[data-date="'+d+'"]');
    if(sec){
      var ol=sec.querySelector('.day-list');
      if(ol)ol.insertAdjacentHTML('beforeend',html);
      var cnt=sec.querySelector('.dh-count .num');
      if(cnt)cnt.textContent=parseInt(cnt.textContent||'0',10)+count;
    }else{
      tl.insertAdjacentHTML('beforeend',
        '<section class="day-sec" data-date="'+d+'">'+dayHeaderHTML(d,count)
        +'<ol class="day-list">'+html+'</ol></section>');
    }
  });
  tl.querySelectorAll('.feed-item').forEach(bindFeedItem);
  applyFilters();
}
/* 分页状态机：加载态 / 失败重试 / 到底 */
var lmState={loading:false,done:false};
function setLoadMoreState(s){
  var btn=document.getElementById('loadMoreBtn'),st=document.getElementById('loadMoreState'),
      wrap=document.getElementById('loadMoreWrap'),end=document.getElementById('feedEnd');
  if(!btn)return;
  if(s==='loading'){btn.disabled=true;btn.innerHTML='<span class="spin"></span>'+(IS_EN?'Loading':'正在加载');if(st)st.textContent='';}
  else if(s==='error'){btn.disabled=false;btn.textContent=IS_EN?'Failed to load, click to retry':'加载失败，点击重试';if(st)st.textContent=IS_EN?'Something went wrong with the network or data. Click the button to try again.':'网络或数据有问题，点按钮再试一次。';}
  else if(s==='done'){if(wrap)wrap.hidden=true;if(end)end.hidden=false;}
  else{btn.disabled=false;btn.textContent=IS_EN?'Load more':'加载更多';if(st)st.textContent='';}
}
/* 分页：按天取分块，一天不够再取下一天，直到凑满 30 条未见过的卡片 */
var lmDayIdx=0,lmBuffer=[];
function loadMore(){
  if(lmState.loading||lmState.done||state.q)return Promise.resolve(false);
  var tl=document.getElementById('timeline');
  if(!tl)return Promise.resolve(false);
  lmState.loading=true;setLoadMoreState('loading');
  var seen={};
  tl.querySelectorAll('.feed-item').forEach(function(el){seen[el.getAttribute('data-id')]=1;});
  tl.querySelectorAll('.group-extra-list a').forEach(function(a){
    var m=/items\\/([0-9a-f]+)\\.html/.exec(a.getAttribute('href')||'');
    if(m)seen[m[1]]=1;
  });
  return getDayIndex().then(function(days){
    var next=[];
    function fill(){
      while(next.length<30&&lmBuffer.length){
        var it=lmBuffer.shift();
        if(!seen[it.id])next.push(it);
      }
      if(next.length>=30||lmDayIdx>=days.length)return Promise.resolve(next);
      var d=days[lmDayIdx++];
      return getDay(d).then(function(items){lmBuffer=items.slice();return fill();});
    }
    return fill();
  }).then(function(next){
    if(!next.length){lmState.done=true;lmState.loading=false;setLoadMoreState('done');saveScrollState();return false;}
    renderBatch(next);
    lmState.loading=false;
    if(next.length<30){lmState.done=true;setLoadMoreState('done');}
    else setLoadMoreState('idle');
    saveScrollState();
    return true;
  }).catch(function(){
    lmState.loading=false;setLoadMoreState('error');
    return false;
  });
}
var loadBtn=document.getElementById('loadMoreBtn');
if(loadBtn)loadBtn.addEventListener('click',function(){loadMore();});
var sentinel=document.getElementById('loadMoreSentinel');
if(sentinel&&'IntersectionObserver' in window){
  var io=new IntersectionObserver(function(entries){
    entries.forEach(function(en){if(en.isIntersecting)loadMore();});
  },{rootMargin:'900px 0px'});
  io.observe(sentinel);
}
/* 全量搜索模式（B2/B17）：标题 > 摘要 > 来源，同级按时间倒序 */
var searchMode=false;
function enterSearchMode(){
  var sr=document.getElementById('searchResults');
  if(!sr)return;
  searchMode=true;
  ['featured','hot','timeline','loadMoreWrap','loadMoreSentinel','feedEnd','noResult'].forEach(function(id){
    var el=document.getElementById(id);if(el)el.hidden=true;
  });
  sr.hidden=false;
  renderSearchResults();
}
function exitSearchMode(){
  if(!searchMode)return;
  searchMode=false;
  ['featured','hot','timeline','loadMoreSentinel'].forEach(function(id){
    var el=document.getElementById(id);if(el)el.hidden=false;
  });
  var wrap=document.getElementById('loadMoreWrap');if(wrap)wrap.hidden=lmState.done;
  var end=document.getElementById('feedEnd');if(end)end.hidden=!lmState.done;
  var sr=document.getElementById('searchResults');if(sr)sr.hidden=true;
}
function matchFiltersData(it){
  if(state.cat==='official'&&(it.tier||(IH_CFG?IH_CFG.tiers[it.source_id]:'T2'))!=='T1')return false;
  if(state.cat==='starred'&&!starSet.has(it.id))return false;
  if(state.cat!=='all'&&state.cat!=='starred'&&state.cat!=='official'&&it.category!==state.cat)return false;
  if(state.unread&&readSet.has(it.id))return false;
  return true;
}
function renderSearchResults(){
  var srList=document.getElementById('srList'),srCount=document.getElementById('srCount');
  if(!srList)return;
  var q=state.q;
  srList.innerHTML='<p class="more-note">'+(IS_EN?'Searching…':'正在搜索…')+'</p>';
  getStore().then(function(items){
    if(state.q!==q)return;
    var scored=[];
    items.forEach(function(it){
      if(!matchFiltersData(it))return;
      var title=(((it.en_title||'')+' '+(it.zh_title||'')+' '+(it.title||''))+'').toLowerCase();
      var sum=((IS_EN?(it.en_oneliner||''):(it.zh_oneliner||''))+'').toLowerCase();
      var src=((IS_EN?(it.source_en||it.source):it.source)||'').toLowerCase();
      var tier=0;
      if(title.indexOf(q)>-1)tier=3;
      else if(sum.indexOf(q)>-1)tier=2;
      else if(src.indexOf(q)>-1)tier=1;
      if(tier)scored.push({it:it,tier:tier});
    });
    scored.sort(function(a,b){
      return b.tier-a.tier||(new Date(b.it.published)-new Date(a.it.published));
    });
    if(srCount)srCount.textContent=IS_EN?('Found '+scored.length+' items'):('找到 '+scored.length+' 条');
    if(!scored.length){
      srList.innerHTML='<div class="empty-state"><div class="empty-icon">'+SEARCH_ICON_SVG+'</div>'
        +'<h3 class="empty-title">'+(IS_EN?('No items matching "'+escHtml(state.q)+'".'):('没有匹配「'+escHtml(state.q)+'」的动态。'))+'</h3>'
        +'<p class="empty-text">'+(IS_EN?'Try another keyword, or clear the search to see everything.':'换个关键词试试，或者清除搜索看看全部。')+'</p>'
        +'<div class="empty-actions"><button type="button" class="empty-btn" data-empty-action="clear">'+(IS_EN?'Clear filters':'清除筛选')+'</button>'
        +'<button type="button" class="empty-btn primary" data-empty-action="featured">'+(IS_EN?'See featured':'去看精选')+'</button></div></div>';
      return;
    }
    var show=scored.slice(0,50);
    srList.innerHTML=show.map(function(s){return cardHTML(s.it);}).join('')
      +(scored.length>50?'<p class="more-note">'+(IS_EN?('Showing the first 50 of '+scored.length+' items.'):('只显示前 50 条，共 '+scored.length+' 条。'))+'</p>':'');
    srList.querySelectorAll('.feed-item').forEach(bindFeedItem);
  }).catch(function(){
    srList.innerHTML='<div class="empty-state"><h3 class="empty-title">'+(IS_EN?'Search is unavailable right now':'搜索暂时不可用')+'</h3>'
      +'<p class="empty-text">'+(IS_EN?'The data did not load. Refresh the page and try again.':'数据没加载出来，刷新页面再试。')+'</p></div>';
  });
}
/* 滚动恢复（B18）：从详情页/热点页返回首页时恢复滚动位置与已加载批次数 */
var SCROLL_KEY='__SLUG__-scroll';
function saveScrollState(){
  var tl=document.getElementById('timeline');
  if(!tl)return;
  try{sessionStorage.setItem(SCROLL_KEY,JSON.stringify({
    y:window.scrollY,n:tl.querySelectorAll('.feed-item').length,t:Date.now()}));}catch(e){}
}
window.addEventListener('pagehide',saveScrollState);
var scrollSaveTimer=null;
window.addEventListener('scroll',function(){
  if(scrollSaveTimer)return;
  scrollSaveTimer=setTimeout(function(){scrollSaveTimer=null;saveScrollState();},500);
},{passive:true});
function maybeRestoreScroll(){
  var tl=document.getElementById('timeline');
  if(!tl)return;
  var nav=performance.getEntriesByType&&performance.getEntriesByType('navigation')[0];
  var isBack=nav&&nav.type==='back_forward';
  var sameRef=document.referrer&&document.referrer.indexOf(location.host)>-1;
  if(!isBack&&!sameRef)return;
  var raw=null;try{raw=sessionStorage.getItem(SCROLL_KEY);}catch(e){}
  if(!raw)return;
  var st=null;try{st=JSON.parse(raw);}catch(e){}
  if(!st||!st.n||st.n<=100||Date.now()-st.t>1800000)return;
  var target=st.n;
  (function again(ok){
    var cur=tl.querySelectorAll('.feed-item').length;
    if(ok&&cur<target){loadMore().then(again);return;}
    window.scrollTo(0,st.y);
  })(true);
}
maybeRestoreScroll();
/* 同事件归组展开（B13）：事件委托，动态加载的也生效 */
document.addEventListener('click',function(e){
  var t=e.target.closest('.group-toggle');
  if(!t)return;
  var li=t.closest('.slot');
  var extra=li?li.querySelector('.group-extra'):null;
  if(!extra)return;
  var open=extra.hidden;
  extra.hidden=!open;
  t.setAttribute('aria-expanded',open?'true':'false');
  var n=extra.querySelectorAll('li').length;
  t.innerHTML=open?(IS_EN?'Collapse <span aria-hidden="true">▴</span>':'收起 <span aria-hidden="true">▴</span>'):(IS_EN?('Show '+n+' more reports <span aria-hidden="true">▾</span>'):('另有 '+n+' 篇报道 <span aria-hidden="true">▾</span>'));
});
/* 浮层搜索框的清空按钮（B14） */
var ovClear=document.getElementById('overlaySearchClear');
if(ovClear)ovClear.addEventListener('click',function(){
  if(overlayInput){overlayInput.value='';overlayInput.dispatchEvent(new Event('input'));overlayInput.focus();}
});
/* 详情页（B20）：打开即记已读；收藏；返回；复制链接；分享 */
(function(){
  var pg=document.querySelector('[data-item-id]');
  if(!pg)return;
  var id=pg.getAttribute('data-item-id');
  if(id&&!readSet.has(id)){readSet.add(id);saveSet(LS_READ,readSet);}
  var star=document.getElementById('itemStarBtn');
  if(star&&id){
    var syncStar=function(){
      var on=starSet.has(id);
      star.classList.toggle('on',on);
      var sp=star.querySelector('span');if(sp)sp.textContent=on?(IS_EN?'Saved':'已收藏'):(IS_EN?'Save':'收藏');
      star.setAttribute('aria-label',on?(IS_EN?'Unsave':'取消收藏'):(IS_EN?'Save':'收藏'));star.title=on?(IS_EN?'Unsave':'取消收藏'):(IS_EN?'Save':'收藏');
    };
    syncStar();
    star.addEventListener('click',function(){
      if(starSet.has(id)){starSet.delete(id);delete starMeta[id];}
      else{
        starSet.add(id);
        starMeta[id]={title:star.getAttribute('data-title')||'',
          link:star.getAttribute('data-link')||'',
          source:star.getAttribute('data-source')||'',at:new Date().toISOString()};
      }
      saveSet(LS_STAR,starSet);saveObj(LS_STAR_META,starMeta);
      syncStar();updateStarCounts();
    });
  }
  var back=document.getElementById('backBtn');
  if(back)back.addEventListener('click',function(){
    if(document.referrer&&document.referrer.indexOf(location.host)>-1){history.back();}
    else{location.href=back.getAttribute('data-home')||'../index.html';}
  });
  var copy=document.getElementById('copyLinkBtn');
  function fallbackCopy(text){
    var ta=document.createElement('textarea');ta.value=text;
    ta.style.position='fixed';ta.style.opacity='0';
    document.body.appendChild(ta);ta.select();
    try{document.execCommand('copy');}catch(e){}
    document.body.removeChild(ta);
  }
  if(copy)copy.addEventListener('click',function(){
    var url=location.href;
    var done=function(){copy.textContent=IS_EN?'Copied':'已复制';setTimeout(function(){copy.textContent=IS_EN?'Copy link':'复制链接';},1500);};
    if(navigator.clipboard&&navigator.clipboard.writeText){
      navigator.clipboard.writeText(url).then(done).catch(function(){fallbackCopy(url);done();});
    }else{fallbackCopy(url);done();}
  });
  var share=document.getElementById('shareBtn');
  if(share&&navigator.share){
    share.hidden=false;
    share.addEventListener('click',function(){
      navigator.share({title:document.title,url:location.href}).catch(function(){});
    });
  }
})();
})();
</script>
"""

# 外置 JS 文件内容：去掉 SCRIPT 首尾的 <script> 标签
# （行内主题启动脚本 THEME_BOOT 不受影响，继续内联在 <head> 里）
_SCRIPT_JS = SCRIPT.strip()
assert _SCRIPT_JS.startswith("<script>") and _SCRIPT_JS.endswith("</script>")
SCRIPT_JS = _SCRIPT_JS[len("<script>"):-len("</script>")].strip() + "\n"


def _storage_prefix(site):
    """localStorage 键前缀：取 site.slug，各站互不干扰。"""
    return site.get("slug", "hot")


def theme_boot(site):
    return THEME_BOOT.replace("__SLUG__-", _storage_prefix(site) + "-")


def script_js(site):
    return SCRIPT_JS.replace("__SLUG__-", _storage_prefix(site) + "-")


def _logo(size):
    return LOGO_SVG.replace('width="44" height="44"',
                            f'width="{size}" height="{size}"')


def _nav_items(prefix, base=""):
    """精选与全部动态是两个页面（对标 AIHOT / 与 /all），不再是站内锚点。
    页面链接用 PAGE_BASE（到本语言根）；prefix/base 参数保留兼容。"""
    return [
        ("featured", tr("精选", "Featured"), "zap", f"{PAGE_BASE}index.html"),
        ("all", tr("全部动态", "All updates"), "list", f"{PAGE_BASE}all.html"),
        ("hot", tr("热点榜", "Hot list"), "trend", f"{PAGE_BASE}hot.html"),
        ("daily", tr("日报", "Daily"), "doc", f"{PAGE_BASE}daily.html"),
        ("starred", tr("收藏", "Saved"), "bookmark", f"{PAGE_BASE}starred.html"),
    ]


def _side_lang_link(site, rel_path):
    """侧栏底部语言链接（左下角按钮）：中文页 English，英文页 中文；点即记住选择。"""
    href = lang_counterpart_href(rel_path)
    if not href:
        return ""
    key = _storage_prefix(site) + "-lang"
    if PAGE_LANG == "zh":
        return ('<a class="gh" href="' + href + '" onclick="try{localStorage.setItem(\'' + key + '\',\'en\')}catch(e){}">English</a>')
    return ('<a class="gh" href="' + href + '" onclick="try{localStorage.setItem(\'' + key + '\',\'zh\')}catch(e){}">中文</a>')


def sidebar_html(site, active, prefix="", base="", rel_path=""):
    items = _nav_items(prefix, base)
    links = "".join(
        f'<a class="side-link{" on" if key == active else ""}" href="{href}">'
        f'{icon(ic)}<span>{label}</span>'
        f'{"<span class=\"num\" id=\"starCount\"></span>" if key == "starred" else ""}</a>'
        for key, label, ic, href in items)
    more_links = (
        f'<a class="side-link{" on" if active == "more" else ""}" href="{PAGE_BASE}more.html">{icon("user")}<span>{tr("我的", "Mine")}</span></a>'
        f'<a class="side-link" href="{PAGE_BASE}weekly.html">{icon("calendar")}<span>{tr("周报", "Weekly")}</span></a>'
        f'<a class="side-link" href="{PAGE_BASE}monthly.html">{icon("calendar")}<span>{tr("月报", "Monthly")}</span></a>'
        f'<a class="side-link{" on" if active == "changelog" else ""}" href="{PAGE_BASE}changelog.html">{icon("doc")}<span>{tr("更新日志", "Changelog")}</span></a>'
        f'<a class="side-link{" on" if active == "about" else ""}" href="{PAGE_BASE}about.html">{icon("rss")}<span>{tr("关于", "About")}</span></a>'
        f'<a class="side-link" href="{site["repo"]}/issues" target="_blank" rel="noopener">{icon("message")}<span>{tr("反馈", "Feedback")}</span></a>'
        f'<a class="side-link" href="{ASSET_BASE}data/hot.json">{icon("code")}<span>{tr("数据 JSON", "Data JSON")}</span></a>')
    return (f'<aside class="sidebar"><a class="brand" href="{PAGE_BASE}index.html">{_logo(32)}'
            f'<span><b>{esc(site["name"])}</b><small>{esc(tr(site.get("subtitle", ""), "Global Muse usage hotspots"))}</small></span></a>'
            f'<nav aria-label="{tr("主导航", "Main navigation")}"><div class="nav-sec"><h3>{tr("内容", "Content")}</h3>{links}</div>'
            f'<div class="nav-sec"><h3>{tr("更多", "More")}</h3>{more_links}'
            f'</div></nav>'
            f'<div class="side-foot">'
            f'<a class="gh" href="{site["repo"]}" target="_blank" rel="noopener">{tr("GitHub 仓库", "GitHub Repo")}</a>'
            f'{_side_lang_link(site, rel_path)}'
            f'{_theme_btn()}'
            f'<p class="note">{tr("每天 " + esc(site["edition_time_cst"]) + " 出日报", "Daily issue at " + esc(site["edition_time_cst"]))}</p>'
            f'</div></aside>')


def rail_html(site, active, prefix="", base=""):
    items = _nav_items(prefix, base)
    links = "".join(
        f'<a class="rail-link{" on" if key == active else ""}" href="{href}">'
        f'{icon(ic, 20)}<span>{label}</span></a>'
        for key, label, ic, href in items)
    links += (f'<a class="rail-link{" on" if active == "more" else ""}" href="{PAGE_BASE}more.html">'
              f'{icon("user", 20)}<span>{tr("我的", "Mine")}</span></a>')
    return (f'<aside class="rail"><a class="brand" href="{PAGE_BASE}index.html" aria-label="{esc(tr(site["name"] + " 首页", site["name"] + " home"))}">'
            f'{_logo(28)}</a><nav aria-label="{tr("主导航", "Main navigation")}">{links}</nav></aside>')


def _theme_btn():
    return (f'<button type="button" class="icon-btn theme-btn theme-cycle" aria-label="{tr("外观：跟随系统（点击切换）", "Appearance: system (click to switch)")}">' 
            f'<span class="ic-moon">{icon("moon", 20)}</span>'
            f'<span class="ic-sun">{icon("sun", 20)}</span>'
            f'<span class="ic-monitor">{icon("monitor", 20)}</span></button>')


def topbar_html(site, active, prefix="", base="", rel_path=""):
    if active in ("daily", "weekly", "monthly"):
        center = ('<span class="title">'
                  + {"daily": tr("日报", "Daily"), "weekly": tr("周报", "Weekly"), "monthly": tr("月报", "Monthly")}[active] + '</span>')
    else:
        center = (f'<span class="switch">'
                  f'<a class="{"on" if active == "featured" else ""}" href="{PAGE_BASE}index.html">{tr("精选", "Featured")}</a>'
                  f'<a class="{"on" if active == "all" else ""}" href="{PAGE_BASE}all.html">{tr("全部", "All")}</a></span>')
    return (f'<header class="topbar"><a class="brand" href="{PAGE_BASE}index.html">{_logo(26)}<b>{site["name"]}</b></a>'
            f'{center}{lang_switch_html(rel_path)}{_theme_btn()}</header>')


def tabbar_html(active, prefix="", base=""):
    tabs = [
        ("featured", tr("精选", "Featured"), "zap", f"{PAGE_BASE}index.html"),
        ("hot", tr("热点", "Hot"), "trend", f"{PAGE_BASE}hot.html"),
        ("daily", tr("日报", "Daily"), "doc", f"{PAGE_BASE}daily.html"),
        ("all", tr("全部", "All"), "list", f"{PAGE_BASE}all.html"),
        ("starred", tr("收藏", "Saved"), "bookmark", f"{PAGE_BASE}starred.html"),
    ]
    links = "".join(
        f'<a class="{"on" if key == active else ""}" href="{href}">'
        f'{icon(ic, 20)}<span>{label}</span></a>'
        for key, label, ic, href in tabs)
    return f'<nav class="tabbar" aria-label="{tr("主导航", "Main navigation")}"><div class="tabbar-in">{links}</div></nav>'


def footer_html(site, base="", rel_path=""):
    name = esc(site["name"])
    repo = esc(site.get("repo", ""))
    note = site.get("footer_note", "")
    mcp_link = f'<a href="{PAGE_BASE}about.html">{tr("MCP 接入", "MCP Access")}</a>' if site.get("mcp_url") else ""
    tips = site.get("tips") or []
    tip_html = ""
    if tips:
        cards = ""
        for t in tips:
            lbl = (t.get("label_en") or t["label"]) if PAGE_LANG == "en" else t["label"]
            cards += (
                f'<div class="tip-card"><img class="tip-qr" src="{ASSET_BASE}{esc(t["image"])}" alt="{tr("赞赏码：", "Tip code: ")}{esc(lbl)}" width="150" height="150">'
                f'<p class="tip-label">{esc(lbl)}</p>'
                f'<p class="tip-addr">{esc(t["address"])}</p></div>')
        tip_html = (f'<div class="tip"><p class="tip-title">{tr("赞赏支持", "Support Us")}</p>'
                    f'<div class="tip-cards">{cards}</div></div>')
    return (f'<footer class="foot"><p>{tr(name + " 是聚合摘要与阅读索引，标题与摘要版权归各来源所有。内容只作资讯参考；本站不转载全文。", name + " is an aggregator and reading index. Titles and summaries belong to their original sources. Content is for reference only; full text is never republished.")}</p>'
            + (f'<p>{esc(tr(note, "Built with the HOT pipeline template, open-sourced under the MIT License."))}</p>' if note else '')
            + f'<nav class="foot-links" aria-label="{tr("页脚链接", "Footer links")}">'
            f'{lang_switch_html(rel_path)}'
            f'<a href="{ASSET_BASE}feed.xml">{tr("RSS 订阅", "RSS Feed")}</a>'
            f'{mcp_link}'
            f'<a href="{ASSET_BASE}data/days/index.json">{tr("数据 JSON", "Data JSON")}</a>'
            f'<a href="{repo}">{tr("GitHub 仓库", "GitHub Repo")}</a>'
            f'<a href="{repo}/issues">{tr("反馈", "Feedback")}</a>'
            f'<a href="{PAGE_BASE}more.html">{tr("我的", "Mine")}</a>'
            f'<a href="{PAGE_BASE}about.html">{tr("关于", "About")}</a>'
            f'<a href="{PAGE_BASE}terms.html">{tr("条款", "Terms")}</a>'
            f'<a href="{PAGE_BASE}privacy.html">{tr("隐私", "Privacy")}</a></nav>'
            f'{tip_html}</footer>')


def page_open(site, active, title, description, prefix="", base="", canonical="",
              ld_items=None, page_cls="", ld_blocks=None, og_type="website",
              extra_head="", rel_path=""):
    site_url = site.get("url", "")
    if PAGE_LANG == "en" and description == site.get("description", ""):
        description = site.get("description_en", description)
    canon_zh = canonical or site_url + "/"
    en_url = _en_url(site_url, canon_zh)
    canon_zh = _enc_url(canon_zh)
    en_url = _enc_url(en_url)
    canon = en_url if PAGE_LANG == "en" else canon_zh
    lang_attr = "en" if PAGE_LANG == "en" else "zh-CN"
    in_lang = "en" if PAGE_LANG == "en" else "zh-CN"
    if PAGE_LANG == "en":
        hreflang = (f'<link rel="alternate" hreflang="en" href="{esc(canon)}">\n'
                    f'<link rel="alternate" hreflang="zh-CN" href="{esc(canon_zh)}">\n'
                    f'<link rel="alternate" hreflang="x-default" href="{esc(canon)}">\n')
    else:
        hreflang = (f'<link rel="alternate" hreflang="zh-CN" href="{esc(canon_zh)}">\n'
                    f'<link rel="alternate" hreflang="en" href="{esc(en_url)}">\n'
                    f'<link rel="alternate" hreflang="x-default" href="{esc(en_url)}">\n')
    og = (f'<meta property="og:title" content="{esc(title)}">\n'
          f'<meta property="og:description" content="{esc(description)}">\n'
          f'<meta property="og:type" content="{og_type}">\n'
          f'<meta property="og:url" content="{esc(canon)}">\n'
          f'<meta property="og:image" content="{site_url}/assets/og-image.png">\n'
          f'<meta property="og:image:width" content="1200">\n'
          f'<meta property="og:image:height" content="630">\n'
          f'<meta name="twitter:card" content="summary_large_image">\n'
          f'<meta name="twitter:title" content="{esc(title)}">\n'
          f'<meta name="twitter:description" content="{esc(description)}">\n'
          f'<meta name="twitter:image" content="{site_url}/assets/og-image.png">\n')
    ld = {"@context": "https://schema.org", "@type": "WebSite",
          "name": site["name"], "url": site_url,
          "inLanguage": in_lang,
          "description": site.get("description_en", site.get("description", "")) if PAGE_LANG == "en" else site.get("description", "")}
    ld_parts = [json.dumps(ld, ensure_ascii=False)]
    if ld_items:
        items_ld = {"@context": "https://schema.org", "@type": "ItemList",
                    "itemListElement": [
                        {"@type": "ListItem", "position": i + 1,
                         "name": disp_title(it),
                         "url": site_url + "/items/" + it["id"] + ".html"}
                        for i, it in enumerate(ld_items[:10])]}
        ld_parts.append(json.dumps(items_ld, ensure_ascii=False))
    for block in (ld_blocks or []):
        ld_parts.append(json.dumps(block, ensure_ascii=False))
    ld_html = "".join(
        f'<script type="application/ld+json">{part}</script>\n' for part in ld_parts)
    return (f"<!DOCTYPE html>\n<html lang=\"{lang_attr}\" data-base=\"{ASSET_BASE}\"><head><meta charset=\"utf-8\">\n"
            f"<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
            f"<title>{esc(title)}</title>\n"
            f"<meta name=\"description\" content=\"{esc(description)}\">\n"
            f'<link rel="canonical" href="{esc(canon)}">\n'
            f'{hreflang}'
            f'<meta name="robots" content="index, follow, max-image-preview:large">\n'
            f'<link rel="alternate" type="application/rss+xml" title="{esc(site["name"])}" href="{site_url}/feed.xml">\n'
            f"{extra_head}"
            f'<link rel="icon" type="image/svg+xml" href="{ASSET_BASE}favicon.svg">\n'
            f'<link rel="icon" type="image/x-icon" href="{ASSET_BASE}favicon.ico">\n'
            f'<link rel="apple-touch-icon" href="{ASSET_BASE}apple-touch-icon.png">\n'
            f"{og}"
            f'{ld_html}'
            f"{theme_boot(site)}{lang_redirect_script(site, rel_path)}<link rel=\"stylesheet\" href=\"{ASSET_BASE}assets/site.css\"></head>\n<body>"
            f'<div class="shell">{sidebar_html(site, active, prefix, base, rel_path)}{rail_html(site, active, prefix, base)}'
            f'<div class="main">{topbar_html(site, active, prefix, base, rel_path)}<div class="page{page_cls}">')


def page_close(site, active, prefix="", base="", rel_path=""):
    to_top = (f'<button type="button" class="to-top" id="toTop" aria-label="{tr("回到顶部", "Back to top")}">'
              f'{icon("arrow-up", 18)}</button>')
    return (f"{footer_html(site, base, rel_path)}</div></div></div>{to_top}{tabbar_html(active, prefix, base)}<script src='{ASSET_BASE}assets/site.js'></script>{CF_BEACON}{clarity_snippet(site)}</body></html>\n")


def day_header(d, items, today, aside=False):
    is_today = d == today
    name = tr("今天", "Today") if is_today else tr(f"{d.month}月{d.day}日", f"{d.month}/{d.day}")
    date_txt = (f"{d.month}月{d.day}日") if PAGE_LANG == "zh" else f"{MONTHS_EN[d.month - 1]} {d.day}"
    cls = "day-head is-today" if is_today else "day-head"
    toggle = (f'<button type="button" class="dh-toggle" aria-label="{tr("收起/展开这一天", "Collapse/expand this day")}">'
              f'{icon("chevron-down", 14)}</button>')
    aside_html = ('<span class="dh-aside"><button type="button" class="toggle-chip unread-toggle">'
                  f'{tr("只看未读", "Unread only")}</button></span>') if aside else ""
    wd = WEEKDAYS_EN[d.weekday()] if PAGE_LANG == "en" else WEEKDAYS[d.weekday()]
    wd_short = WEEKDAYS_SHORT_EN[d.weekday()] if PAGE_LANG == "en" else WEEKDAYS_SHORT[d.weekday()]
    return (f'<header class="{cls}">'
            f'<span class="dh-name">{name}</span>'
            f'<span class="dh-date">{date_txt}</span>'
            f'{toggle}'
            f'<span class="dh-wd dh-wd-short">{wd_short}</span>'
            f'<span class="dh-wd dh-wd-full">{wd}</span>'
            f'<span class="dh-count"><b class="num">{len(items)}</b> {tr("条", "items")}</span>{aside_html}</header>')


def _norm_title(title):
    """标题归一化：去标点/空白/大小写，供同事件归组比较用。"""
    t = (title or "").lower()
    t = re.sub(r"[\s\-_·•|/\\:;,.!?？！。、，；：（）()\[\]{}“”\"'‘’<>《》]+", "", t)
    return t


def group_similar(items):
    """保守版同事件归组（B13）：只合并同一天、标题归一化后相同
    或仅差后缀（短的是长的的前缀，且长度比 ≥0.8；归一化后至少 10 字）。
    2026-11-25 把关：去掉“同一来源”限制——同一篇文章经不同订阅源
    （不同 Google 新闻查询、Google 新闻 vs 原站）入库时标题相同，
    之前因 source_id 不同各占时间线一格；跨来源合并后仍保留
    “另有 N 篇报道”展开链接。时间线归组仍只认标题本身，不用
    _same_topic（后者会把不同角度的同主题文章也并掉，时间线要的是
    完整不是精选）。返回 [{main, extra:[...]}]，顺序不变。"""
    groups = []
    for it in items:
        pub = it["_pub"].astimezone(CST).date()
        norm = _norm_title(_strip_outlet(it.get("zh_title") or it["title"]))
        merged = False
        if len(norm) >= 10:
            for g in groups:
                m = g["main"]
                if m["_pub"].astimezone(CST).date() != pub:
                    continue
                mnorm = _norm_title(_strip_outlet(m.get("zh_title") or m["title"]))
                if len(mnorm) < 10:
                    continue
                if norm == mnorm or (
                        (norm.startswith(mnorm) or mnorm.startswith(norm))
                        and min(len(norm), len(mnorm)) / max(len(norm), len(mnorm)) >= 0.8):
                    g["extra"].append(it)
                    merged = True
                    break
        if not merged:
            groups.append({"main": it, "extra": []})
    return groups


_TOPIC_STOPWORDS = set("""muse meta ai agent assistant app the a an and or of to in on for with by at from
over after before about into its it is are was were be been this that these those as new
first can could will would should may might also more most other another per via vs
says said shows show faces facing amid report reports news anyone else have has get got
make made take using used work works thing things way days day week today just still back even
really much many very well one two three also screen add adds added fix fixed issue""".split())


# _same_topic 规则 (6) 用：Meta 系社媒/通讯入口词与聊天标记。
# 背景见 _same_topic：入口 + 聊天标记双条件才算同事件，广告角度与
# 收藏整理教程因无聊天标记不受影响。
_SURFACES = ("instagram", "whatsapp", "messenger", "facebook")
_CHAT_MARKERS = ("私信", "聊天", "direct message")


def _surf_chat(it):
    """返回 (入口词集合, 是否含聊天标记)：标题+中英文简介一起看，
    同一事件的不同 outlet 措辞不同，标题里未必有标记。"""
    text = ((it.get("title") or "") + " " + (it.get("zh_title") or "")
            + " " + (it.get("zh_oneliner") or "") + " " + (it.get("en_oneliner") or "")).lower()
    surf = {w for w in _SURFACES if w in text}
    chat = any(m in text for m in _CHAT_MARKERS) or re.search(r"\bdms?\b", text) is not None
    return surf, chat


def _strip_outlet(title):
    """去掉标题末尾的 outlet 后缀（Google 新闻标题常带 " - Ars Technica"；
    outlet 名会污染同事件判定，如两家不同报道同为 "- Crypto Briefing"）。"""
    t = (title or "").strip()
    for sep in (" ——《", " —— ", " - ", " | ", " — "):
        if sep in t:
            head, tail = t.rsplit(sep, 1)
            if len(head) >= 15 and len(tail) <= 25:
                t = head.strip()
                break
    return t


def _stem_word(w):
    if len(w) > 5 and w.endswith("ing"):
        w = w[:-3]
    if len(w) > 4 and w.endswith("ers"):
        w = w[:-3]
    elif len(w) > 3 and w.endswith("s"):
        w = w[:-1]
    return w


def _canon_lat(w):
    """拉丁词规范形：与 _stem_word 一致的词干，再把复数残留的 ie→y、
    末尾 e 去掉（如 stories→storie→story、launches→launche→launch），
    供通用词比对用——否则词干 'launche' 对不上通用表里的 'launch'。"""
    w = _stem_word(w)
    if w.endswith("ie"):
        return w[:-2] + "y"
    if w.endswith("e"):
        return w[:-1]
    return w


def _is_generic_lat(w):
    """通用拉丁词判定（规范形比对）：like/month/launche 之类不算主题词。"""
    return _canon_lat(w) in _GENERIC_LAT_CANON


def _sig_tokens(text):
    """标题显著词：拉丁词（去停用词、轻量词干）+ 中文双字（只从纯 CJK 片段取，
    避免 "meta/muse" 本身拼出 me/et/ta 等垃圾双字；含“的”的双字是助词残片
    （如 的智/己的），不是主题词，直接丢弃）。"""
    t = (text or "").lower()
    lat, cjk = set(), set()
    for w in re.findall(r"[a-z0-9]+", t):
        if len(w) < 4 or w in _TOPIC_STOPWORDS:
            continue
        lat.add(_stem_word(w))
    for run in re.findall(r"[\u4e00-\u9fff]+", t):
        for i in range(len(run) - 1):
            b = run[i:i + 2]
            if "的" in b:
                continue
            cjk.add(b)
    return lat, cjk


_GENERIC_CJK = set("""智能 能体 报道 道称 用户 户的 助手 引发 指出 质疑 存在 可能 表示
一个 这个 我们 他们 可以 进行 使用 通过 以及 并且 因为 所以 就是 不是 没有
什么 怎么 如何 这样 那样 这些 那些 成为 已经 正在 还是 不过 但是 然而 此外
同时 包括 例如 比如 关于 对于 由于 因此 然后 之后 之前 现在 今天 昨天 明天
最近 目前 未来 过去 时候 方面 方式 方法 问题 情况 内容 相关 各种 那个 这里
那里 这是 也是 都是 或者 如果 虽然 尽管 推出 发布 宣布 上线 带来 自己 手把 把手 手教 教你""".split())

_GENERIC_LAT = set("""spaces space wearable wearables glasses watch watches
subscription subscriptions settings setup guide guides tutorial tutorials tips tip
review reviews analysis opinion feature features device devices app apps model models
update updates launch launches release releases voice video music photo photos chat chats
message messages search data report reports news story stories phone phones call calls
user users people person company business world week month year time thing things work
works using used make makes take takes show shows face faces issue issues screen add adds
added fix fixed""".split())

_GENERIC_LAT_CANON = {_canon_lat(w) for w in _GENERIC_LAT}


# 通用三字母缩写：标题首词是这些时不算品牌锚（如 API/SDK/GPT 是通用技术词，
# COM/NET 是 outlet 后缀残留；规则 (5) 只认非通用品牌缩写）。
_GENERIC_ACRONYMS = set("""API SDK CEO CTO CFO GPU CPU USA UK EU AI VR AR ML LLM APP WEB
IOS MAC TV PC OS IT PR GPT PDF URL HTML CSS RSS USB LED LCD SEO ADS IOT UI UX QA
CI CD AWS IBM SAP CRM ERP B2B B2C DOC XLS MP3 MP4 GIF JPG PNG SVG JSON XML SQL COM
NET ORG WWW""".split())


def _lead_acronym(it):
    """标题首词品牌缩写：_sig_tokens 丢弃 <4 字母词，muse/meta 又是停用词，
    品牌事件两标题除此无共享词时规则 (2)(3) 全漏。两种形式：
    (a) 首词即三字母全大写（如 DXL）；(b) 首词是“首字母大写词 + 两字母全大写词”
    （如 Destination XL → DXL，DXL 的全称正是 Destination XL Group）。
    取 outlet 处理后的 title / zh_title 首词，两边一致才算。
    (b) 要求第二词不在通用缩写表里（如 Meta AI 的 AI），防不同 Meta AI 报道误并。"""
    for field in ("title", "zh_title"):
        t = _strip_outlet(it.get(field) or "").strip()
        m = re.match(r"([A-Z]{3})\b", t)
        if m and m.group(1) not in _GENERIC_ACRONYMS:
            return m.group(1)
        m2 = re.match(r"([A-Z])[a-z]+ ([A-Z]{2})\b", t)
        if m2 and m2.group(2) not in _GENERIC_ACRONYMS:
            return m2.group(1) + m2.group(2)
    return None


_ANCHOR_LAT_VARIANTS = {
    "privacy": {"privacy", "private"},
    "lawsuit": {"lawsuit", "suit", "suing", "sued", "sue"},
    "signal": {"signal"},
    "encrypt": {"encrypted", "encryption", "encrypt"},
    "bank": {"bank", "balance", "balances"},
    "charm": {"charm"},
    "reuters": {"reuters"},
}
_ANCHOR_CJK = ("隐私", "加密", "银行", "余额", "起诉", "诉讼", "诉状", "路透", "信号", "泄露")

# 锚词家族：同一新闻浪潮的不同角度用不同锚词
# （如路透隐私调查：privacy / encrypt / bank / breach / flaw 各篇不同），
# 家族用于热点榜单的每族上限，规则 (4) 的同锚合并仍用上面的单个锚词。
_ANCHOR_FAMILIES = {
    "privacy": (
        {"privacy", "private", "signal", "encrypted", "encryption", "encrypt",
         "bank", "balance", "balances", "reuters", "breach", "unauthorized", "flaw"},
        ("隐私", "加密", "银行", "余额", "泄露", "路透", "信号", "缺陷", "隐患", "擅自")),
    "lawsuit": (
        {"lawsuit", "suit", "suing", "sued", "sue"},
        ("起诉", "诉讼", "诉状")),
    "charm": (
        {"charm"},
        ()),
}
_HOT_FAMILY_CAP = 2


def _anchor_families(it):
    """该条目所属的锚词家族集合（用于热点榜单每族上限）。"""
    text = " ".join([it.get("title") or "", it.get("zh_title") or "",
                     it.get("zh_oneliner") or ""]).lower()
    words = set(re.findall(r"[a-z0-9]+", text))
    fams = set()
    for name, (lat, cjk) in _ANCHOR_FAMILIES.items():
        if words & lat or any(w in text for w in cjk):
            fams.add(name)
    return fams


def cap_families(items, max_per=_HOT_FAMILY_CAP):
    """热点榜单多样性上限：按分数顺序取，每个锚词家族最多保留 max_per 条；
    无家族的条目不受限；多家族条目只有在其全部家族都已满额时才跳过
    （如 Charm 规格泄露同时属 privacy 与 charm 家族，不因 privacy 满额被误杀）。
    被跳过的条目仍在时间线与详情页里，只是 不进热点榜。"""
    kept, counts = [], {}
    for it in items:
        fams = _anchor_families(it)
        if fams and all(counts.get(f, 0) >= max_per for f in fams):
            continue
        kept.append(it)
        for f in fams:
            counts[f] = counts.get(f, 0) + 1
    return kept


def _story_anchors(it):
    """事件锚词：标题+中文标题+一句话简介里的专属事件词。
    拉丁词按变体归一（如 private/privacy、suit/suing/lawsuit），
    中文按词子串匹配（如 起诉/诉讼/诉状 各自独立，不强行归一，
    靠拉丁锚词覆盖跨语言同一事件）。"""
    text = " ".join([it.get("title") or "", it.get("zh_title") or "",
                     it.get("zh_oneliner") or ""]).lower()
    words = set(re.findall(r"[a-z0-9]+", text))
    anchors = set()
    for key, variants in _ANCHOR_LAT_VARIANTS.items():
        if words & variants:
            anchors.add("L:" + key)
    for w in _ANCHOR_CJK:
        if w in text:
            anchors.add("C:" + w)
    return anchors


def _same_topic(a, b):
    """跨来源同事件判定（2026-11-11 把关新增；2026-11-19 加强；2026-11-20 再加强）：
    (1) 原规则：归一化标题一短一长、短者是长者的前缀且至少 10 字；
    (2) 标题显著词重叠——拉丁词共享 >=2 个且至少一个 >=6 字，
        或中文双字共享 >=6 个（如两家媒体同报路透社隐私调查，
        标题措辞不同但共享 privacy/signal/message 等词）。
    (3) 2026-11-20 新增，2026-11-24 收紧：标题+一句话简介取词（简介措辞比标题更收敛），
        去掉通用双字（智能/能体/报道/用户/助手等“智能体”套话，11-24 起加
        推出/发布/宣布/上线/带来）后——
        拉丁词共享 >=2（11-24 起先去标题 outlet 后缀、去掉通用拉丁词），
        或中文双字共享 >=3，
        或共享一个强锚拉丁词（>=5 字且非通用词，如 charm/privacy/breach，
        11-24 起按规范形比对通用表，'launche' 不再漏网）
        再加 >=2 个中文双字（11-24 起由 >=1 收紧：单双字常是苹果这类高频词）。
        背景：11-20 日报 10 条里 8 条同属路透隐私调查、热点 20 条里
        11 条是 Charm 300 美元，规则 (2) 的中文阈值 6 对短中文标题过严，
        且纯中文标题没有拉丁词可共享，导致同事件漏并。
        11-24 背景：30 天库实测规则 (3) 误并——outlet 后缀、通用词、词干
        漏网三处，见代码内注释。
    (4) 2026-11-20 再新增：共享一个事件锚词且发布时间相差 <=3 天。
        背景：同一调查的不同角度改写（如隐私调查的银行余额、加密消息、
        账号混淆、擅自预订几篇）措辞几乎不重叠，规则 (2)(3) 全漏，
        实测当时热点前 20 里 0 对合并。锚词只取事件专属词
        （privacy/private、lawsuit/suit/suing、signal、encrypt、bank、
        charm、reuters，及中文 隐私/加密/银行/余额/起诉/诉讼/诉状/
        路透/信号/泄露），3 天窗口防不同事件误并。
        注意：去重只影响精选/热点/日报取前 N，时间线不受影响，
        被并掉的条目仍在时间线与详情页里。
    只用于精选/热点/日报的取前 N 去重，时间线不受影响。"""
    ta = _strip_outlet(a.get("zh_title") or a["title"])
    tb = _strip_outlet(b.get("zh_title") or b["title"])
    na = _norm_title(ta)
    nb = _norm_title(tb)
    if len(na) >= 10 and len(nb) >= 10 and (na.startswith(nb) or nb.startswith(na)):
        return True
    # (2) 2026-11-24 起标题先去 outlet 后缀：两家同为 " - BigGo Finance" 的
    # 不同事件（代打电话 vs 字节跳动竞品）会因共享 biggo/finance 被误并。
    la, ca = _sig_tokens(_strip_outlet(a.get("title") or "") + " " + _strip_outlet(a.get("zh_title") or ""))
    lb, cb = _sig_tokens(_strip_outlet(b.get("title") or "") + " " + _strip_outlet(b.get("zh_title") or ""))
    shared_lat = la & lb
    if len(shared_lat) >= 2 and any(len(w) >= 6 for w in shared_lat):
        return True
    if len(ca & cb) >= 6:
        return True
    # (3) 2026-11-20 新增，2026-11-24 收紧：标题+一句话简介取词（简介措辞比标题更收敛），
    # 去掉通用双字（智能/能体/报道/用户/助手等“智能体”套话）后——
    # 拉丁词共享 >=2，或中文双字共享 >=3，
    # 或共享一个强锚拉丁词（>=5 字且非通用词，如 charm/privacy/breach）
    # 再加 >=1 个中文双字。
    # 2026-11-24 收紧原因：实测 30 天库误并——(a) 标题 outlet 后缀（BigGo Finance）
    # 被当成共享主题词；(b) 共享拉丁词未排除通用词（like/month 就能并）；
    # (c) 强锚词干 'launche' 对不上通用表 'launch'，配通用双字 '推出' 即误并。
    # 收紧：标题先去 outlet 后缀；共享拉丁词去掉通用词；通用双字加 推出/发布/宣布/上线/带来。
    la2, ca2 = _sig_tokens(_strip_outlet(a.get("title") or "") + " " + (a.get("zh_title") or "")
                           + " " + (a.get("zh_oneliner") or ""))
    lb2, cb2 = _sig_tokens(_strip_outlet(b.get("title") or "") + " " + (b.get("zh_title") or "")
                           + " " + (b.get("zh_oneliner") or ""))
    ca2 = {c for c in ca2 if c not in _GENERIC_CJK}
    cb2 = {c for c in cb2 if c not in _GENERIC_CJK}
    shared_lat2 = {w for w in la2 & lb2 if not _is_generic_lat(w)}
    shared_cjk2 = ca2 & cb2
    if len(shared_lat2) >= 2:
        return True
    if len(shared_cjk2) >= 3:
        return True
    anchors = {w for w in shared_lat2 if len(w) >= 5}
    # 2026-11-24：强锚 + 中文双字由 >=1 改为 >=2——单双字常是“苹果”这类
    # 高频公司名/泛词（如 Apple 造智能体 vs $300 Charm 两报道只共享 apple+苹果），
    # >=1 会误并；真同事件一般共享 >=2 个中文双字。
    if anchors and len(shared_cjk2) >= 2:
        return True
    # (4) 共享事件锚词且 3 天内发布：同一调查的不同角度改写。
    pa, pb = a.get("_pub"), b.get("_pub")
    if pa is not None and pb is not None:
        try:
            if abs((pa - pb).total_seconds()) <= 3 * 86400:
                if _story_anchors(a) & _story_anchors(b):
                    return True
        except TypeError:
            pass
    # (5) 2026-11-24 新增：两标题同以一个三字母品牌缩写开头且 3 天内发布。
    # 背景：11-24 日报/热点各有 2 条 DXL（IT Brief 与 Unite.AI 角度不同），
    # _sig_tokens 丢 <4 字母词、muse/meta 是停用词，共享词为 0，规则 (2)(3)(4) 全漏。
    # 实测 30 天库：首词全大写三字母对 55 对全是 DXL 同一通稿事件，误并 0；
    # 不加首词限制时 ALM/CNA/ESP/RAM 等 outlet 后缀与提交词会误并，故只认首词。
    # 同日补：全称形式也算（Destination XL → DXL，同一家公司），否则
    # Chain Store Age 的全称版仍会与 IT Brief 的缩写版各占热点一位。
    if pa is not None and pb is not None:
        try:
            if abs((pa - pb).total_seconds()) <= 3 * 86400:
                la, lb = _lead_acronym(a), _lead_acronym(b)
                if la is not None and la == lb:
                    return True
        except TypeError:
            pass
    # (6) 2026-11-25 把关新增：同社媒/通讯入口的同事件——两标题+简介都含
    # 同一入口词（instagram/whatsapp/messenger/facebook）且都含聊天标记
    # （私信/聊天/direct message/DM），3 天内发布。
    # 背景：11-24/25 的 Instagram 私信上线有 30+ 条变体标题，措辞几乎不重叠
    # （显著词 Jaccard 0.02–0.06），规则 (2)(3) 全漏，热点前 20 里占 4 席、
    # 日报占 2 席；30 天库实测本规则只并出 1 组 23 条（全是该事件），
    # 收藏整理教程与广告角度因无聊天标记不受影响。
    # 只用于精选/热点/日报去重，不进时间线归组（见 group_similar）。
    if pa is not None and pb is not None:
        try:
            if abs((pa - pb).total_seconds()) <= 3 * 86400:
                sa, ca6 = _surf_chat(a)
                sb, cb6 = _surf_chat(b)
                if (sa & sb) and ca6 and cb6:
                    return True
        except TypeError:
            pass
    return False


def _reject_hit(kw, text):
    """排除词命中：词边界匹配（可带复数 s），如 museum 拦住 "Meta Museum"，
    amusement 拦住 "Amusement Park"，rock band 拦住乐队 Muse；
    但不拦 MuseAgent / musegadget / Museverse 等合法复合词。"""
    pat = r"(?<![a-z0-9])" + re.escape(kw.lower()) + r"s?(?![a-z0-9])"
    return re.search(pat, (text or "").lower()) is not None


def dedup_topics(items):
    """按顺序去重同事件条目，保留先出现的（调用前已按分数排好序）。"""
    kept = []
    for it in items:
        if any(_same_topic(it, k) for k in kept):
            continue
        kept.append(it)
    return kept


def timeline_slot(it, sel_ids, base=""):
    pub = it["_pub"].astimezone(CST)
    badge = it["id"] in sel_ids
    return (f'<li class="slot" data-category="{esc(it["category"])}">'
            f'<time class="slot-time" datetime="{pub.isoformat()}">{pub.strftime("%H:%M")}</time>'
            f'<span class="rail" aria-hidden="true"></span>'
            f'{feed_item(it, badge=badge, base=base)}</li>')


def timeline_group_slot(group, sel_ids, base=""):
    """归组后的时间线格：主卡 + “另有 N 篇报道”展开（B13）。"""
    main = group["main"]
    extra = group["extra"]
    slot = timeline_slot(main, sel_ids, base)
    if not extra:
        return slot
    n = len(extra)
    rows = "".join(
        f'<li><a href="{PAGE_BASE}items/{esc(e["id"])}.html">'
        f'{esc(disp_title(e))}</a>'
        f'<span class="ge-time">{esc(e["_pub"].astimezone(CST).strftime("%H:%M"))}</span></li>'
        for e in extra)
    toggle = (f'<button type="button" class="group-toggle" aria-expanded="false">'
              f'{tr(f"另有 {n} 篇报道", f"Show {n} more reports")} <span aria-hidden="true">▾</span></button>')
    extra_html = (f'<div class="group-extra" hidden><ul class="group-extra-list">{rows}</ul></div>')
    # 把展开区插进主卡的 article 末尾之前：直接拼在 slot 的 </li> 之前
    return slot[:-5] + toggle + extra_html + "</li>"


INDEX_SSR_SLOTS = 20


def _tl_sections(items, sel_ids):
    """时间线按天分组渲染（首页精选 feed 与全部动态页共用）。
    首屏只渲染前 INDEX_SSR_SLOTS 条（全渲染会让单文件超过推送上限）；
    其余由 JS 分页按需从 data/days/ 取。日期头上的条数按已渲染的算，
    否则 JS 追加时再累加会把数算重。"""
    rendered = items[:INDEX_SSR_SLOTS]
    groups = group_similar(rendered)
    days = {}
    for g in groups:
        days.setdefault(g["main"]["_pub"].astimezone(CST).date(), []).append(g)
    day_counts = {}
    for it in rendered:
        d = it["_pub"].astimezone(CST).date()
        day_counts[d] = day_counts.get(d, 0) + 1
    today = datetime.now(CST).date()
    tl_sections = ""
    for n, (d, gs) in enumerate(days.items()):
        slots = "".join(timeline_group_slot(g, sel_ids) for g in gs)
        fake_items = [None] * day_counts[d]
        tl_sections += (f'<section class="day-sec" data-date="{d.isoformat()}">'
                        f'{day_header(d, fake_items, today, aside=(n == 0))}'
                        f'<ol class="day-list">{slots}</ol></section>')
    return tl_sections


def render_index(site, cats, cfg, src_by_id, selected, hot, timeline, generated_at, counts):
    sel_ids = {it["id"] for it in selected}
    cat_opts = "".join(
        f'<button type="button" class="chip" data-filter="{c["key"]}">{esc(tr(c["label"], c.get("label_en")))}</button>'
        for c in cats)
    cat_opts += f'<button type="button" class="chip" data-filter="official">{tr("官方", "Official")}</button>'
    search_html = (f'<div class="search" role="search">{icon("search", 16)}'
                   f'<input id="siteSearch" type="text" placeholder="{tr("搜索标题、摘要…", "Search titles & summaries…")}" '
                   f'maxlength="200" autocomplete="off" aria-label="{tr("搜索标题和摘要", "Search titles and summaries")}">'
                   f'<button type="button" class="clear" id="searchClear" aria-label="{tr("清空", "Clear")}">✕</button>'
                   f'<kbd>/</kbd></div>')
    search_trigger = (f'<button type="button" class="search-trigger" aria-label="{tr("打开搜索", "Open search")}">'
                      f'{icon("search", 16)}<span>{tr("搜索标题、摘要…", "Search titles & summaries…")}</span></button>')
    overlay_cats = "".join(
        f'<button type="button" class="chip" data-filter="{c["key"]}">{esc(tr(c["label"], c.get("label_en")))}</button>'
        for c in cats)
    overlay_cats += f'<button type="button" class="chip" data-filter="official">{tr("官方", "Official")}</button>'
    overlay_hot = "".join(
        f'<li><span class="rank{" r1" if i == 0 else (" r2" if i == 1 else (" r3" if i == 2 else ""))}">{i + 1}</span>'
        f'<a href="{PAGE_BASE}items/{esc(it["id"])}.html">{esc(disp_title(it))}</a></li>'
        for i, it in enumerate(hot[:5]))
    overlay_html = (
        f'<div class="search-overlay" id="searchOverlay" hidden>'
        f'<div class="overlay-bar"><button type="button" class="icon-btn" id="overlayClose" aria-label="{tr("关闭搜索", "Close search")}">{icon("x", 20)}</button>'
        f'<div class="search overlay-search">{icon("search", 16)}'
        f'<input id="overlaySearch" type="text" placeholder="{tr("搜索标题、摘要…", "Search titles & summaries…")}" maxlength="200" autocomplete="off" aria-label="{tr("搜索标题和摘要", "Search titles and summaries")}">'
        f'<button type="button" class="clear" id="overlaySearchClear" aria-label="{tr("清空", "Clear")}">✕</button></div></div>'
        f'<div class="overlay-sec"><h3>{tr("最近搜索", "Recent searches")}</h3><div id="recentList"></div>'
        f'<button type="button" class="recent-clear" id="clearRecent">{tr("清除最近搜索", "Clear recent searches")}</button></div>'
        f'<div class="overlay-sec"><h3>{tr("按分类找", "Browse by category")}</h3><div class="overlay-cats">{overlay_cats}</div></div>'
        f'<div class="overlay-sec"><h3>{tr("正在热议", "Trending now")}</h3><ol class="overlay-hot">{overlay_hot}</ol></div>'
        f'</div>')
    sel_html = "".join(feed_item(it, badge=True) for it in selected) \
        or f"<p>{tr('今日暂无达到精选门槛的条目。', 'No items reached the featured threshold today.')}</p>"
    top5 = hot[:5]
    hot_html = "".join(hot_row(it, i + 1) for i, it in enumerate(top5)) \
        or f"<li>{tr('暂无热点。', 'No hot items yet.')}</li>"
    hot_more = (f'<a class="hot-more" href="{PAGE_BASE}hot.html">'
                f'{tr("完整榜单", "Full hot list")} <span aria-hidden="true">→</span></a>') if len(hot) > 5 else ""
    tl_sections = _tl_sections(timeline, sel_ids)
    unread_row = ('<div class="unread-row"><button type="button" class="toggle-chip unread-toggle">'
                  f'{tr("只看未读", "Unread only")}</button></div>')
    sc = cfg["scoring"]
    ih_cfg = {
        "base": sc["base"],
        "recency": sc["recency"],
        "tierBonus": sc["tier_bonus"],
        "devBonus": sc["dev_keyword_bonus"],
        "devCap": sc["dev_keyword_cap"],
        "devLabels": REASON_LABELS,
        "labelEn": LABEL_EN,
        "noiseKw": sc["noise_keywords"],
        "noisePenalty": sc["noise_keyword_penalty"],
        "noiseFloor": sc["noise_keyword_floor"],
        "tagSlugs": TAG_SLUGS,
        "tiers": {sid: s.get("tier", "T2") for sid, s in src_by_id.items()},
    }
    cfg_json = json.dumps(ih_cfg, ensure_ascii=False)
    empty_state = (
        '<div id="noResult" class="empty-state" hidden>'
        f'<div class="empty-icon" id="noResultIcon">{icon("search", 40)}</div>'
        f'<h3 class="empty-title" id="noResultTitle">{tr("这个分类下暂无动态。", "No items in this category yet.")}</h3>'
        '<p class="empty-text" id="noResultText"></p>'
        '<div class="empty-actions">'
        f'<button type="button" class="empty-btn" data-empty-action="clear">{tr("清除筛选", "Clear filters")}</button>'
        f'<button type="button" class="empty-btn primary" data-empty-action="featured">{tr("去看精选", "See featured")}</button>'
        '</div></div>')
    lede = (f'更新于 {esc(generated_at)}（北京时间）<span class="lede-rest"> · 最近 7 天共 {counts["total_7d"]} 条 · '
            f'精选 {counts["selected"]} 条 · 只显示标题与摘要，点击标题查看详情，详情页里有原文链接。</span>')
    lede_en = (f'Updated {esc(disp_zh_date(generated_at))} (Beijing Time)<span class="lede-rest"> · '
               f'{counts["total_7d"]} items in the last 7 days · {counts["selected"]} featured · '
               f'Titles and summaries only; click a title for details and the original link.</span>')
    return (page_open(site, "featured", tr(f'{disp_site_title(site)} · 今日精选与热点榜', f'{disp_site_title(site)} · Featured & Hot'),
                      site["description"], ld_items=selected, rel_path="index.html")
            + f'<div class="m-title">{tr("精选", "Featured")}</div>'
            + f'<h1>{tr("精选", "Featured")}</h1>'
            + f'<p class="lede">{tr(lede, lede_en)}</p>'
            + f'<div class="filter-row"><div class="tabs" role="tablist" aria-label="{tr("分类筛选", "Filter by category")}">'
            f'<span class="tabs-thumb" id="tabsThumb"></span>'
            f'<button type="button" class="chip on" data-filter="all">{tr("全部", "All")}</button>{cat_opts}</div>'
            + search_trigger + search_html + '</div>'
            + overlay_html
            + f'<section class="card hot-card" id="hot" aria-labelledby="hot-topics">'
            f'<div class="hot-head"><h2 id="hot-topics"><span class="live" aria-hidden="true">'
            f'<span class="ping"></span><span class="dot"></span></span>{tr("当前热点", "Hot right now")}</h2></div>'
            f'<ol class="hot-list hot-top5">{hot_html}</ol>'
            + hot_more
            + '</section>'
            + f'<div id="featured">{sel_html}</div>'
            + f'<div id="timeline">'
            + unread_row
            + tl_sections
            + '</div>'
            + f'<a class="more-row" href="{PAGE_BASE}all.html">{icon("list", 18)}'
            + f'<span class="m-label">{tr("查看全部动态", "View all updates")}</span><span class="m-arrow">›</span></a>'
            + '<div id="searchResults" hidden>'
            + f'<div class="search-results-head"><h2>{tr("搜索结果", "Search results")}</h2><span class="sr-count" id="srCount"></span></div>'
            + '<div id="srList"></div></div>'
            + empty_state
            + '<div id="loadMoreSentinel"></div>'
            + '<div class="load-more-wrap" id="loadMoreWrap">'
            + f'<button type="button" class="load-more-btn" id="loadMoreBtn">{tr("加载更多", "Load more")}</button>'
            + '<p class="load-more-state" id="loadMoreState"></p></div>'
            + f'<p class="feed-end" id="feedEnd" hidden>{tr("已经到底了", "You have reached the end")}</p>'
            + f'<script id="ihConfig" type="application/json">{cfg_json}</script>'
            + page_close(site, "featured", rel_path="index.html"))


def render_all(site, cats, cfg, src_by_id, selected, hot, pool, generated_at):
    """全部动态页（对标 AIHOT /all）：30 天全量按时间倒序、按天分组；
    首屏只渲染前 INDEX_SSR_SLOTS 条，其余由 JS 分页从 data/days/ 取。
    无精选区、无热点框；分类筛选与搜索与首页共用同一套 JS。"""
    sel_ids = {it["id"] for it in selected}
    cat_opts = "".join(
        f'<button type="button" class="chip" data-filter="{c["key"]}">{esc(tr(c["label"], c.get("label_en")))}</button>'
        for c in cats)
    cat_opts += f'<button type="button" class="chip" data-filter="official">{tr("官方", "Official")}</button>'
    search_html = (f'<div class="search" role="search">{icon("search", 16)}'
                   f'<input id="siteSearch" type="text" placeholder="{tr("搜索标题、摘要…", "Search titles & summaries…")}" '
                   f'maxlength="200" autocomplete="off" aria-label="{tr("搜索标题和摘要", "Search titles and summaries")}">'
                   f'<button type="button" class="clear" id="searchClear" aria-label="{tr("清空", "Clear")}">✕</button>'
                   f'<kbd>/</kbd></div>')
    search_trigger = (f'<button type="button" class="search-trigger" aria-label="{tr("打开搜索", "Open search")}">'
                      f'{icon("search", 16)}<span>{tr("搜索标题、摘要…", "Search titles & summaries…")}</span></button>')
    overlay_cats = "".join(
        f'<button type="button" class="chip" data-filter="{c["key"]}">{esc(tr(c["label"], c.get("label_en")))}</button>'
        for c in cats)
    overlay_cats += f'<button type="button" class="chip" data-filter="official">{tr("官方", "Official")}</button>'
    overlay_hot = "".join(
        f'<li><span class="rank{" r1" if i == 0 else (" r2" if i == 1 else (" r3" if i == 2 else ""))}">{i + 1}</span>'
        f'<a href="{PAGE_BASE}items/{esc(it["id"])}.html">{esc(disp_title(it))}</a></li>'
        for i, it in enumerate(hot[:5]))
    overlay_html = (
        f'<div class="search-overlay" id="searchOverlay" hidden>'
        f'<div class="overlay-bar"><button type="button" class="icon-btn" id="overlayClose" aria-label="{tr("关闭搜索", "Close search")}">{icon("x", 20)}</button>'
        f'<div class="search overlay-search">{icon("search", 16)}'
        f'<input id="overlaySearch" type="text" placeholder="{tr("搜索标题、摘要…", "Search titles & summaries…")}" maxlength="200" autocomplete="off" aria-label="{tr("搜索标题和摘要", "Search titles and summaries")}">'
        f'<button type="button" class="clear" id="overlaySearchClear" aria-label="{tr("清空", "Clear")}">✕</button></div></div>'
        f'<div class="overlay-sec"><h3>{tr("最近搜索", "Recent searches")}</h3><div id="recentList"></div>'
        f'<button type="button" class="recent-clear" id="clearRecent">{tr("清除最近搜索", "Clear recent searches")}</button></div>'
        f'<div class="overlay-sec"><h3>{tr("按分类找", "Browse by category")}</h3><div class="overlay-cats">{overlay_cats}</div></div>'
        f'<div class="overlay-sec"><h3>{tr("正在热议", "Trending now")}</h3><ol class="overlay-hot">{overlay_hot}</ol></div>'
        f'</div>')
    tl_sections = _tl_sections(pool, sel_ids)
    unread_row = ('<div class="unread-row"><button type="button" class="toggle-chip unread-toggle">'
                  f'{tr("只看未读", "Unread only")}</button></div>')
    sc = cfg["scoring"]
    ih_cfg = {
        "base": sc["base"],
        "recency": sc["recency"],
        "tierBonus": sc["tier_bonus"],
        "devBonus": sc["dev_keyword_bonus"],
        "devCap": sc["dev_keyword_cap"],
        "devLabels": REASON_LABELS,
        "labelEn": LABEL_EN,
        "noiseKw": sc["noise_keywords"],
        "noisePenalty": sc["noise_keyword_penalty"],
        "noiseFloor": sc["noise_keyword_floor"],
        "tagSlugs": TAG_SLUGS,
        "tiers": {sid: s.get("tier", "T2") for sid, s in src_by_id.items()},
    }
    cfg_json = json.dumps(ih_cfg, ensure_ascii=False)
    empty_state = (
        '<div id="noResult" class="empty-state" hidden>'
        f'<div class="empty-icon" id="noResultIcon">{icon("search", 40)}</div>'
        f'<h3 class="empty-title" id="noResultTitle">{tr("这个分类下暂无动态。", "No items in this category yet.")}</h3>'
        '<p class="empty-text" id="noResultText"></p>'
        '<div class="empty-actions">'
        f'<button type="button" class="empty-btn" data-empty-action="clear">{tr("清除筛选", "Clear filters")}</button>'
        f'<button type="button" class="empty-btn primary" data-empty-action="featured">{tr("去看精选", "See featured")}</button>'
        '</div></div>')
    lede = (f'更新于 {esc(generated_at)}（北京时间）<span class="lede-rest"> · 最近 30 天共 {len(pool)} 条 · '
            f'只显示标题与摘要，点击标题查看详情，详情页里有原文链接。</span>')
    lede_en = (f'Updated {esc(disp_zh_date(generated_at))} (Beijing Time)<span class="lede-rest"> · '
               f'{len(pool)} items in the last 30 days · '
               f'Titles and summaries only; click a title for details and the original link.</span>')
    return (page_open(site, "all", tr(f'{disp_site_title(site)} · 全部动态', f'{disp_site_title(site)} · All updates'),
                      site["description"], rel_path="all.html")
            + f'<div class="m-title">{tr("全部动态", "All updates")}</div>'
            + f'<h1>{tr("全部动态", "All updates")}</h1>'
            + f'<p class="lede">{tr(lede, lede_en)}</p>'
            + f'<div class="filter-row"><div class="tabs" role="tablist" aria-label="{tr("分类筛选", "Filter by category")}">'
            f'<span class="tabs-thumb" id="tabsThumb"></span>'
            f'<button type="button" class="chip on" data-filter="all">{tr("全部", "All")}</button>{cat_opts}</div>'
            + search_trigger + search_html + '</div>'
            + overlay_html
            + f'<div id="timeline">'
            + unread_row
            + tl_sections
            + '</div>'
            + '<div id="searchResults" hidden>'
            + f'<div class="search-results-head"><h2>{tr("搜索结果", "Search results")}</h2><span class="sr-count" id="srCount"></span></div>'
            + '<div id="srList"></div></div>'
            + empty_state
            + '<div id="loadMoreSentinel"></div>'
            + '<div class="load-more-wrap" id="loadMoreWrap">'
            + f'<button type="button" class="load-more-btn" id="loadMoreBtn">{tr("加载更多", "Load more")}</button>'
            + '<p class="load-more-state" id="loadMoreState"></p></div>'
            + f'<p class="feed-end" id="feedEnd" hidden>{tr("已经到底了", "You have reached the end")}</p>'
            + f'<script id="ihConfig" type="application/json">{cfg_json}</script>'
            + page_close(site, "all", rel_path="all.html"))


LAUNCH_DATE = datetime(2026, 1, 1, tzinfo=CST).date()


def issue_no(kind, date_iso):
    """期号从上线日（config 里 site.launch_date，main 中覆写 LAUNCH_DATE）起算：
    日报 = 上线天数；周报 = 上线周数；月报 = 上线月数。"""
    d = datetime.strptime(date_iso, "%Y-%m-%d").date()
    days = (d - LAUNCH_DATE).days + 1
    if kind == "daily":
        return days
    if kind == "weekly":
        return days // 7 + 1
    return (d.year - LAUNCH_DATE.year) * 12 + (d.month - LAUNCH_DATE.month) + 1


def period_summary_en(report, kind):
    """日报/周报/月报速览的英文版：新报告直接用存储的 summary_en；旧存档从中文 summary 里解析数字重组。"""
    if report.get("summary_en"):
        return report["summary_en"]
    window_en = {"daily": "In the past 24 hours", "weekly": "In the past 7 days",
                 "monthly": "In the past 30 days"}[kind]
    m = re.search(r"共收录 (\d+) 条动态，精选 (\d+) 条（([^）]*)）", report.get("summary") or "")
    if not m:
        return ""
    total, picked, cat_part = m.groups()
    cats_en = []
    for piece in cat_part.split("、"):
        mm = re.match(r"(.+) (\d+) 条$", piece.strip())
        if mm:
            cats_en.append(f"{CAT_LABEL_EN_BY_ZH.get(mm.group(1), mm.group(1))} {mm.group(2)}")
    items = report.get("items") or []
    if items:
        h0 = items[0]
        _h = h0.get("en_title") or h0.get("title", "")
        head_en = "Headline: " + _h + ("" if _h.endswith(("?", "!", ".")) else ".")
    else:
        head_en = "No featured items."
    return (f"{window_en}, {total} items collected, {picked} featured "
            f"({', '.join(cats_en) if cats_en else 'none'}). {head_en}")


def render_period(site, kind, report, base="", prev=None, next_=None, canonical="", rel_path=""):
    """日报/周报/月报共用同一模板（B9）：kind 为 daily/weekly/monthly。
    report: {kind, date, date_iso, issue, summary, items}。
    prev/next: (label, href) 或 None。base 是到站根的目录前缀。"""
    summary_txt = period_summary_en(report, kind) if PAGE_LANG == "en" else (report.get("summary") or "")
    labels = {"daily": ("日报", "过去 24 小时", "今日精选", "每天"),
              "weekly": ("周报", "过去 7 天", "本周精选", "每周"),
              "monthly": ("月报", "过去 30 天", "本月精选", "每月")}
    name, window, picked, _every = labels[kind]
    name_en = {"daily": "Daily", "weekly": "Weekly", "monthly": "Monthly"}[kind]
    window_en = {"daily": "past 24 hours", "weekly": "past 7 days", "monthly": "past 30 days"}[kind]
    picked_en = {"daily": "Today's picks", "weekly": "This week's picks", "monthly": "This month's picks"}[kind]
    if kind == "daily":
        sched_txt = tr(f"每天 {esc(site['edition_time_cst'])} 出刊", f"Published daily at {esc(site['edition_time_cst'])}")
    elif kind == "weekly":
        sched_txt = tr("过去 7 天滚动精选，每半小时更新", "Rolling 7-day picks, updated every half hour")
    else:
        sched_txt = tr("过去 30 天滚动精选，每半小时更新", "Rolling 30-day picks, updated every half hour")
    items_html = "".join(feed_item(it, rank=i + 1, base=base)
                         for i, it in enumerate(report["items"])) \
        or f"<p>{tr(f'{window}没有达到精选门槛的条目。', f'No items in the {window_en} reached the featured threshold.')}</p>"
    try:
        wd = WEEKDAYS[datetime.strptime(report["date"], "%Y年%m月%d日").weekday()]
        wd_en = WEEKDAYS_EN[datetime.strptime(report["date"], "%Y年%m月%d日").weekday()]
    except ValueError:
        wd = ""
        wd_en = ""
    wd_txt = wd_en if PAGE_LANG == "en" else wd
    nav = ""
    if prev or next_:
        pl = (f'<a href="{esc(prev[1])}">← {tr("上一期", "Previous issue")} · {esc(disp_zh_date(prev[0]))}</a>') if prev else "<span></span>"
        nl = (f'<a class="dn-next" href="{esc(next_[1])}">{tr("下一期", "Next issue")} · {esc(disp_zh_date(next_[0]))} →</a>') if next_ else ""
        nav = f'<nav class="daily-nav">{pl}{nl}</nav>'
    period_nav = (
        f'<p class="more-note">'
        f'<a href="{PAGE_BASE}daily.html">{tr("日报", "Daily")}</a> · <a href="{PAGE_BASE}weekly.html">{tr("周报", "Weekly")}</a> · '
        f'<a href="{PAGE_BASE}monthly.html">{tr("月报", "Monthly")}</a> · <a href="{PAGE_BASE}daily/archive.html">{tr("往期存档", "Archive")}</a></p>')
    issue_txt = tr(f"第 {report['issue']} 期", f"Issue {report['issue']}")
    picked_txt = tr(f"{picked} {len(report['items'])} 条", f"{picked_en}: {len(report['items'])} items")
    meta_txt = tr(f'{esc(report["date"])} {wd_txt} · {sched_txt} · {window}精选 {len(report["items"])} 条',
                  f'{esc(disp_zh_date(report["date"]))} {wd_txt} · {sched_txt} · {len(report["items"])} featured in the {window_en}')
    return (page_open(site, kind, tr(f'{site["name"]}{name} · {report["date"]}', f'{site["name"]} {name_en} · {disp_zh_date(report["date"])}'),
                      summary_txt or site["description"],
                      prefix="index.html", base=base,
                      canonical=canonical, ld_items=report["items"], page_cls=" page-reading",
                      rel_path=rel_path)
            + f'<div class="m-title">{tr(name, name_en)}</div>'
            + f'<div class="report-shell"><div class="masthead"><div class="mp-brand">'
            f'{_logo(44)}<b>{esc(site["name"])}{tr(name, name_en)}</b><span class="mp-issue">{issue_txt}</span></div>'
            + f'<p class="mp-meta">{meta_txt}</p>{period_nav}</div>'
            + f'<div class="well" style="margin-top:16px"><span class="kicker">{tr("速览", "At a glance")}</span>'
            f'<p>{esc(summary_txt)}</p></div>'
            + f'<h2 class="sec">{picked_txt}</h2>'
            + items_html + nav + "</div>"
            + page_close(site, kind, prefix="index.html", base=base, rel_path=rel_path))


def render_daily(site, daily, base="", prev=None, next_=None, canonical="", rel_path=""):
    report = dict(daily)
    report.setdefault("kind", "daily")
    report.setdefault("issue", issue_no("daily", daily.get("date_iso", LAUNCH_DATE.isoformat())))
    return render_period(site, "daily", report, base=base, prev=prev, next_=next_,
                         canonical=canonical, rel_path=rel_path)


def render_starred(site):
    """收藏页（B3）：内容由 JS 从 localStorage 快照 + data/days/ 分块渲染，
    下架条目置灰并提示；导入/导出先不做。"""
    empty_state = (
        '<div id="starEmpty" class="empty-state" hidden>'
        f'<div class="empty-icon">{icon("bookmark", 40)}</div>'
        f'<h3 class="empty-title">{tr("还没有收藏", "No saved items yet")}</h3>'
        f'<p class="empty-text">{tr("去点卡片右上角的书签，喜欢的动态就会出现在这里。", "Tap the bookmark on a card and it will show up here.")}</p>'
        '<div class="empty-actions">'
        f'<a class="empty-btn primary" href="{PAGE_BASE}index.html">{tr("去看精选", "See featured")}</a>'
        '</div></div>')
    lede = tr("收藏只保存在你的浏览器里（localStorage），换设备不会同步。",
              "Saved items live only in your browser (localStorage) and do not sync across devices.")
    lede_rest = tr("点开标题即记已读；下架的条目会置灰保留。",
                   "Opening a title marks it as read; removed items stay greyed out.")
    return (page_open(site, "starred", tr(f'{disp_site_title(site)} · 收藏', f'{disp_site_title(site)} · Saved'),
                      site["description"], prefix="index.html",
                      canonical=site.get("url", "") + "/starred.html", rel_path="starred.html")
            + f'<div class="m-title">{tr("收藏", "Saved")}</div>'
            + f'<h1>{tr("收藏", "Saved")}</h1>'
            + f'<p class="lede">{lede}<span class="lede-rest">{lede_rest}</span></p>'
            + '<div id="starList"></div>'
            + empty_state
            + page_close(site, "starred", prefix="index.html", rel_path="starred.html"))


def render_more(site, changelog_version):
    """“我的”页（B4）：收藏、外观、数据、更新日志、反馈、RSS、关于等入口收在一起。"""
    star_row = (
        f'<a class="more-row" href="{PAGE_BASE}starred.html">{icon("bookmark", 18)}'
        f'<span class="m-label">{tr("收藏", "Saved")}</span>'
        f'<span class="m-val"><span id="moreStarCount">0</span> {tr("条", "items")}</span>'
        f'<span class="m-arrow">›</span></a>')
    theme_seg = (
        f'<div class="more-row" style="cursor:default">{icon("sun", 18)}'
        f'<span class="m-label">{tr("外观", "Appearance")}</span>'
        f'<span class="theme-seg" role="group" aria-label="{tr("外观", "Appearance")}">'
        f'<span class="theme-seg-thumb" id="themeSegThumb"></span>'
        f'<button type="button" data-theme-opt="dark">{tr("深色", "Dark")}</button>'
        f'<button type="button" data-theme-opt="system">{tr("跟随系统", "System")}</button>'
        f'<button type="button" data-theme-opt="light">{tr("浅色", "Light")}</button>'
        f'</span></div>')
    data_row = (
        f'<a class="more-row" href="{ASSET_BASE}feed.xml">{icon("rss", 18)}'
        f'<span class="m-label">{tr("RSS 订阅", "RSS Feed")}</span><span class="m-val">feed.xml</span>'
        f'<span class="m-arrow">›</span></a>'
        f'<a class="more-row" href="{ASSET_BASE}data/days/index.json">{icon("code", 18)}'
        f'<span class="m-label">{tr("数据 JSON", "Data JSON")}</span><span class="m-val">{tr("30 天全量", "30 days of data")}</span>'
        f'<span class="m-arrow">›</span></a>')
    about_rows = (
        f'<a class="more-row" href="{PAGE_BASE}about.html">{icon("rss", 18)}'
        f'<span class="m-label">{tr("关于 " + site["name"], "About " + site["name"])}</span><span class="m-arrow">›</span></a>'
        f'<a class="more-row" href="{PAGE_BASE}changelog.html">{icon("doc", 18)}'
        f'<span class="m-label">{tr("更新日志", "Changelog")}</span>'
        f'<span class="dot-red" id="changelogDot" data-changelog-version="{esc(changelog_version)}" hidden></span>'
        f'<span class="m-arrow">›</span></a>'
        f'<a class="more-row" href="{site["repo"]}/issues" target="_blank" rel="noopener">{icon("message", 18)}'
        f'<span class="m-label">{tr("反馈", "Feedback")}</span><span class="m-val">GitHub Issues</span>'
        f'<span class="m-arrow">›</span></a>'
        f'<a class="more-row" href="{PAGE_BASE}terms.html">{icon("doc", 18)}'
        f'<span class="m-label">{tr("条款", "Terms")}</span><span class="m-arrow">›</span></a>'
        f'<a class="more-row" href="{PAGE_BASE}privacy.html">{icon("doc", 18)}'
        f'<span class="m-label">{tr("隐私", "Privacy")}</span><span class="m-arrow">›</span></a>')
    data_note = tr(
        f'RSS 用 feed.xml 订阅（精选 20 条，每半小时更新）。想自己拉全量数据：<a href="{ASSET_BASE}data/days/index.json">data/days/</a> 按天分块存放最近 30 天的条目，<a href="{ASSET_BASE}data/hot.json">data/hot.json</a> 是今日热点榜 Top 20。',
        f'Subscribe via feed.xml (top 20 featured, updated every half hour). To pull the full data yourself: <a href="{ASSET_BASE}data/days/index.json">data/days/</a> holds the last 30 days of items in per-day chunks, and <a href="{ASSET_BASE}data/hot.json">data/hot.json</a> is today’s Top 20 hot list.')
    return (page_open(site, "more", tr(f'{disp_site_title(site)} · 我的', f'{disp_site_title(site)} · Mine'),
                      site["description"], prefix="index.html",
                      canonical=site.get("url", "") + "/more.html", rel_path="more.html")
            + f'<div class="m-title">{tr("我的", "Mine")}</div>'
            + f'<h1>{tr("我的", "Mine")}</h1>'
            + f'<p class="lede">{tr("收藏、外观、数据与关于，都在这里。", "Saved items, appearance, data and about — all here.")}</p>'
            + f'<section class="more-sec"><h2>{tr("内容", "Content")}</h2>{star_row}'
            f'<a class="more-row" href="{PAGE_BASE}daily/archive.html">{icon("calendar", 18)}'
            f'<span class="m-label">{tr("往期日报", "Past daily issues")}</span><span class="m-arrow">›</span></a>'
            f'<a class="more-row" href="{PAGE_BASE}weekly.html">{icon("calendar", 18)}'
            f'<span class="m-label">{tr("周报", "Weekly")}</span><span class="m-arrow">›</span></a>'
            f'<a class="more-row" href="{PAGE_BASE}monthly.html">{icon("calendar", 18)}'
            f'<span class="m-label">{tr("月报", "Monthly")}</span><span class="m-arrow">›</span></a></section>'
            + f'<section class="more-sec"><h2>{tr("外观", "Appearance")}</h2>{theme_seg}</section>'
            + f'<section class="more-sec"><h2>{tr("数据与订阅", "Data & subscriptions")}</h2>{data_row}'
            f'<p class="more-note">{data_note}</p></section>'
            + f'<section class="more-sec"><h2>{tr("关于本站", "About this site")}</h2>{about_rows}</section>'
            + page_close(site, "more", prefix="index.html", rel_path="more.html"))


def render_changelog(site, entries):
    """更新日志页（B6）：由 data/changelog.json 驱动；打开即记为已读（JS）。"""
    latest = entries[0]["version"] if entries else ""
    items_html = ""
    for e in entries:
        cl_items = (e.get("items_en") or e.get("items", [])) if PAGE_LANG == "en" else e.get("items", [])
        cl_title = (e.get("title_en") or e.get("title", "")) if PAGE_LANG == "en" else e.get("title", "")
        lis = "".join(f"<li>{esc(x)}</li>" for x in cl_items)
        items_html += (
            f'<article class="cl-item"><h3>{esc(cl_title)}</h3>'
            f'<p class="cl-date">{esc(e.get("date", ""))}</p>'
            f"<ul>{lis}</ul></article>")
    return (page_open(site, "changelog", tr(f'{disp_site_title(site)} · 更新日志', f'{disp_site_title(site)} · Changelog'),
                      site["description"], prefix="index.html",
                      canonical=site.get("url", "") + "/changelog.html", rel_path="changelog.html")
            + f'<div class="m-title">{tr("更新日志", "Changelog")}</div>'
            + f'<h1>{tr("更新日志", "Changelog")}</h1>'
            + f'<p class="lede">{tr(site["name"] + " 每次改版都记在这里。", "Every change to " + site["name"] + ", logged here.")}</p>'
            + f'<div id="changelogPage" data-changelog-version="{esc(latest)}">{items_html}</div>'
            + page_close(site, "changelog", prefix="index.html", rel_path="changelog.html"))


def render_archive(site, daily_entries, weekly_entries, monthly_entries):
    """往期存档（B8/B9）：日报按月分组；周报、月报各列一组。"""
    def month_groups(entries):
        groups = {}
        for e in entries:
            ym = e["date_iso"][:7]
            groups.setdefault(ym, []).append(e)
        return groups

    def daily_section():
        if not daily_entries:
            return f"<p>{tr('还没有往期日报——从今天开始攒。', 'No past daily issues yet — starting from today.')}</p>"
        out = ""
        for ym in sorted(month_groups(daily_entries), reverse=True):
            y, m = ym.split("-")
            rows = "".join(
                f'<li><a href="{esc(e["file"])}"><span class="a-date">{disp_zh_date(e["date_short"])}</span>'
                f'<span class="a-issue">{tr("第 " + str(e["issue"]) + " 期", "Issue " + str(e["issue"]))}</span>'
                f'<span class="a-count">{tr(str(e["count"]) + " 条", str(e["count"]) + " items")}</span></a></li>'
                for e in month_groups(daily_entries)[ym])
            month_txt = (f"{y}年{int(m)}月") if PAGE_LANG == "zh" else f"{MONTHS_EN[int(m) - 1]} {y}"
            out += (f'<div class="arch-month"><h3>{month_txt}</h3>'
                    f'<ul class="arch-list">{rows}</ul></div>')
        return out

    def period_section(title, entries, label):
        if not entries:
            return ""
        rows = "".join(
            f'<li><a href="{esc(e["file"])}"><span class="a-date">{disp_zh_date(e["date_short"])}</span>'
            f'<span class="a-issue">{tr("第 " + str(e["issue"]) + " 期", "Issue " + str(e["issue"]))}</span>'
            f'<span class="a-count">{tr(str(e["count"]) + " 条", str(e["count"]) + " items")}</span></a></li>'
            for e in entries)
        return (f'<div class="arch-month"><h3>{tr(title, label)}</h3>'
                f'<ul class="arch-list">{rows}</ul></div>')

    launch_txt = ""
    if site.get("launch_date"):
        launch_txt = tr("期号从 " + esc(site.get("launch_date", "")) + " 上线日起算。",
                        "Issue numbers count from the launch on " + esc(site.get("launch_date", "")) + ".")
    return (page_open(site, "archive", tr(f'{disp_site_title(site)} · 往期存档', f'{disp_site_title(site)} · Archive'),
                      site["description"], prefix="index.html", base="../",
                      canonical=site.get("url", "") + "/daily/archive.html", rel_path="daily/archive.html")
            + f'<div class="m-title">{tr("往期存档", "Archive")}</div>'
            + f'<h1>{tr("往期存档", "Archive")}</h1>'
            + f'<p class="lede">{tr("日报、周报、月报的合订本。", "A bound collection of daily, weekly and monthly issues.")}{launch_txt}</p>'
            + f'<h2 class="sec">{tr("日报", "Daily")}</h2>' + daily_section()
            + period_section("周报", weekly_entries, "Weekly")
            + period_section("月报", monthly_entries, "Monthly")
            + page_close(site, "archive", prefix="index.html", base="../", rel_path="daily/archive.html"))


def render_topic(site, label, slug, items):
    """主题页（B11）：某标签下的条目列表。"""
    items_html = "".join(feed_item(it, base="../") for it in items) or f"<p>{tr('这个标签下暂时没有条目。', 'No items under this tag yet.')}</p>"
    return (page_open(site, "topics", f'{disp_site_title(site)} · #{disp_label(label)}',
                      tr(f"关于「{label}」的{site.get('audience', '')}动态。",
                         f"About {disp_label(label)}: {site.get('audience_en', 'Muse users and AI agent watchers')} updates."),
                      prefix="index.html", base="../",
                      canonical=site.get("url", "") + "/topics/" + slug + ".html",
                      ld_items=items, rel_path="topics/" + slug + ".html")
            + f'<div class="m-title">#{esc(disp_label(label))}</div>'
            + f'<h1>#{esc(disp_label(label))}</h1>'
            + f'<p class="lede">{tr(f"共 {len(items)} 条", f"{len(items)} items")} · <a href="../topics.html">{tr("全部主题", "All topics")} →</a></p>'
            + items_html
            + page_close(site, "topics", prefix="index.html", base="../", rel_path="topics/" + slug + ".html"))


def render_topics_index(site, tag_counts):
    """主题索引（B11）：全部标签 + 条数。"""
    rows = "".join(
        f'<a class="more-row" href="topics/{slug}.html">{icon("rss", 18)}'
        f'<span class="m-label">#{esc(disp_label(label))}</span>'
        f'<span class="m-val">{tr(str(n) + " 条", str(n) + " items")}</span><span class="m-arrow">›</span></a>'
        for label, slug, n in tag_counts)
    return (page_open(site, "topics", tr(f'{disp_site_title(site)} · 主题', f'{disp_site_title(site)} · Topics'),
                      tr(f"按主题浏览{site.get('audience', '')}动态。",
                         f"Browse {site.get('audience_en', 'Muse users and AI agent watchers')} updates by topic."),
                      prefix="index.html",
                      canonical=site.get("url", "") + "/topics.html", rel_path="topics.html")
            + f'<div class="m-title">{tr("主题", "Topics")}</div>'
            + f'<h1>{tr("主题", "Topics")}</h1>'
            + f'<p class="lede">{tr("按标签浏览：点一个标签，看它下面最近 30 天的动态。", "Browse by tag: pick one to see its items from the last 30 days.")}</p>'
            + (f'<section class="more-sec">{rows}</section>' if rows else f"<p>{tr('暂无标签。', 'No tags yet.')}</p>")
            + page_close(site, "topics", prefix="index.html", rel_path="topics.html"))


def render_simple_page(site, active, title, lede, blocks, canonical_path, title_en=None, lede_en=None, blocks_en=None):
    """静态文案页（B5 关于 / C4 条款与隐私）共用骨架。英文站有 blocks_en 时用英文正文。"""
    body = ""
    show_blocks = blocks_en if (PAGE_LANG == "en" and blocks_en) else blocks
    for h, paras in show_blocks:
        ps = "".join(f"<p>{p}</p>" for p in paras)
        body += (f'<h2 class="sec">{esc(h)}</h2>' if h else "") + ps
    return (page_open(site, active, tr(f'{disp_site_title(site)} · {title}', f'{disp_site_title(site)} · {title_en or title}'),
                      site["description"], prefix="index.html",
                      canonical=site.get("url", "") + "/" + canonical_path, rel_path=canonical_path)
            + f'<div class="m-title">{esc(tr(title, title_en))}</div>'
            + f'<h1>{esc(tr(title, title_en))}</h1>'
            + f'<p class="lede">{esc(tr(lede, lede_en))}</p>'
            + body
            + page_close(site, active, prefix="index.html", rel_path=canonical_path))


def render_about(site):
    name = site.get("name", "HOT")
    audience = site.get("audience", "")
    blocks = site.get("about_blocks") or [
        {"h": "定位", "paras": [f"{name} 是给{audience}看的热点站。"]},
        {"h": "怎么做", "paras": ["采集——公开 RSS 信源，每半小时拉一次。",
                            "打分——规则打分（时效、相关度、来源），不是 AI 打分。",
                            "出报——只展示标题、摘要与原文链接，不转载全文。"]},
    ]
    pairs = [(b.get("h", ""), b.get("paras", [])) for b in blocks]
    blocks_en = site.get("about_blocks_en")
    pairs_en = [(b.get("h", ""), b.get("paras", [])) for b in blocks_en] if blocks_en else None
    mcp_url = site.get("mcp_url", "")
    if mcp_url:
        pairs.append(("MCP 接入", [
            "本站提供 MCP（Model Context Protocol）接入点，AI 客户端可以直接查热点、日报、搜索最近动态——返回的同样只有标题、一句简介与原文链接。",
            f"端点：<code>{esc(mcp_url)}</code>（Streamable HTTP，无需密钥）。",
            "三个工具：get_hot（当前热点榜）、get_daily（最新一期日报）、search_items（按关键词与分类搜索最近动态）。",
            "以 Claude Desktop 为例，在配置文件里加一个 mcpServers 项，type 填 http，url 填上面这个端点即可。"]))
        if pairs_en is not None:
            pairs_en.append(("MCP Access", [
                "This site provides an MCP (Model Context Protocol) endpoint, so AI clients can query the hot list, daily issues and search recent items directly — returning only titles, one-line summaries and original links.",
                f"Endpoint: <code>{esc(mcp_url)}</code> (Streamable HTTP, no API key needed).",
                "Three tools: get_hot (current hot list), get_daily (latest daily issue), search_items (search recent items by keyword and category).",
                "For Claude Desktop, add an mcpServers entry in your config file with type http and the endpoint URL above."]))
    return render_simple_page(site, "about", "关于", f"{name} 是什么、怎么做、谁做的。", pairs, "about.html",
                              title_en="About", lede_en=f"What {name} is, how it works, and who makes it.",
                              blocks_en=pairs_en)


def render_terms(site):
    return render_simple_page(site, "terms", "条款", "使用本站前请先了解这些。", [
        ("", ["本站为信息聚合，内容来自各家公开 RSS；站内只展示标题、摘要与原文链接，不转载全文。",
              "内容版权归原作者所有。",
              "如有内容不妥或希望下架，请通过 GitHub Issues 联系，我们会尽快处理。"]),
    ], "terms.html", title_en="Terms", lede_en="Please read this before using the site.",
        blocks_en=[("", ["This site is an information aggregator; content comes from public RSS feeds. "
                         "Only titles, summaries and original links are shown; full text is never republished.",
                         "Content copyright belongs to the original authors.",
                         "If any content is inappropriate or you want something taken down, "
                         "contact us via GitHub Issues and we will handle it promptly."])])


def render_privacy(site):
    return render_simple_page(site, "privacy", "隐私", "本站如何对待你的数据。", [
        ("", ["本站不收集、不上传任何个人信息。",
              "收藏与已读记录只保存在你自己的浏览器里（localStorage），清除浏览器数据即清除。"]),
    ], "privacy.html", title_en="Privacy", lede_en="How this site treats your data.",
        blocks_en=[("", ["This site does not collect or upload any personal information.",
                         "Saved and read records live only in your own browser (localStorage); "
                         "clearing browser data clears them."])])


def render_item(site, it, related, is_selected, daily_issue):
    """文章详情页（items/<id>.html）：只有标题、一句话简介、来源、评分、理由、标签、
    相关条目——不编造正文，不转载全文，不展示源站摘要或完整摘要原文。
    导读就是本站自己写的一句话简介；没有简介时只显示标题与链接，
    原文只通过“打开原文”按钮出去。英文站标题优先 en_title、一句话简介用 en_oneliner。"""
    site_url = site.get("url", "")
    title = disp_title(it)
    # “原文标题”去掉源站 RSS 常带的媒体后缀（如“ - 디지털투데이”“ - SBS 뉴스”），
    # 只显示原标题本身；_strip_outlet 与去重用的同一规则（末尾短尾缀才剥离）。
    en_title = _strip_outlet(it["title"]) if (PAGE_LANG == "zh" and it.get("zh_title") and it["zh_title"] != it["title"]) else ""
    oneliner = disp_oneliner(it)
    desc = oneliner if oneliner else title
    pub = _pub_dt(it)
    domain = urllib.parse.urlparse(it["link"]).netloc
    canonical = f"{site_url}/items/{it['id']}.html"
    mid_name = tr("精选", "Featured") if is_selected else tr("全部动态", "All updates")
    mid_href = "/" if is_selected else "/all.html"
    in_lang = "en" if PAGE_LANG == "en" else "zh-CN"
    ld_blocks = [
        {"@context": "https://schema.org", "@type": "Article",
         "headline": title, "description": desc,
         "datePublished": pub.astimezone(timezone.utc).isoformat(),
         "dateModified": pub.astimezone(timezone.utc).isoformat(),
         "inLanguage": in_lang,
         "author": {"@type": "Organization", "name": disp_source(it)},
         "publisher": {"@type": "Organization", "name": site["name"]},
         "image": site_url + "/assets/og-image.png",
         "mainEntityOfPage": canonical},
        {"@context": "https://schema.org", "@type": "BreadcrumbList",
         "itemListElement": [
             {"@type": "ListItem", "position": 1, "name": tr("首页", "Home"),
              "item": site_url + "/"},
             {"@type": "ListItem", "position": 2, "name": mid_name,
              "item": site_url + mid_href},
             {"@type": "ListItem", "position": 3, "name": title,
              "item": canonical}]},
    ]
    meta = (f'<span class="src">{esc(disp_source(it))}</span>'
            + (f'<span class="off-tag">{tr("官方", "Official")}</span>' if it.get("tier") == "T1" else "")
            + f'<time>· {esc(fmt_cst(pub))}</time>'
            + (f'<span class="pick">{tr("精选", "Featured")}</span>' if is_selected else "")
            + f'<span class="sp">{score_pill(it["score"])}</span>')
    en_html = (f'<p class="item-en-title">{tr("原文标题：", "Original title: ")}{esc(en_title)}</p>' if en_title else "")
    # 导读：只显示本站自己写的一句话简介；没有简介时不展示任何源站摘要文字。
    guide_text = oneliner
    guide_attr = ' lang="en"' if (PAGE_LANG == "en" and guide_text) else ""
    reason_html = (f'<section class="item-sec"><h2>{tr("推荐理由", "Why it matters")}</h2>'
                   f'<p>{esc(disp_reason(it))}</p></section>' if disp_reason(it) else "")
    tags_html = ""
    tags = it.get("tags") or []
    if tags:
        tags_html = (f'<section class="item-sec"><h2>{tr("主题", "Topics")}</h2><div class="fi-tags">' + "".join(
            f'<a class="tag" href="../topics/{TAG_SLUGS.get(t, t)}.html">#{esc(disp_label(t))}</a>'
            for t in tags[:3]) + '</div></section>')
    issue_html = ""
    if daily_issue:
        issue_html = (f'<p class="item-source-line">{tr("收录于", "In ")}'
                      f'<a href="../daily/{daily_issue["key"]}.html">{tr("日报第 " + str(daily_issue["issue"]) + " 期", "Daily issue " + str(daily_issue["issue"]))}'
                      f'{tr("（" + esc(daily_issue["date"]) + "）", "(" + esc(disp_zh_date(daily_issue["date"])) + ")")}</a></p>')
    related_html = ""
    if related:
        cards = "".join(feed_item(r, base="../") for r in related)
        related_html = (f'<section class="item-sec"><h2>{tr("相关条目", "Related items")}</h2>'
                        f'<div class="item-related-list">{cards}</div></section>')
    pub_iso = pub.astimezone(timezone.utc).isoformat()
    article_head = (f'<meta property="article:published_time" content="{pub_iso}">\n'
                    f'<meta property="article:modified_time" content="{pub_iso}">\n'
                    f'<meta property="article:author" content="{esc(site["name"])}">\n')
    save_lbl = tr("收藏", "Save")
    return (page_open(site, "all", f"{title} · {site['name']}", desc,
                      prefix="index.html", base="../", canonical=canonical,
                      page_cls=" page-reading", ld_blocks=ld_blocks,
                      og_type="article", extra_head=article_head,
                      rel_path=f"items/{it['id']}.html")
            + f'<article class="item-page" data-item-id="{esc(it["id"])}">'
            + f'<button type="button" class="item-back" id="backBtn" data-home="../index.html">← {tr("返回", "Back")}</button>'
            + f'<div class="item-meta">{meta}</div>'
            + f'<h1 class="item-h1">{esc(title)}</h1>'
            + en_html
            + f'<div class="well item-guide"><span class="kicker">{tr("导读", "Summary")}</span>'
            + (f'<p{guide_attr}>{esc(guide_text)}</p>' if guide_text else f'<p>{tr("这条动态暂无简介，点“打开原文”查看。", "No summary for this item yet — open the original to read it.")}</p>')
            + '</div>'
            + reason_html
            + f'<div class="item-actions">'
            f'<a class="item-open-btn" href="{esc(it["link"])}" target="_blank" rel="noopener">{tr("打开原文", "Read original")} ↗</a>'
            f'<button type="button" class="item-ghost-btn" id="itemStarBtn" data-id="{esc(it["id"])}" '
            f'data-title="{esc(title)}" data-link="{esc(it["link"])}" data-source="{esc(disp_source(it))}">'
            f'{icon("bookmark", 16)}<span>{save_lbl}</span></button>'
            f'<button type="button" class="item-ghost-btn" id="copyLinkBtn">{tr("复制链接", "Copy link")}</button>'
            f'<button type="button" class="item-ghost-btn" id="shareBtn" hidden>{tr("分享", "Share")}</button>'
            f'</div>'
            + f'<p class="item-source-line">{tr("来源：", "Source: ")}<b>{esc(disp_source(it))}</b> · {esc(domain)}</p>'
            + issue_html
            + tags_html
            + related_html
            + '</article>'
            + page_close(site, "all", prefix="index.html", base="../", rel_path=f"items/{it['id']}.html"))


def render_404(site):
    """GitHub Pages 缺页处理：简单独立页（链接用绝对地址，任何缺页路径下都可用）。"""
    site_url = site.get("url", "")
    return (f"<!DOCTYPE html>\n<html lang=\"zh-CN\"><head><meta charset=\"utf-8\">\n"
            f"<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
            f"<title>找不到这篇内容 · {site['name']}</title>\n"
            f"<meta name=\"description\" content=\"找不到这篇内容。\">\n"
            f'<link rel="icon" type="image/svg+xml" href="{site_url}/favicon.svg">\n'
            f'<link rel="icon" type="image/x-icon" href="{site_url}/favicon.ico">\n'
            f'<link rel="apple-touch-icon" href="{site_url}/apple-touch-icon.png">\n'
            f"{theme_boot(site)}<link rel=\"stylesheet\" href=\"{site_url}/assets/site.css\"></head>\n<body>"
            f'<div class="shell"><div class="main"><div class="page page-reading">'
            f'<div class="empty-state" style="margin-top:20vh">'
            f'<div class="empty-icon">{icon("search", 40)}</div>'
            f'<h3 class="empty-title">找不到这篇内容</h3>'
            f'<p class="empty-text">链接可能有误，或者这篇内容已经下架。</p>'
            f'<div class="empty-actions">'
            f'<a class="empty-btn primary" href="{site_url}/index.html">回首页</a>'
            f'<a class="empty-btn" href="{site_url}/hot.html">去看热点榜</a>'
            f'</div></div></div></div></div>{CF_BEACON}{clarity_snippet(site)}</body></html>\n')


def render_hot(site, hot, generated_at, counts, cfg):
    """完整热点榜：No.1 头条大卡 + No.2–3 次卡 + No.4–20 带 Delta 的行 + 方法说明（B1）。"""
    sc = cfg["scoring"]
    hero = ""
    subs = ""
    rest = ""
    if hot:
        h0 = hot[0]
        latest = disp_oneliner(h0)
        hero = (
            f'<article class="card hot-hero"><div class="hot-hero-top">'
            f'<span class="no-tag">NO.01</span>{hot_badges(h0)}</div>'
            f'<h2><a href="{PAGE_BASE}items/{esc(h0["id"])}.html">'
            f'{esc(disp_title(h0))}</a></h2>'
            f'<p class="hot-hero-meta">{esc(disp_source(h0))} · {esc(fmt_cst(_pub_dt(h0)))} · '
            f'{esc(cat_label(h0))}</p>'
            + (f'<p class="hot-hero-latest"><span class="k">{tr("最新进展", "Latest")}</span>{esc(shorten(latest, 110))}</p>'
               if latest else "")
            + f'<div class="hot-hero-foot"><span class="hot-big"><b class="num">{round(h0["hot_score"])}</b>{tr("热度", " Heat")}</span>'
            f'{hot_delta_html(h0)}{score_pill(h0["score"])}</div></article>')
    if len(hot) > 1:
        sub_cards = ""
        for i, it in enumerate(hot[1:3], start=2):
            sub_cards += (
                f'<article class="card hot-sub"><div class="hot-sub-top">'
                f'<span class="no-tag">NO.{i:02d}</span>{hot_badges(it)}</div>'
                f'<h3><a href="{PAGE_BASE}items/{esc(it["id"])}.html">'
                f'{esc(disp_title(it))}</a></h3>'
                f'<p class="hot-sub-meta">{esc(disp_source(it))} · {esc(fmt_cst(_pub_dt(it)))}</p>'
                f'<div class="hot-sub-foot"><span class="hot-num"><b class="num">{round(it["hot_score"])}</b> {tr("热度", "Heat")}</span>'
                f'{hot_delta_html(it)}</div></article>')
        subs = f'<div class="hot-sub-grid">{sub_cards}</div>'
    if len(hot) > 3:
        rows = "".join(hot_row(it, i + 1, pad=True) for i, it in enumerate(hot[3:], start=3))
        rest = (f'<section class="card hot-card" aria-labelledby="hot-rest" style="margin-top:12px">'
                f'<ol class="hot-list">{rows}</ol></section>')
    elif not hot:
        rest = f"<p>{tr('暂无热点。', 'No hot items yet.')}</p>"
    rec = sc["recency"]
    rec_txt = "、".join(f'{r["max_hours"]} 小时内 +{r["bonus"]}' for r in rec)
    rec_txt_en = ", ".join(f'+{r["bonus"]} within {r["max_hours"]}h' for r in rec)
    tier_txt = f'官方信源 +{sc["tier_bonus"].get("T1", 0)}'
    tier_txt_en = f'Official sources +{sc["tier_bonus"].get("T1", 0)}'
    if "T3" in sc["tier_bonus"]:
        tier_txt += f'；T3 信源 {sc["tier_bonus"]["T3"]}'
        tier_txt_en += f'; T3 sources {sc["tier_bonus"]["T3"]}'
    method_txt = (
        f'每条动态先按规则打分：基础 {sc["base"]} 分；新鲜度（{rec_txt}）；'
        f'{tier_txt}；命中主题关键词（{"、".join(sc["dev_keywords"])}）'
        f'每个 +{sc["dev_keyword_bonus"]}、上限 +{sc["dev_keyword_cap"]}；噪音关键词每个 {sc["noise_keyword_penalty"]}、'
        f'下限 {sc["noise_keyword_floor"]}；总分封顶 100 分。热度 = 评分 × {sc["decay_base"]}'
        f'^天数（每天衰减），只看最近 {sc["hot_days"]} 天。趋势对照上一轮榜单：名次上升 2 名以上为上升，'
        f'下降 2 名以上为回落，只挪 1 名算持平；首次上榜标“新”。')
    method_txt_en = (
        f'Each item is scored by rules: base {sc["base"]} points; freshness ({rec_txt_en}); '
        f'{tier_txt_en}; matching topic keywords ({", ".join(k for k in sc["dev_keywords"] if k.isascii())}) '
        f'+{sc["dev_keyword_bonus"]} each, capped at +{sc["dev_keyword_cap"]}; noise keywords '
        f'{sc["noise_keyword_penalty"]} each, floor {sc["noise_keyword_floor"]}; total capped at 100. '
        f'Heat = score × {sc["decay_base"]}^days (decaying daily), looking at the last {sc["hot_days"]} days. '
        f'Trends compare with the previous list: up 2+ places is rising, down 2+ is falling, '
        f'1 place is flat; first-time entries are marked "New".')
    method = (
        f'<section class="well hot-method"><span class="kicker">{tr("热度是怎么算的？", "How is heat calculated?")}</span>'
        f'<p>{tr(method_txt, method_txt_en)}</p></section>')
    lede = (f'更新于 {esc(generated_at)}（北京时间）<span class="lede-rest"> · 最近 7 天共 {counts["total_7d"]} 条 · '
            f'热度按评分随时间衰减，趋势对照上一轮榜单。</span>')
    lede_en = (f'Updated {esc(disp_zh_date(generated_at))} (Beijing Time)<span class="lede-rest"> · '
               f'{counts["total_7d"]} items in the last 7 days · '
               f'Heat decays from score over time; trends compare with the previous list.</span>')
    return (page_open(site, "hot", tr(f'{disp_site_title(site)} · 热点榜', f'{disp_site_title(site)} · Hot list'),
                      site["description"], prefix="index.html",
                      canonical=site.get("url", "") + "/hot.html", ld_items=hot, rel_path="hot.html")
            + f'<div class="m-title">{tr("热点榜", "Hot list")}</div>'
            + f'<h1>{tr("热点榜", "Hot list")}</h1>'
            + f'<p class="lede">{tr(lede, lede_en)}</p>'
            + hero + subs + rest + method
            + page_close(site, "hot", prefix="index.html", rel_path="hot.html"))


def rss_date(dt):
    return dt.astimezone(timezone.utc).strftime("%a, %d %b %Y %H:%M:%S GMT")


def build_feed_xml(site, items):
    """RSS 2.0（B12）：精选 20 条，每轮都写。"""
    site_url = site.get("url", "")
    now_rfc = rss_date(datetime.now(timezone.utc))
    chan_title = site.get("title", site.get("name", "HOT"))
    chan_desc = site.get("description", "")
    items_xml = ""
    for it in items[:20]:
        title = it.get("zh_title") or it["title"]
        desc = it.get("zh_oneliner") or ""
        pub = _pub_dt(it)
        items_xml += ("<item><title>" + esc(title) + "</title>"
                      "<link>" + esc(it["link"]) + "</link>"
                      "<description>" + esc(desc) + "</description>"
                      "<pubDate>" + rss_date(pub) + "</pubDate>"
                      "<guid isPermaLink=\"false\">" + esc(it["id"]) + "</guid>"
                      "<source url=\"" + esc(it["link"]) + "\">" + esc(it["source"]) + "</source>"
                      "</item>")
    return ("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
            "<rss version=\"2.0\"><channel>"
            "<title>" + esc(chan_title) + "</title>"
            "<link>" + esc(site_url) + "/</link>"
            "<description>" + esc(chan_desc) + "</description>"
            "<language>zh-CN</language>"
            "<lastBuildDate>" + now_rfc + "</lastBuildDate>"
            + items_xml +
            "</channel></rss>\n")


def load_period_archive(dirpath):
    """读回某类（daily/weekly/monthly）已存档的报告，按 date_iso 倒序。"""
    reports = []
    if not os.path.isdir(dirpath):
        return reports
    for fn in sorted(os.listdir(dirpath)):
        if not fn.endswith(".json"):
            continue
        try:
            r = load_json(os.path.join(dirpath, fn))
            if r.get("date_iso"):
                reports.append(r)
        except (json.JSONDecodeError, KeyError, OSError):
            continue
    reports.sort(key=lambda r: r["date_iso"], reverse=True)
    return reports


def enrich_report_items(reports, history):
    """旧存档报告的条目可能没有新加的翻译字段（en_title/en_oneliner），按 id 从当前 store 补齐。"""
    for rep in reports:
        for it in rep.get("items", []):
            src = history.get(it.get("id", ""))
            if not src:
                continue
            for k in ("zh_title", "zh_oneliner", "en_title", "en_oneliner"):
                if not it.get(k) and src.get(k):
                    it[k] = src[k]


# ---------------------------------------------------------------- SEO / GEO
# 搜索引擎与 AI 引用用的生成物：robots.txt、sitemap.xml、llms.txt、geo-audit。
# 全部取自 config.json，不写死任何站名、域名与端点；mirror_url / mcp_url
# 为空时对应行段直接省略，不输出占位 URL。hreflang 只写 zh-CN + x-default，
# 本站没有英文页，绝不写 hreflang="en"。

def _sitemap_lastmod(sub, fn, default):
    """按存档文件名推算真实 lastmod：daily=YYYY-MM-DD，monthly=当月 1 日，
    weekly=ISO 周的周一；解析失败时用默认值。"""
    stem = fn[:-5] if fn.endswith(".html") else fn
    try:
        if sub == "daily":
            return datetime.strptime(stem, "%Y-%m-%d").strftime("%Y-%m-%d")
        if sub == "monthly":
            return datetime.strptime(stem, "%Y-%m").strftime("%Y-%m-%d")
        if sub == "weekly":
            y, w = stem.split("-W")
            return datetime.fromisocalendar(int(y), int(w), 1).strftime("%Y-%m-%d")
    except (ValueError, AttributeError):
        return default
    return default


def build_robots_txt(site):
    """完整版 robots.txt：明确放行主流 AI 爬虫，禁 Bytespider / PetalBot。

    站名、规范域名、镜像地址全部取自 config.json 的 site 段；
    mirror_url 为空时不写镜像行。
    """
    site_url = site.get("url", "")
    name = site.get("name", "")
    mirror_url = (site.get("mirror_url") or "").rstrip("/")
    allow_bots = ["GPTBot", "ChatGPT-User", "OAI-SearchBot", "ClaudeBot",
                  "Claude-Web", "PerplexityBot", "Perplexity-User",
                  "Google-Extended", "CCBot", "Meta-ExternalAgent",
                  "Applebot-Extended"]
    deny_bots = ["Bytespider", "PetalBot"]
    lines = [f"# {name} — 允许搜索引擎与 AI 爬虫抓取公开内容",
             f"# 规范域名为 {site_url}/"]
    if mirror_url:
        lines.append(f"# 镜像 {mirror_url} 内容相同，请以规范域名为准")
    lines += ["# 给 AI 看的站点说明见 llms.txt（站根 /llms.txt）",
              "",
              "User-agent: *",
              "Allow: /",
              ""]
    for bot in allow_bots:
        lines += [f"User-agent: {bot}", "Allow: /", ""]
    for bot in deny_bots:
        lines += [f"User-agent: {bot}", "Disallow: /", ""]
    lines.append(f"Sitemap: {site_url}/sitemap.xml")
    return "\n".join(lines) + "\n"


def build_llms_txt(site, cats, today_iso):
    """llms.txt：站点说明 + 机器可读入口 + 分类（分类取自 config.json）。

    介绍段首行取 site.tagline（建站时改成新站自己的一句话）；其余为通用
    英文说明，只依赖站名，不依赖任何站点的主题措辞。分类行用可选的
    label_en（无 label_en 时只写中文 label）。mcp_url 为空时不写 MCP 段，
    改写纯数据入口段；mirror_url 为空时不写 Mirror 行。
    """
    site_url = site.get("url", "")
    name = site.get("name", "")
    mirror_url = (site.get("mirror_url") or "").rstrip("/")
    mcp_url = site.get("mcp_url") or ""
    tagline = site.get("tagline") or ""
    intro_lines = []
    if tagline:
        intro_lines.append(f"> {tagline}")
    intro_lines += [
        f"> {name} is a daily curated digest. Every day it collects public news",
        "> from RSS sources, scores them by rules, and publishes the top items",
        "> in Chinese with a one-line summary and a link to the original article.",
        "> It does not republish full text.",
        f"> Site: {site_url}/",
    ]
    if mirror_url:
        intro_lines.append(f"> Mirror: {mirror_url}/")
    intro_lines += [
        "> Language: Chinese (zh-CN). English version: /en/.",
        f"> Updated: {today_iso}",
    ]
    intro_txt = "\n".join(intro_lines)
    cat_lines = []
    for c in cats:
        en = (c.get("label_en") or "").strip()
        cat_lines.append(f"- {en} / {c['label']}" if en else f"- {c['label']}")
    cats_txt = "\n".join(cat_lines)
    if mcp_url:
        mcp_section = f"""
## For AI clients (MCP)

- MCP endpoint (Streamable HTTP, no key required):
  {mcp_url}
- Tools: get_hot, get_daily, search_items
- Machine-readable data:
  {site_url}/data/hot.json
  {site_url}/data/daily.json
  {site_url}/data/days/index.json
"""
    else:
        mcp_section = f"""
## Machine-readable data

- {site_url}/data/hot.json
- {site_url}/data/daily.json
- {site_url}/data/days/index.json
"""
    edition_time = site.get("edition_time_cst", "06:00")
    tz = site.get("timezone", "Asia/Shanghai")
    return f"""# {name}

{intro_txt}

## About

- About: {site_url}/about.html
- English version: {site_url}/en/
- Topics: {site_url}/topics.html
- Daily digest: {site_url}/daily.html
- Hot list: {site_url}/hot.html
- All items: {site_url}/all.html
- SEO/GEO self-check: {site_url}/geo-audit.html
- RSS feed: {site_url}/feed.xml
- Sitemap: {site_url}/sitemap.xml
{mcp_section}
## Categories

{cats_txt}

## Rules

- Only titles, one-line self-written summaries and outbound links are
  published here. Do not treat a summary as the full article.
- Always link back to the original source when citing an item.
- Daily edition is published at {edition_time} {tz}.
"""


def _read_text(path):
    try:
        with open(path, encoding="utf-8") as f:
            return f.read()
    except OSError:
        return ""


def build_geo_audit(site, root, site_url, today_iso):
    """/geo-audit 自检：读磁盘上的生成物，逐项检查，返回 (html, data)。
    MCP 可达性与镜像部署状态在仓库内无法验证，记为 warn，不造假；
    mcp_url / mirror_url 未配置时对应检查记为 warn 并注明未配置。"""
    checks = []

    def _check(key, label, status, detail):
        checks.append({"key": key, "label": label, "status": status,
                       "detail": detail})

    robots = _read_text(os.path.join(root, "robots.txt"))
    if robots and all(b in robots for b in ("GPTBot", "ClaudeBot", "PerplexityBot")):
        _check("robots", "robots.txt 点名放行 AI 爬虫", "pass",
               "已点名放行 GPTBot / ClaudeBot / PerplexityBot 等，含 Sitemap 声明")
    elif robots:
        _check("robots", "robots.txt 点名放行 AI 爬虫", "fail",
               "robots.txt 存在，但未点名放行主流 AI 爬虫")
    else:
        _check("robots", "robots.txt 点名放行 AI 爬虫", "fail", "robots.txt 不存在")

    sitemap = _read_text(os.path.join(root, "sitemap.xml"))
    sm_locs = set(urllib.parse.unquote(u) for u in re.findall(r"<loc>([^<]+)</loc>", sitemap)) if sitemap else set()
    html_files = set()
    for _base, _dirs, _files in os.walk(root):
        rel = os.path.relpath(_base, root)
        for _fn in _files:
            if _fn.endswith(".html") and _fn != "404.html":
                # 搜索引擎验证文件（根目录 google*.html）不是内容页，不进 sitemap
                if rel == "." and _fn.startswith("google"):
                    continue
                p = _fn if rel == "." else f"{rel}/{_fn}"
                html_files.add(p)
    # 首页以规范根路径 site_url/ 入 sitemap，等价于磁盘上的 index.html
    missing = sorted(f"{site_url}/{p}" for p in html_files
                     if f"{site_url}/{p}" not in sm_locs
                     and not (p == "index.html" and f"{site_url}/" in sm_locs)
                     and not (p == "en/index.html" and f"{site_url}/en/" in sm_locs))
    if sitemap and not missing:
        _check("sitemap", "sitemap.xml 条数与漏页", "pass",
               f"共 {len(sm_locs)} 条 URL，磁盘 {len(html_files)} 个 HTML 页全部在列")
    elif sitemap:
        _check("sitemap", "sitemap.xml 条数与漏页", "fail",
               f"共 {len(sm_locs)} 条 URL，漏 {len(missing)} 页："
               + "、".join(missing[:5]) + ("…" if len(missing) > 5 else ""))
    else:
        _check("sitemap", "sitemap.xml 条数与漏页", "fail", "sitemap.xml 不存在")

    llms = _read_text(os.path.join(root, "llms.txt"))
    mcp_url = site.get("mcp_url") or ""
    if not llms:
        _check("llms", "llms.txt 存在", "fail", "llms.txt 不存在")
    elif mcp_url and mcp_url in llms:
        _check("llms", "llms.txt 存在", "pass", "已生成，含 MCP 端点与数据 JSON 入口")
    elif mcp_url:
        _check("llms", "llms.txt 存在", "warn", "llms.txt 存在，但未写 MCP 端点")
    else:
        _check("llms", "llms.txt 存在", "pass",
               "已生成，含数据 JSON 入口（未配置 MCP 端点）")

    index_html = _read_text(os.path.join(root, "index.html"))
    if 'rel="canonical"' in index_html and 'hreflang="zh-CN"' in index_html:
        _check("canonical", "首页 canonical / hreflang", "pass",
               "canonical、hreflang=zh-CN 与 x-default 齐全")
    else:
        _check("canonical", "首页 canonical / hreflang", "fail",
               "首页缺少 canonical 或 hreflang（需下次生成后生效）")
    if '"@type": "WebSite"' in index_html and '"inLanguage"' in index_html:
        _check("jsonld", "首页 JSON-LD（WebSite）", "pass",
               "WebSite 结构化数据含 inLanguage=zh-CN")
    elif '"@type": "WebSite"' in index_html:
        _check("jsonld", "首页 JSON-LD（WebSite）", "warn",
               "WebSite 存在，但缺 inLanguage")
    else:
        _check("jsonld", "首页 JSON-LD（WebSite）", "fail", "首页缺少 WebSite 结构化数据")

    items_dir = os.path.join(root, "items")
    newest_item = ""
    if os.path.isdir(items_dir):
        _htmls = [os.path.join(items_dir, f) for f in os.listdir(items_dir)
                  if f.endswith(".html")]
        if _htmls:
            newest_item = max(_htmls, key=os.path.getmtime)
    item_html = _read_text(newest_item) if newest_item else ""
    if item_html and '"dateModified"' in item_html and '"datePublished"' in item_html \
            and 'og:type" content="article"' in item_html:
        _check("item", "详情页 Article（抽查最新 1 篇）", "pass",
               "含 datePublished / dateModified，og:type=article")
    elif item_html:
        _check("item", "详情页 Article（抽查最新 1 篇）", "fail",
               "详情页缺 dateModified 或 og:type 不是 article")
    else:
        _check("item", "详情页 Article（抽查最新 1 篇）", "warn", "未找到详情页可抽查")

    og_samples = [("index.html", index_html)]
    if item_html:
        og_samples.append(("详情页（最新 1 篇）", item_html))
    bad_og = []
    for _label, _h in og_samples:
        _lacks = []
        if "/assets/og-image.png" not in _h:
            _lacks.append("og:image/twitter:image 未指向 /assets/og-image.png")
        if 'content="summary_large_image"' not in _h:
            _lacks.append("twitter:card 不是 summary_large_image")
        if "favicon.ico" not in _h:
            _lacks.append("favicon.ico 链接缺失")
        if "apple-touch-icon" not in _h:
            _lacks.append("apple-touch-icon 链接缺失")
        if _lacks:
            bad_og.append(f"{_label} 缺 {';'.join(_lacks)}")
    if og_samples and not bad_og:
        _check("og", "OG 图与图标链接（batch 2 落地检查）", "pass",
               "首页与最新详情页 og:image / twitter:image 均指向 "
               "/assets/og-image.png，twitter:card 为 summary_large_image，"
               "含 favicon.ico 与 apple-touch-icon 链接。")
    elif og_samples:
        _check("og", "OG 图与图标链接（batch 2 落地检查）", "fail",
               "；".join(bad_og))
    else:
        _check("og", "OG 图与图标链接（batch 2 落地检查）", "warn",
               "未抽到页面可检查。")

    period_samples = ["daily.html", "weekly.html", "monthly.html",
                      "en/daily.html", "en/weekly.html", "en/monthly.html"]
    period_html = {}
    for _rel in period_samples:
        _p = os.path.join(root, _rel)
        if os.path.exists(_p):
            period_html[_rel] = _read_text(_p)
    bad_period = []
    for _rel, _h in period_html.items():
        _lacks = []
        if 'rel="canonical"' not in _h:
            _lacks.append("canonical")
        if 'hreflang="zh-CN"' not in _h:
            _lacks.append("hreflang zh-CN")
        if 'hreflang="x-default"' not in _h:
            _lacks.append("hreflang x-default")
        if 'name="robots"' not in _h:
            _lacks.append("robots meta")
        if "application/rss+xml" not in _h:
            _lacks.append("RSS 发现链接")
        if _lacks:
            bad_period.append(f"{_rel} 缺 {','.join(_lacks)}")
    if period_html and not bad_period:
        _check("period", "定期页 head（日报/周报/月报，中英）", "pass",
               f"抽查 {len(period_html)} 页（日报/周报/月报，中英）全部含 canonical、"
               "hreflang zh-CN + x-default、robots meta、RSS 发现链接。")
    elif period_html:
        _check("period", "定期页 head（日报/周报/月报，中英）", "fail",
               "；".join(bad_period))
    else:
        _check("period", "定期页 head（日报/周报/月报，中英）", "warn",
               "未抽到定期页可检查。")

    if mcp_url:
        _check("mcp", "MCP 端点可达性", "warn",
               f"端点 {mcp_url} 已写入 llms.txt；"
               "本轮未做在线请求，可达性需线上验证")
    else:
        _check("mcp", "MCP 端点可达性", "warn",
               "未配置 MCP 端点（site.mcp_url 为空），llms.txt 不含 MCP 段")
    mirror_url = (site.get("mirror_url") or "").rstrip("/")
    if mirror_url:
        _check("mirror", "镜像站部署", "warn",
               f"镜像 {mirror_url} 的部署状态在仓库内无法验证，"
               "请以托管平台控制台最新部署为准")
    else:
        _check("mirror", "镜像站部署", "warn",
               "未配置镜像（site.mirror_url 为空），跳过此项")
    feed = _read_text(os.path.join(root, "feed.xml"))
    if feed and "<rss" in feed and "<item>" in feed:
        _check("feed", "feed.xml 正常", "pass",
               f"RSS 2.0 正常，含 {feed.count('<item>')} 条")
    else:
        _check("feed", "feed.xml 正常", "fail", "feed.xml 不存在或内容异常")

    n_pass = sum(1 for c in checks if c["status"] == "pass")
    n_warn = sum(1 for c in checks if c["status"] == "warn")
    n_fail = sum(1 for c in checks if c["status"] == "fail")
    data = {"generated_at": today_iso, "site": site_url,
            "summary": {"total": len(checks), "passed": n_pass,
                        "warn": n_warn, "failed": n_fail},
            "checks": checks}
    icon = {"pass": "✅", "warn": "⚠️", "fail": "❌"}
    rows = "".join(
        f'<tr><td>{icon[c["status"]]} {esc(c["label"])}</td>'
        f'<td>{esc(c["detail"])}</td></tr>\n' for c in checks)
    body = (f'<div class="m-title">SEO / GEO 自检</div>'
            f'<h1>{esc(site["name"])} · SEO / GEO 自检</h1>'
            f'<p class="lede">最后检查：{today_iso}（每轮生成后自动刷新；'
            f'通过 {n_pass}/{len(checks)}，警告 {n_warn}，失败 {n_fail}）</p>'
            f'<table class="audit-table"><thead><tr><th>检查项</th><th>结果</th></tr></thead>'
            f'<tbody>{rows}</tbody></table>'
            f'<p class="more-note">数据文件：<a href="data/geo-audit.json">data/geo-audit.json</a>'
            f' · 站点说明：<a href="llms.txt">llms.txt</a>'
            f' · 站点地图：<a href="sitemap.xml">sitemap.xml</a></p>')
    html = (page_open(site, "more", f'{site["title"]} · SEO / GEO 自检',
                      f'{site["name"]} SEO 与 GEO 自检页：robots、sitemap、llms、canonical、'
                      "结构化数据、详情页、MCP 与订阅源的逐项检查结果。",
                      prefix="index.html",
                      canonical=site_url + "/geo-audit.html")
            + body + page_close(site, "more", prefix="index.html"))
    return html, data


# ---------------------------------------------------------------- 主流程

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--daily", action="store_true", help="同时产出当日日报")
    ap.add_argument("--root", default=ROOT)
    args = ap.parse_args()
    root = args.root
    cfg = load_json(os.path.join(root, "config.json"))
    sources = load_json(os.path.join(root, "sources.json"))["sources"]
    site = cfg["site"]
    _crawler = site.get("crawler_name", "HOTBot/1.0")
    _repo = site.get("repo", "")
    UA["User-Agent"] = f"{_crawler} (+{_repo})" if _repo else _crawler
    global LAUNCH_DATE
    _launch = site.get("launch_date", "")
    try:
        if _launch:
            LAUNCH_DATE = datetime.strptime(_launch, "%Y-%m-%d").replace(tzinfo=CST).date()
    except ValueError:
        print(f"launch_date 无效：{_launch}，改用默认 2026-01-01", file=sys.stderr)
    cats = cfg["categories"]
    cat_label = {c["key"]: c["label"] for c in cats}
    cat_label_en = {c["key"]: c.get("label_en", "") for c in cats}
    global CAT_LABEL_EN, CAT_LABEL_EN_BY_ZH
    CAT_LABEL_EN = cat_label_en
    CAT_LABEL_EN_BY_ZH = {c["label"]: c.get("label_en", c["label"]) for c in cats}

    def set_lang(lang, depth):
        """写一页前设置双语全局：lang 为 "zh"/"en"，depth 为页面相对站根的深度（0 根页，1 子目录）。"""
        global PAGE_LANG, ASSET_BASE, PAGE_BASE
        PAGE_LANG = lang
        if lang == "zh":
            ASSET_BASE = "" if depth == 0 else "../"
            PAGE_BASE = "" if depth == 0 else "../"
        else:
            ASSET_BASE = "../" if depth == 0 else "../../"
            PAGE_BASE = "" if depth == 0 else "../"
    sc = cfg["scoring"]
    now = datetime.now(timezone.utc)
    now_cst = now.astimezone(CST)

    data_dir = os.path.join(root, "data")
    os.makedirs(data_dir, exist_ok=True)

    # 历史（增量更新：新条目合并进来，旧条目按时间淘汰，不全量覆盖丢历史）
    # 本地库 data/store.json（不推送；推送清单里没有它）。老版 data/items.json
    # 只在首次迁移时读一次，之后不再读写。
    hist_path = os.path.join(data_dir, "store.json")
    history = {}
    if os.path.exists(hist_path):
        try:
            for it in load_json(hist_path).get("items", []):
                history[it["id"]] = it
        except (json.JSONDecodeError, KeyError):
            print("store.json damaged, starting fresh", file=sys.stderr)
    elif os.path.exists(os.path.join(data_dir, "items.json")):
        try:
            for it in load_json(os.path.join(data_dir, "items.json")).get("items", []):
                history[it["id"]] = it
            print("migrated history from data/items.json to data/store.json")
        except (json.JSONDecodeError, KeyError):
            print("items.json damaged, starting fresh", file=sys.stderr)

    src_by_id = {s["id"]: s for s in sources}
    required_keywords = [k.lower() for k in cfg.get("required_keywords", [])]
    reject_keywords = [k.lower() for k in cfg.get("reject_keywords", [])]
    exclude_links = {norm_link(u) for u in cfg.get("exclude_links", [])}

    def enrich_store_item(it):
        """给历史条目补上与时间无关的派生字段（B16/B2 供 JS 动态渲染用）：
        信源分级、分类、中文标签。"""
        it["tier"] = src_by_id.get(it.get("source_id", ""), {}).get("tier", "T2")
        it["category"] = classify(it, cats,
                                  src_by_id.get(it.get("source_id", ""), {}).get(
                                      "category_hint", "industry"))
        it["category_label"] = cat_label.get(it["category"], it["category"])
        it["tags"] = labels_for(it, cfg)[:3]

    for _it in history.values():  # 老条目回填（以前的 items.json 没有这些字段）
        if "tags" not in _it or "tier" not in _it or "category" not in _it:
            enrich_store_item(_it)
        # 分级跟随 sources.json 实时刷新：改了某源的 tier，历史条目下一轮立即生效，
        # 否则旧条目会一直沿用首次收录时的分级（2026-11-11 把关发现 T3 改完旧条目仍按 T2 打分）
        _it["tier"] = src_by_id.get(_it.get("source_id", ""), {}).get("tier", "T2")

    fetched, failed = 0, []
    # 中文翻译（data/zh_draft.json，按规范化链接匹配；每日精选把关时更新草稿，
    # 下一轮生成自动合入并写回 store.json，Actions 重生成也不会丢）
    zh_path = os.path.join(data_dir, "zh_draft.json")
    if os.path.exists(zh_path):
        try:
            zh = load_json(zh_path)
            applied = 0
            for it in history.values():
                tr = zh.get(norm_link(it.get("link", "")))
                if not tr:
                    continue
                if tr.get("zh_title"):
                    it["zh_title"] = tr["zh_title"]
                if tr.get("zh_oneliner"):
                    it["zh_oneliner"] = tr["zh_oneliner"]
                if tr.get("en_title"):
                    it["en_title"] = tr["en_title"]
                if tr.get("en_oneliner"):
                    it["en_oneliner"] = tr["en_oneliner"]
                applied += 1
            if applied:
                print(f"zh: {applied} items matched from zh_draft.json")
        except (json.JSONDecodeError, AttributeError) as e:
            print("zh_draft.json skipped (%s)" % e, file=sys.stderr)
    # 2026-11-25 把关：入库标题索引——同一篇文章经不同订阅源/不同 Google
    # 新闻查询会拿到不同的 CBM 链接，链接去重拦不住；30 天库实测 106 组
    # 标题完全相同的重复（同日 98 组、3 天内跨日 16 组，全是同一篇重入）。
    # 以归一化标题（去 outlet 后缀，≥10 字）+ 3 天发布窗口为准，
    # 比对原文标题与已入库条目的原文标题/中文标题；本轮新入库的也即时进索引。
    def _ingest_title_key(title):
        t = _norm_title(_strip_outlet(title or ""))
        return t if len(t) >= 10 else ""

    _cutoff_idx = now - timedelta(days=sc["history_days"])
    title_index = {}
    for _old in history.values():
        try:
            _op = datetime.fromisoformat(_old["published"])
        except ValueError:
            continue
        if _op.tzinfo is None:
            _op = _op.replace(tzinfo=timezone.utc)
        if _op < _cutoff_idx:
            continue
        for _t in {_ingest_title_key(_old.get("title")),
                   _ingest_title_key(_old.get("zh_title"))}:
            if _t:
                title_index.setdefault(_t, []).append(_old)

    for src in sources:
        try:
            body = fetch(src["url"])
            new_items = parse_feed(body, src)
        except Exception as e:  # noqa: BLE001 - 单个信源失败不中断整轮
            failed.append((src["id"], str(e)[:80]))
            continue
        if required_keywords:
            new_items = [it for it in new_items
                         if any(kw in (it["title"] + " " + (it.get("summary") or "")).lower()
                                for kw in required_keywords)]
        if reject_keywords:
            # 排除词：标题/摘要命中即整条丢弃（museum/amusement/rock band 等同名误命中）
            new_items = [it for it in new_items
                         if not any(_reject_hit(kw, it["title"] + " " + (it.get("summary") or ""))
                                    for kw in reject_keywords)]
        if exclude_links:
            new_items = [it for it in new_items if norm_link(it["link"]) not in exclude_links]
        fetched += len(new_items)
        for it in new_items:
            pub = it["published"] or now
            it["published"] = pub.astimezone(timezone.utc).isoformat()
            it["id"] = hashlib.sha1(norm_link(it["link"]).encode()).hexdigest()
            if it["id"] in history:
                continue  # 已收录：去重
            tk = _ingest_title_key(it["title"])
            if tk:
                _dup = False
                for _old in title_index.get(tk, ()):
                    try:
                        _op = datetime.fromisoformat(_old["published"])
                    except ValueError:
                        continue
                    if _op.tzinfo is None:
                        _op = _op.replace(tzinfo=timezone.utc)
                    if abs((pub - _op).total_seconds()) <= 3 * 86400:
                        _dup = True
                        break
                if _dup:
                    continue  # 同文重入：标题相同且 3 天内已收录（不同链接同一篇）
            entry = {
                "id": it["id"], "title": it["title"], "link": it["link"],
                "source": it["source"], "source_id": it["source_id"],
                "published": it["published"], "summary": it["summary"],
                "fetched_at": now.isoformat(),
            }
            if it.get("summary_full"):
                entry["summary_full"] = it["summary_full"]
            enrich_store_item(entry)
            history[it["id"]] = entry
            if tk:
                title_index.setdefault(tk, []).append(entry)
    # 淘汰超过 history_days 的旧条目
    cutoff_hist = now - timedelta(days=sc["history_days"])
    history = {k: v for k, v in history.items()
               if datetime.fromisoformat(v["published"]) >= cutoff_hist}
    save_json(hist_path, {"updated_at": now.isoformat(), "items": list(history.values())})

    # 分类与打分（在内存里算，不写回历史文件，保持历史干净）
    live = []
    for it in history.values():
        pub = datetime.fromisoformat(it["published"])
        if pub.tzinfo is None:
            pub = pub.replace(tzinfo=timezone.utc)
        item = dict(it)
        item["_pub"] = pub
        item["_tier"] = it.get("tier") or src_by_id.get(it["source_id"], {}).get("tier", "T2")
        item["category"] = it.get("category") or classify(
            item, cats, src_by_id.get(it["source_id"], {}).get("category_hint", "industry"))
        item["category_label"] = cat_label.get(item["category"], item["category"])
        item["tags"] = it.get("tags") or labels_for(item, cfg)[:3]
        item["score"] = score(item, cfg, now)
        item["reason"] = reason_for(item, cfg, now)
        item["reason_en"] = reason_for_en(item, cfg, now)
        # 当日新到：今天首次被本站收录，且本身也是 24 小时内发布的
        # （只按收录日期会把建站日批量回填的旧文也标上“新”）
        fa = it.get("fetched_at")
        is_new = False
        if fa:
            try:
                fdt = datetime.fromisoformat(fa)
                if fdt.tzinfo is None:
                    fdt = fdt.replace(tzinfo=timezone.utc)
                is_new = (fdt.astimezone(CST).date() == now_cst.date()
                          and (now - item["_pub"]) <= timedelta(hours=24))
            except ValueError:
                pass
        item["is_new"] = is_new
        live.append(item)

    # 可选 LLM 重排（无 Key 时直接跳过）
    live.sort(key=lambda x: x["score"], reverse=True)
    live = maybe_llm_rerank(live, site)

    recent_48h = [it for it in live if (now - it["_pub"]) <= timedelta(hours=sc["selected_hours"])]
    selected = [it for it in recent_48h if it["score"] >= sc["selected_min"]]
    selected.sort(key=lambda x: x["score"], reverse=True)
    selected = dedup_topics(selected)[:sc["daily_top"]]

    last_7d = [it for it in live if (now - it["_pub"]) <= timedelta(days=sc["hot_days"])]
    for it in last_7d:
        age_days = (now - it["_pub"]).total_seconds() / 86400.0
        it["hot_score"] = round(it["score"] * (sc["decay_base"] ** age_days), 1)
    hot = cap_families(dedup_topics(sorted(last_7d, key=lambda x: x["hot_score"], reverse=True)))[:sc["hot_top"]]
    timeline = sorted(last_7d, key=lambda x: x["_pub"], reverse=True)[:sc["timeline_max"]]

    # 趋势：对照上一轮已发布的榜单名次与热度（读旧 data/hot.json，写新文件之前）
    prev_ranks = {}
    prev_scores = {}
    old_hot_path = os.path.join(data_dir, "hot.json")
    if os.path.exists(old_hot_path):
        try:
            for i, h in enumerate(load_json(old_hot_path).get("hot", [])):
                prev_ranks[h["id"]] = i + 1
                prev_scores[h["id"]] = h.get("hot_score")
        except (json.JSONDecodeError, KeyError):
            pass
    for i, it in enumerate(hot):
        r = i + 1
        prev = prev_ranks.get(it["id"])
        it["prev_rank"] = prev
        it["prev_hot_score"] = prev_scores.get(it["id"])
        if prev is None:
            it["trend"] = "new"
        elif prev - r >= 2:
            it["trend"] = "up"
        elif r - prev >= 2:
            it["trend"] = "down"
        else:
            it["trend"] = "same"  # 只挪 1 名算持平，免得 4 小时一轮的抖动全画成箭头

    def pub_item(it):
        return {"id": it["id"], "title": it["title"], "link": it["link"],
                "source": it["source"], "source_id": it["source_id"],
                "published": it["published"],
                "zh_title": it.get("zh_title", ""),
                "zh_oneliner": it.get("zh_oneliner", ""),
                "en_title": it.get("en_title", ""),
                "en_oneliner": it.get("en_oneliner", ""),
                "category": it["category"], "category_label": it["category_label"],
                "tier": it.get("_tier", "T2"), "tags": it.get("tags", []),
                "score": it["score"],
                "reason": it.get("reason", ""), "reason_en": it.get("reason_en", ""),
                "is_new": bool(it.get("is_new", False)),
                "trend": it.get("trend", "same"),
                "hot_score": it.get("hot_score", it["score"]),
                "prev_rank": it.get("prev_rank"),
                "prev_hot_score": it.get("prev_hot_score")}

    gen_cst = now_cst.strftime("%Y年%m月%d日 %H:%M")
    # hot.json 只写最终发布的热点榜 Top 20（7 天候选只在内存里，不落盘）
    hot_data = {
        "generated_at": now.isoformat(),
        "generated_at_cst": gen_cst,
        "counts": {"total_7d": len(last_7d), "selected": len(selected),
                   "hot": len(hot), "timeline": len(timeline)},
        "hot": [pub_item(it) for it in hot],
    }
    save_json(os.path.join(data_dir, "hot.json"), hot_data, compact=True)

    # 客户端数据按天分块（data/days/）：首页分页与搜索按需取，不再发 30 天全量文件
    def chunk_item(it):
        return {"id": it["id"], "title": it["title"],
                "zh_title": it.get("zh_title", ""),
                "zh_oneliner": it.get("zh_oneliner", ""),
                "en_title": it.get("en_title", ""),
                "en_oneliner": it.get("en_oneliner", ""),
                "link": it["link"], "source": it["source"],
                "source_en": SOURCE_NAME_EN.get(it.get("source_id", ""), it["source"]),
                "source_id": it.get("source_id", ""),
                "reason_en": it.get("reason_en", ""),
                "published": it["published"],
                "score": it["score"], "tags": it.get("tags", []),
                "tier": it.get("_tier", "T2"), "category": it["category"],
                "category_label": it["category_label"],
                "category_label_en": cat_label_en.get(it["category"], "")}
    days_dir = os.path.join(data_dir, "days")
    os.makedirs(days_dir, exist_ok=True)
    by_day = {}
    for it in live:
        d = it["_pub"].astimezone(CST).date().isoformat()
        by_day.setdefault(d, []).append(it)
    day_index = []
    for d in sorted(by_day, reverse=True):
        items = sorted(by_day[d], key=lambda x: x["_pub"], reverse=True)
        save_json(os.path.join(days_dir, d + ".json"),
                  {"date": d, "items": [chunk_item(it) for it in items]},
                  compact=True)
        day_index.append({"date": d, "count": len(items)})
    save_json(os.path.join(days_dir, "index.json"),
              {"updated_at": now.isoformat(), "days": day_index}, compact=True)
    # 清掉已出 30 天窗口的旧分块（index.json 不再列出它们）
    for fn in os.listdir(days_dir):
        if fn.endswith(".json") and fn != "index.json" and fn[:-5] not in by_day:
            os.remove(os.path.join(days_dir, fn))
    print(f"days: {len(day_index)} day files, "
          f"{sum(x['count'] for x in day_index)} items")

    # 共享 CSS/JS 外置（assets/）：每页改引相对路径，不再内嵌整份
    assets_dir = os.path.join(root, "assets")
    os.makedirs(assets_dir, exist_ok=True)
    with open(os.path.join(assets_dir, "site.css"), "w", encoding="utf-8") as f:
        f.write(CSS)
    with open(os.path.join(assets_dir, "site.js"), "w", encoding="utf-8") as f:
        f.write(script_js(site))
    site_url = site.get("url", "")

    # 主页与热点榜（中文站；英文站的 en/ 镜像在下面）
    set_lang("zh", 0)
    with open(os.path.join(root, "index.html"), "w", encoding="utf-8") as f:
        f.write(render_index(site, cats, cfg, src_by_id, selected, hot, timeline,
                             gen_cst, hot_data["counts"]))
    # 全部动态页（对标 AIHOT /all）：30 天全量按时间倒序
    with open(os.path.join(root, "all.html"), "w", encoding="utf-8") as f:
        f.write(render_all(site, cats, cfg, src_by_id, selected, hot,
                           sorted(live, key=lambda x: x["_pub"], reverse=True),
                           gen_cst))
    with open(os.path.join(root, "hot.html"), "w", encoding="utf-8") as f:
        f.write(render_hot(site, hot, gen_cst, hot_data["counts"], cfg))

    # 静态页：收藏 / 我的 / 更新日志 / 关于 / 条款 / 隐私（每轮都重写，内容不依赖抓取）
    changelog = []
    changelog_path = os.path.join(data_dir, "changelog.json")
    if os.path.exists(changelog_path):
        try:
            changelog = load_json(changelog_path).get("entries", [])
        except (json.JSONDecodeError, AttributeError):
            changelog = []
    changelog_version = changelog[0]["version"] if changelog else ""
    with open(os.path.join(root, "starred.html"), "w", encoding="utf-8") as f:
        f.write(render_starred(site))
    with open(os.path.join(root, "more.html"), "w", encoding="utf-8") as f:
        f.write(render_more(site, changelog_version))
    with open(os.path.join(root, "changelog.html"), "w", encoding="utf-8") as f:
        f.write(render_changelog(site, changelog))
    with open(os.path.join(root, "about.html"), "w", encoding="utf-8") as f:
        f.write(render_about(site))
    with open(os.path.join(root, "terms.html"), "w", encoding="utf-8") as f:
        f.write(render_terms(site))
    with open(os.path.join(root, "privacy.html"), "w", encoding="utf-8") as f:
        f.write(render_privacy(site))
    with open(os.path.join(root, "404.html"), "w", encoding="utf-8") as f:
        f.write(render_404(site))

    # 英文站（en/ 镜像：与中文站同结构；没有 feed.xml、404、geo-audit）
    en_root = os.path.join(root, "en")
    os.makedirs(en_root, exist_ok=True)
    set_lang("en", 0)
    with open(os.path.join(en_root, "index.html"), "w", encoding="utf-8") as f:
        f.write(render_index(site, cats, cfg, src_by_id, selected, hot, timeline,
                             gen_cst, hot_data["counts"]))
    with open(os.path.join(en_root, "all.html"), "w", encoding="utf-8") as f:
        f.write(render_all(site, cats, cfg, src_by_id, selected, hot,
                           sorted(live, key=lambda x: x["_pub"], reverse=True),
                           gen_cst))
    with open(os.path.join(en_root, "hot.html"), "w", encoding="utf-8") as f:
        f.write(render_hot(site, hot, gen_cst, hot_data["counts"], cfg))
    with open(os.path.join(en_root, "starred.html"), "w", encoding="utf-8") as f:
        f.write(render_starred(site))
    with open(os.path.join(en_root, "more.html"), "w", encoding="utf-8") as f:
        f.write(render_more(site, changelog_version))
    with open(os.path.join(en_root, "changelog.html"), "w", encoding="utf-8") as f:
        f.write(render_changelog(site, changelog))
    with open(os.path.join(en_root, "about.html"), "w", encoding="utf-8") as f:
        f.write(render_about(site))
    with open(os.path.join(en_root, "terms.html"), "w", encoding="utf-8") as f:
        f.write(render_terms(site))
    with open(os.path.join(en_root, "privacy.html"), "w", encoding="utf-8") as f:
        f.write(render_privacy(site))

    # 主题页（B11）：按标签从 30 天全量里取条目，每标签一页 + 索引页
    tag_items = {}
    for it in live:
        for t in it.get("tags", []):
            tag_items.setdefault(t, []).append(it)
    tag_counts = []
    topics_dir = os.path.join(root, "topics")
    os.makedirs(topics_dir, exist_ok=True)
    en_topics_dir = os.path.join(en_root, "topics")
    os.makedirs(en_topics_dir, exist_ok=True)
    for label in sorted(tag_items, key=lambda l: -len(tag_items[l])):
        items = sorted(tag_items[label], key=lambda x: x["_pub"], reverse=True)[:50]
        slug = TAG_SLUGS.get(label, label)
        tag_counts.append((label, slug, len(tag_items[label])))
        set_lang("zh", 1)
        with open(os.path.join(topics_dir, slug + ".html"), "w", encoding="utf-8") as f:
            f.write(render_topic(site, label, slug, [pub_item(it) for it in items]))
        set_lang("en", 1)
        with open(os.path.join(en_topics_dir, slug + ".html"), "w", encoding="utf-8") as f:
            f.write(render_topic(site, label, slug, [pub_item(it) for it in items]))
    set_lang("zh", 0)
    with open(os.path.join(root, "topics.html"), "w", encoding="utf-8") as f:
        f.write(render_topics_index(site, tag_counts))
    set_lang("en", 0)
    with open(os.path.join(en_root, "topics.html"), "w", encoding="utf-8") as f:
        f.write(render_topics_index(site, tag_counts))

    # RSS / robots / sitemap / favicon（C5；每轮都写）
    feed_items = sorted(recent_48h, key=lambda x: x["score"], reverse=True)[:20]
    with open(os.path.join(root, "feed.xml"), "w", encoding="utf-8") as f:
        f.write(build_feed_xml(site, [pub_item(it) for it in feed_items]))
    # robots.txt（SEO/GEO：明确放行 AI 爬虫，禁高频低价值抓取；llms.txt 见下方）
    with open(os.path.join(root, "robots.txt"), "w", encoding="utf-8") as f:
        f.write(build_robots_txt(site))
    with open(os.path.join(root, "favicon.svg"), "w", encoding="utf-8") as f:
        f.write(LOGO_SVG)
    # sitemap.xml：真实 lastmod + 全量页面（历史 + 本轮 live + 磁盘已有详情页/存档页）
    today_iso = now_cst.strftime("%Y-%m-%d")
    sitemap_entries = {}

    def _add_sitemap(path, lastmod):
        # 空字符串是首页（规范根路径 /），必须入 sitemap，不能被真值判断丢掉
        if path != "404.html" and path not in sitemap_entries:
            sitemap_entries[path] = lastmod or today_iso

    for _p in ["", "all.html", "hot.html", "daily.html", "weekly.html", "monthly.html",
               "starred.html", "more.html", "changelog.html", "about.html",
               "terms.html", "privacy.html", "topics.html",
               "daily/archive.html", "feed.xml", "geo-audit.html"]:
        _add_sitemap(_p, today_iso)
    for _l, slug, _n in tag_counts:
        _add_sitemap("topics/" + slug + ".html", today_iso)
    # 磁盘上已有的主题页（主题最后一项过期后文件仍在）也要进 sitemap，
    # 否则 geo-audit 会因磁盘有页而 sitemap 无对应 URL 报错
    _topics_dir = os.path.join(root, "topics")
    if os.path.isdir(_topics_dir):
        for _fn in sorted(os.listdir(_topics_dir)):
            if _fn.endswith(".html"):
                _add_sitemap("topics/" + _fn, today_iso)
    _pub_dates = {}
    for _it in live:
        _pub_dates[_it["id"]] = _it["_pub"].astimezone(CST).date().isoformat()
    for _it_id, _it in history.items():
        _pub_dates.setdefault(_it_id, (_it.get("published") or "")[:10] or today_iso)
    for _it_id in list(history.keys()) + [_it["id"] for _it in live]:
        _add_sitemap("items/" + _it_id + ".html", _pub_dates.get(_it_id, today_iso))
    for _sub in ("daily", "weekly", "monthly"):
        _sub_dir = os.path.join(root, _sub)
        if os.path.isdir(_sub_dir):
            for _fn in sorted(os.listdir(_sub_dir)):
                if _fn.endswith(".html"):
                    _add_sitemap(f"{_sub}/{_fn}",
                                 _sitemap_lastmod(_sub, _fn, today_iso))
    _items_dir = os.path.join(root, "items")
    if os.path.isdir(_items_dir):
        for _fn in sorted(os.listdir(_items_dir)):
            if _fn.endswith(".html"):
                _add_sitemap("items/" + _fn, _pub_dates.get(_fn[:-5], today_iso))
    # 英文镜像：与中文条目一一对应（feed.xml 与 geo-audit.html 没有英文版；
    # 详情页镜像本轮 live 里的条目，以及磁盘上已有的过期条目英文页，
    # 否则 geo-audit 会因磁盘有页而 sitemap 无对应 URL 报错）
    live_ids = {it["id"] for it in live}
    for _p, _lm in list(sitemap_entries.items()):
        if _p in ("feed.xml", "geo-audit.html"):
            continue
        if _p.startswith("items/"):
            _iid = _p[len("items/"):-len(".html")]
            if _iid not in live_ids and not os.path.exists(
                    os.path.join(root, "en", "items", _iid + ".html")):
                continue
        _add_sitemap(("en/" + _p) if _p else "en/", _lm)
    sm = ["<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
          "<urlset xmlns=\"http://www.sitemaps.org/schemas/sitemap/0.9\" xmlns:xhtml=\"http://www.w3.org/1999/xhtml\">"]
    for _p, _lm in sitemap_entries.items():
        _loc = site_url + "/" if not _p else f"{site_url}/{_p}"
        _enc_loc = _enc_url(_loc)
        # 中英对照：有对应语言版本时加 hreflang（与页头 link alternate 一致，
        # x-default 指向英文版）；feed.xml / geo-audit.html 无英文版，不加
        if _p.startswith("en/"):
            _zh_p, _en_p = _p[len("en/"):], _p
        else:
            _zh_p = _p
            _en_p = "en/" if not _p else "en/" + _p
        _alt = ""
        if _zh_p in sitemap_entries and _en_p in sitemap_entries:
            _zh_loc = _enc_url(site_url + "/" if not _zh_p else f"{site_url}/{_zh_p}")
            _en_loc = _enc_url(f"{site_url}/{_en_p}")
            _alt = (f"<xhtml:link rel=\"alternate\" hreflang=\"zh-CN\" href=\"{_zh_loc}\"/>"
                    f"<xhtml:link rel=\"alternate\" hreflang=\"en\" href=\"{_en_loc}\"/>"
                    f"<xhtml:link rel=\"alternate\" hreflang=\"x-default\" href=\"{_en_loc}\"/>")
        sm.append(f"<url><loc>{_enc_loc}</loc>{_alt}<lastmod>{_lm}</lastmod></url>")
    sm.append("</urlset>")
    with open(os.path.join(root, "sitemap.xml"), "w", encoding="utf-8") as f:
        f.write("\n".join(sm) + "\n")
    # llms.txt：每轮重写，给 AI 客户端的站点说明 + 机器可读入口
    with open(os.path.join(root, "llms.txt"), "w", encoding="utf-8") as f:
        f.write(build_llms_txt(site, cats, today_iso))
    print(f"fetch: {fetched} items parsed from {len(sources) - len(failed)}/{len(sources)} sources"
          + (f"; failed: {failed}" if failed else ""))
    print(f"history: {len(history)} items; 7d: {len(last_7d)}; "
          f"selected: {len(selected)}; hot: {len(hot)}; timeline: {len(timeline)}; "
          f"topics: {len(tag_counts)}")

    if args.daily:
        def build_period(kind, pool, window_label):
            pool_sorted = sorted(pool, key=lambda x: x["score"], reverse=True)
            items = dedup_topics(pool_sorted)[:sc["daily_top"]]
            per_cat = {}
            for it in items:
                per_cat[it["category_label"]] = per_cat.get(it["category_label"], 0) + 1
            cat_part = "、".join(f"{k} {v} 条" for k, v in per_cat.items()) or "无"
            head = (f"头条：{items[0].get('zh_title') or items[0]['title']}"
                    if items else "暂无精选")
            date_str = now_cst.strftime("%Y年%m月%d日")
            date_iso = now_cst.strftime("%Y-%m-%d")
            if kind == "daily":
                key = date_iso
                label = date_str
            elif kind == "weekly":
                iso_y, iso_w, _ = now_cst.isocalendar()
                key = f"{iso_y}-W{iso_w:02d}"
                label = f"{iso_y}年第{iso_w}周"
            else:
                key = now_cst.strftime("%Y-%m")
                label = now_cst.strftime("%Y年%m月")
            window_en = {"daily": "In the past 24 hours", "weekly": "In the past 7 days",
                         "monthly": "In the past 30 days"}[kind]
            cat_part_en = ", ".join(f"{CAT_LABEL_EN_BY_ZH.get(k, k)} {v}" for k, v in per_cat.items()) or "none"
            _h = (items[0].get("en_title") or items[0]["title"]) if items else ""
            head_en = ("Headline: " + _h + ("" if _h.endswith(("?", "!", ".")) else ".")
                       if items else "No featured items.")
            return {
                "kind": kind, "key": key, "label": label,
                "date": date_str, "date_iso": date_iso,
                "issue": issue_no(kind, date_iso),
                "generated_at": now.isoformat(),
                "summary": (f"{window_label}共收录 {len(pool)} 条动态，精选 "
                            f"{len(items)} 条（{cat_part}）。{head}。"),
                "summary_en": (f"{window_en}, {len(pool)} items collected, {len(items)} featured "
                               f"({cat_part_en}). {head_en}"),
                "items": [pub_item(it) for it in items],
            }

        def render_archived(kind, reports, out_dir, lang_root=None):
            """渲染某类全部存档页（带上一期/下一期）；out_dir 为 daily/weekly/monthly。"""
            base_root = lang_root or root
            os.makedirs(os.path.join(base_root, out_dir), exist_ok=True)
            for i, rep in enumerate(reports):
                prev = None
                nxt = None
                if i + 1 < len(reports):
                    prev = (reports[i + 1]["label"], reports[i + 1]["key"] + ".html")
                if i > 0:
                    nxt = (reports[i - 1]["label"], reports[i - 1]["key"] + ".html")
                with open(os.path.join(base_root, out_dir, rep["key"] + ".html"),
                          "w", encoding="utf-8") as f:
                    f.write(render_period(site, kind, rep, base="../", prev=prev,
                                          next_=nxt,
                                          canonical=f"{site_url}/{out_dir}/{rep['key']}.html",
                                          rel_path=f"{out_dir}/{rep['key']}.html"))

        def current_page(kind, cur, reports, out_dir, lang_root=None):
            """当前页（daily.html/weekly.html/monthly.html，站根）：上一期指向上一个存档。"""
            base_root = lang_root or root
            prev = None
            older = [r for r in reports if r["key"] != cur["key"]]
            if older:
                prev = (older[0]["label"], f"{out_dir}/{older[0]['key']}.html")
            with open(os.path.join(base_root, kind + ".html"), "w", encoding="utf-8") as f:
                f.write(render_period(site, kind, cur, base="", prev=prev, next_=None,
                                      canonical=f"{site_url}/{kind}.html",
                                      rel_path=kind + ".html"))

        # --- 日报（每天一份存档）
        last_24h = [it for it in live if (now - it["_pub"]) <= timedelta(hours=sc["daily_hours"])]
        daily = build_period("daily", last_24h, "过去 24 小时")
        save_json(os.path.join(data_dir, "daily.json"), daily)
        daily_data_dir = os.path.join(data_dir, "daily")
        os.makedirs(daily_data_dir, exist_ok=True)
        save_json(os.path.join(daily_data_dir, daily["key"] + ".json"), daily)
        daily_reports = load_period_archive(daily_data_dir)
        enrich_report_items(daily_reports, history)
        set_lang("zh", 1)
        render_archived("daily", daily_reports, "daily")
        set_lang("en", 1)
        render_archived("daily", daily_reports, "daily", en_root)
        set_lang("zh", 0)
        current_page("daily", daily, daily_reports, "daily")
        set_lang("en", 0)
        current_page("daily", daily, daily_reports, "daily", en_root)
        print(f"daily: {daily['date']}, {len(daily['items'])} items, 第 {daily['issue']} 期")

        # --- 周报（滚动 7 天精选；每周只存一份快照）
        last_7d_sorted = sorted(last_7d, key=lambda x: x["score"], reverse=True)
        weekly = build_period("weekly", last_7d_sorted, "过去 7 天")
        save_json(os.path.join(data_dir, "weekly.json"), weekly)
        weekly_data_dir = os.path.join(data_dir, "weekly")
        os.makedirs(weekly_data_dir, exist_ok=True)
        if not os.path.exists(os.path.join(weekly_data_dir, weekly["key"] + ".json")):
            save_json(os.path.join(weekly_data_dir, weekly["key"] + ".json"), weekly)
        weekly_reports = load_period_archive(weekly_data_dir)
        enrich_report_items(weekly_reports, history)
        set_lang("zh", 1)
        render_archived("weekly", weekly_reports, "weekly")
        set_lang("en", 1)
        render_archived("weekly", weekly_reports, "weekly", en_root)
        set_lang("zh", 0)
        current_page("weekly", weekly, weekly_reports, "weekly")
        set_lang("en", 0)
        current_page("weekly", weekly, weekly_reports, "weekly", en_root)
        print(f"weekly: {weekly['label']}, {len(weekly['items'])} items, 第 {weekly['issue']} 期")

        # --- 月报（滚动 30 天精选；每月只存一份快照）
        last_30d = [it for it in live if (now - it["_pub"]) <= timedelta(days=30)]
        monthly = build_period("monthly", last_30d, "过去 30 天")
        save_json(os.path.join(data_dir, "monthly.json"), monthly)
        monthly_data_dir = os.path.join(data_dir, "monthly")
        os.makedirs(monthly_data_dir, exist_ok=True)
        if not os.path.exists(os.path.join(monthly_data_dir, monthly["key"] + ".json")):
            save_json(os.path.join(monthly_data_dir, monthly["key"] + ".json"), monthly)
        monthly_reports = load_period_archive(monthly_data_dir)
        enrich_report_items(monthly_reports, history)
        set_lang("zh", 1)
        render_archived("monthly", monthly_reports, "monthly")
        set_lang("en", 1)
        render_archived("monthly", monthly_reports, "monthly", en_root)
        set_lang("zh", 0)
        current_page("monthly", monthly, monthly_reports, "monthly")
        set_lang("en", 0)
        current_page("monthly", monthly, monthly_reports, "monthly", en_root)
        print(f"monthly: {monthly['label']}, {len(monthly['items'])} items, 第 {monthly['issue']} 期")

        # --- 往期存档页（B8/B9）：日报按月分组；周报、月报各列一组
        def arch_entry(rep, file_href, date_short):
            return {"date_iso": rep["date_iso"], "date_short": date_short,
                    "file": file_href, "issue": rep["issue"],
                    "count": len(rep["items"])}
        d_entries = [arch_entry(r, r["key"] + ".html",
                                datetime.strptime(r["date_iso"], "%Y-%m-%d").strftime("%m月%d日"))
                     for r in daily_reports]
        w_entries = [arch_entry(r, "../weekly/" + r["key"] + ".html", r["label"])
                     for r in weekly_reports]
        m_entries = [arch_entry(r, "../monthly/" + r["key"] + ".html", r["label"])
                     for r in monthly_reports]
        os.makedirs(os.path.join(root, "daily"), exist_ok=True)
        set_lang("zh", 1)
        with open(os.path.join(root, "daily", "archive.html"), "w", encoding="utf-8") as f:
            f.write(render_archive(site, d_entries, w_entries, m_entries))
        os.makedirs(os.path.join(en_root, "daily"), exist_ok=True)
        set_lang("en", 1)
        with open(os.path.join(en_root, "daily", "archive.html"), "w", encoding="utf-8") as f:
            f.write(render_archive(site, d_entries, w_entries, m_entries))
        # sitemap 补上本轮新出的存档页（主 sitemap 已扫描磁盘，只补还没有的；
        # lastmod 用报告真实日期，不再全写当天）
        try:
            with open(os.path.join(root, "sitemap.xml"), encoding="utf-8") as _sf:
                _existing_locs = set(re.findall(r"<loc>([^<]+)</loc>", _sf.read()))
        except OSError:
            _existing_locs = set()
        _sm_extra = []
        for _out, _reps in (("daily", daily_reports), ("weekly", weekly_reports),
                            ("monthly", monthly_reports)):
            for _r in _reps:
                _loc = f"{site_url}/{_out}/{_r['key']}.html"
                _loc_en = f"{site_url}/en/{_out}/{_r['key']}.html"
                # 日报/周报/月报中英版成对出现，补的条目也带 hreflang
                _alt = (f"<xhtml:link rel=\"alternate\" hreflang=\"zh-CN\" href=\"{_loc}\"/>"
                        f"<xhtml:link rel=\"alternate\" hreflang=\"en\" href=\"{_loc_en}\"/>"
                        f"<xhtml:link rel=\"alternate\" hreflang=\"x-default\" href=\"{_loc_en}\"/>")
                if _loc not in _existing_locs:
                    _sm_extra.append(f"<url><loc>{_loc}</loc>{_alt}"
                                     f"<lastmod>{_r['date_iso']}</lastmod></url>")
                if _loc_en not in _existing_locs:
                    _sm_extra.append(f"<url><loc>{_loc_en}</loc>{_alt}"
                                     f"<lastmod>{_r['date_iso']}</lastmod></url>")
        if _sm_extra:
            with open(os.path.join(root, "sitemap.xml"), encoding="utf-8") as _sf:
                _sm_text = _sf.read()
            _sm_text = _sm_text.replace("</urlset>",
                                        "\n".join(_sm_extra) + "\n</urlset>")
            with open(os.path.join(root, "sitemap.xml"), "w", encoding="utf-8") as f:
                f.write(_sm_text)
        print(f"archive: daily {len(d_entries)}, weekly {len(w_entries)}, monthly {len(m_entries)}")

    # --- 文章详情页（items/<id>.html）：30 天库里的每条内容各一页；
    # 旧条目过期后页面留着当永久链接，不删除。
    daily_issue = {}
    for rep in load_period_archive(os.path.join(data_dir, "daily")):
        for it in rep.get("items", []):
            if it["id"] not in daily_issue:
                daily_issue[it["id"]] = {"issue": rep["issue"],
                                         "date": rep["date"],
                                         "key": rep["key"]}
    sel_ids = {it["id"] for it in selected}
    items_dir = os.path.join(root, "items")
    os.makedirs(items_dir, exist_ok=True)
    en_items_dir = os.path.join(en_root, "items")
    os.makedirs(en_items_dir, exist_ok=True)
    by_cat = {}
    by_src = {}
    for it in live:
        by_cat.setdefault(it["category"], []).append(it)
        by_src.setdefault(it["source_id"], []).append(it)
    for lst in list(by_cat.values()) + list(by_src.values()):
        lst.sort(key=lambda x: x["score"], reverse=True)
    n_items = 0
    for it in live:
        picked = []
        for cand in by_cat.get(it["category"], []):
            if cand["id"] != it["id"] and cand not in picked:
                picked.append(cand)
            if len(picked) >= 5:
                break
        if len(picked) < 5:
            for cand in by_src.get(it["source_id"], []):
                if cand["id"] != it["id"] and cand not in picked:
                    picked.append(cand)
                if len(picked) >= 5:
                    break
        # 详情页只用 pub_item 的发布字段（标题 + 一句话简介），不并完整摘要。
        detail = dict(pub_item(it))
        set_lang("zh", 1)
        with open(os.path.join(items_dir, it["id"] + ".html"), "w", encoding="utf-8") as f:
            f.write(render_item(site, detail, [pub_item(r) for r in picked],
                                it["id"] in sel_ids,
                                daily_issue.get(it["id"])))
        set_lang("en", 1)
        with open(os.path.join(en_items_dir, it["id"] + ".html"), "w", encoding="utf-8") as f:
            f.write(render_item(site, detail, [pub_item(r) for r in picked],
                                it["id"] in sel_ids,
                                daily_issue.get(it["id"])))
        n_items += 1
    print(f"items: {n_items} detail pages (+{n_items} en)")
    # --- /geo-audit 自检页 + 数据（SEO/GEO：每轮生成后自检，日报复用同一份数据；只中文版）---
    set_lang("zh", 0)
    geo_html, geo_data = build_geo_audit(site, root, site_url, today_iso)
    with open(os.path.join(root, "geo-audit.html"), "w", encoding="utf-8") as f:
        f.write(geo_html)
    save_json(os.path.join(data_dir, "geo-audit.json"), geo_data)
    print(f"geo-audit: {geo_data['summary']['passed']} passed, "
          f"{geo_data['summary']['warn']} warn, {geo_data['summary']['failed']} failed")


if __name__ == "__main__":
    main()
