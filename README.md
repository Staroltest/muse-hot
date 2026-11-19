# MuseHOT Muse 热点

**在线访问：[https://muse-hot.pages.dev](https://muse-hot.pages.dev)**（主站）· [GitHub Pages 镜像](https://staroltest.github.io/muse-hot) · [RSS](https://muse-hot.pages.dev/feed.xml) · [MCP](https://muse-hot.pages.dev/mcp)

全球各地的人们在拿 Muse 做什么，这个站每天盯着看：官方发布、模型更新、真实用法、教程指南、评测与争议，每天精选 10 条，06:00 出一期日报。

## 一句话

用 hot-site-template 搭的 Muse 热点站，面向 Muse 用户与 AI 智能体关注者，信源逐个实测后定。

## English

MuseHOT tracks what people around the world are doing with Meta's Muse AI assistant: official releases, model updates, real-world usage, tutorials, reviews and controversies. 42 sources, top 10 picks daily, a daily issue at 06:00 Beijing time, in Chinese and English.

## 模板里有什么

| 文件 | 作用 |
| --- | --- |
| `tools/generate.py` | 生成器：拉 RSS → 去重 → 规则打分 → 生成全站。纯 Python 标准库，零依赖。另加了一项 config 可配的 `required_keywords` 主题过滤：只收标题或摘要里出现 Muse 的条目 |
| `tools/geo_audit.py` | GEO 自检：独立运行，只读生成物，输出 `geo-audit.html` + `data/geo-audit.json` |
| `config.json` | 全部可调项：站名、受众、分类与关键词、打分权重、关于页、页脚、赞赏码 |
| `sources.json` | 信源清单（42 条，2026-11-17 第四轮扩至 42 条，2026-11-19 复核） |
| `_worker.js` | MCP 端点（Cloudflare Pages Advanced Mode，单文件无依赖） |
| `_routes.json` | 只把 `/mcp` 交给 worker，其余路径静态托管 |
| `favicon.svg` | 通用站标 |
| `data/changelog.json` | 更新日志 |
| `docs/cron-half-hourly-update.md` | 每半小时更新任务的指令模板 |
| `docs/cron-daily-curation.md` | 每日精选把关任务的指令模板 |
| `docs/pipeline-notes.md` | 流水线踩过的坑与铁律 |
| `BOOTSTRAP.md` | agent 开新站的完整 playbook |

## 站点长什么样

首页（精选 10 条 + 热点榜）、全部动态（30 天全量按天分组）、热点榜、
日报 / 周报 / 月报、主题页、收藏、RSS（`feed.xml`）、MCP（`/mcp`）。
只展示原标题 + 一句自己写的一句话简介 + 原文链接，不转载正文与摘要。

## 成本

免费额度内：GitHub Pages 免费；Cloudflare 直传不消耗每月 500 次构建额度，
静态访问不限量；MCP 调用每天 10 万次免费额度。详见 BOOTSTRAP.md。

## 许可与出处

MIT License，Copyright (c) 2026 Camille。

流水线源自 IndieHOT 的实践；IndieHOT 的信息架构与界面风格参考了卡兹克
（张仁杰）的开源项目 [AIHOT](https://github.com/KKKKhazix/AIHOT)（MIT 协议）。
本站模板按 MIT 协议开源，欢迎取用，署名链请保留。
