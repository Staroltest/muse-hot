#!/usr/bin/env python3
"""Push a HOT site directory to GitHub with the Git Data API.

Uses the registered custom.github credential through the dynamic
credential surrogate, so no token ever appears in arguments, files
or logs. One commit for the whole tree, no per-file commits.

Usage:
    python3 tools/push_site.py --repo Staroltest/muse-hot --message "MuseHOT YYYY-MM-DD HH:MM 更新"
"""
import argparse
import base64
import json
import os
import sys
import time
import urllib.error
import urllib.request

sys.path.insert(0, "/opt/muse/skills/custom-connector-setup/bin")
from dynamic_credentials import add_surrogate_to_request, read_json_response

BASE = "https://api.github.com"
ALLOWED = ["api.github.com"]
CRED = "custom.github"
EXCLUDE_DIRS = {".git", "__pycache__", ".github"}
EXCLUDE_FILES = {"data/store.json"}


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args):
        raise RuntimeError("redirect refused, verify the endpoint")


def call(path, method="GET", payload=None, attempts=3):
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    last = None
    for i in range(attempts):
        request = urllib.request.Request(BASE + path, data=data, method=method)
        add_surrogate_to_request(request, CRED, allowed_hosts=ALLOWED)
        request.add_header("Accept", "application/vnd.github+json")
        request.add_header("X-GitHub-Api-Version", "2022-11-28")
        if data is not None:
            request.add_header("Content-Type", "application/json")
        try:
            with urllib.request.build_opener(NoRedirect()).open(request, timeout=60) as r:
                return read_json_response(r)
        except urllib.error.HTTPError as e:
            body = e.read().decode("utf-8", "replace")
            if e.code == 404 and method == "GET":
                return None
            raise RuntimeError(f"{method} {path} -> HTTP {e.code}: {body[:300]}")
        except (urllib.error.URLError, TimeoutError, OSError) as e:
            last = e
            if i < attempts - 1:
                time.sleep(5)
    raise RuntimeError(f"{method} {path} failed after {attempts} attempts: {last}")


def collect(root):
    files = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in EXCLUDE_DIRS]
        for name in sorted(filenames):
            if name.endswith(".pyc"):
                continue
            full = os.path.join(dirpath, name)
            rel = os.path.relpath(full, root).replace(os.sep, "/")
            if rel in EXCLUDE_FILES:
                continue
            files.append((rel, full))
    return files


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--message", required=True)
    ap.add_argument("--branch", default="main")
    args = ap.parse_args()

    files = collect(args.root)
    print(f"files: {len(files)}")
    blobs = []
    for rel, full in files:
        with open(full, "rb") as f:
            content = base64.b64encode(f.read()).decode("ascii")
        blob = call(f"/repos/{args.repo}/git/blobs", method="POST",
                    payload={"content": content, "encoding": "base64"})
        blobs.append({"path": rel, "mode": "100644", "type": "blob", "sha": blob["sha"]})
    print(f"blobs: {len(blobs)}")

    ref = call(f"/repos/{args.repo}/git/ref/heads/{args.branch}")
    parents = [ref["object"]["sha"]] if ref else []
    base_tree = ref["object"]["sha"] if ref else None
    tree_payload = {"tree": blobs}
    if base_tree:
        # base_tree must be a tree sha, not a commit sha; fetch the commit first
        commit = call(f"/repos/{args.repo}/git/commits/{base_tree}")
        tree_payload["base_tree"] = commit["tree"]["sha"]
    tree = call(f"/repos/{args.repo}/git/trees", method="POST", payload=tree_payload)
    commit = call(f"/repos/{args.repo}/git/commits", method="POST",
                  payload={"message": args.message, "tree": tree["sha"], "parents": parents})
    if ref:
        call(f"/repos/{args.repo}/git/refs/heads/{args.branch}", method="PATCH",
             payload={"sha": commit["sha"], "force": False})
    else:
        call(f"/repos/{args.repo}/git/refs", method="POST",
             payload={"ref": f"refs/heads/{args.branch}", "sha": commit["sha"]})
    print(json.dumps({"commit": commit["sha"], "files": len(files), "repo": args.repo}))


if __name__ == "__main__":
    main()
