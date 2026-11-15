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
import hashlib
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


def git_blob_sha(raw):
    """SHA-1 Git assigns to a blob with these exact bytes (no API call)."""
    return hashlib.sha1(b"blob %d\0" % len(raw) + raw).hexdigest()


def existing_tree(repo, branch):
    """Path -> blob SHA of the branch tip, or {} if it cannot be read.

    One recursive-tree GET. Any failure (or a truncated tree) returns {}
    so the caller falls back to uploading every blob, exactly as before.
    """
    try:
        ref = call(f"/repos/{repo}/git/ref/heads/{branch}")
        if not ref:
            return {}
        commit = call(f"/repos/{repo}/git/commits/{ref['object']['sha']}")
        tree = call(f"/repos/{repo}/git/trees/{commit['tree']['sha']}?recursive=1")
        if not tree or tree.get("truncated"):
            return {}
        return {e["path"]: e["sha"] for e in tree.get("tree", [])
                if e.get("type") == "blob"}
    except Exception as e:
        print(f"existing tree lookup failed, uploading all blobs: {e}")
        return {}


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
    # Reuse the blob SHA for any file whose bytes are already on the
    # branch tip: identical content has an identical blob SHA, so no
    # upload is needed. Previously every file was re-uploaded as a new
    # blob on every push (~350 POSTs per run, twice an hour), which is
    # what kept tripping the GitHub API rate limit late in the hour.
    # The tree below still lists every file, so nothing is dropped.
    existing = existing_tree(args.repo, args.branch)
    blobs = []
    new_blobs = 0
    for rel, full in files:
        with open(full, "rb") as f:
            raw = f.read()
        digest = git_blob_sha(raw)
        if rel in existing and existing[rel] == digest:
            blobs.append({"path": rel, "mode": "100644", "type": "blob", "sha": digest})
            continue
        content = base64.b64encode(raw).decode("ascii")
        blob = call(f"/repos/{args.repo}/git/blobs", method="POST",
                    payload={"content": content, "encoding": "base64"})
        blobs.append({"path": rel, "mode": "100644", "type": "blob", "sha": blob["sha"]})
        new_blobs += 1
    print(f"blobs: {len(blobs)} (reused {len(blobs) - new_blobs}, new {new_blobs})")

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
