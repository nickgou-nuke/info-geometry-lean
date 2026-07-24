#!/usr/bin/env python3
"""
Faithful Automath Omega source sync from GitHub.

This script does not generate theorems. It keeps the local mirror of
the-omega-institute/automath synchronized to a specific manifest state:
- clone if missing
- fetch + hard-reset to the chosen ref otherwise
- emit a compact manifest/changed-files report for downstream loader use
"""

import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
TARGET_DIR = REPO_ROOT / "external_refs" / "automath"
UPSTREAM_URL = "https://github.com/the-omega-institute/automath.git"
DEFAULT_REF = "dev"

MANIFEST_PATH = REPO_ROOT / "docs" / "automath_github_manifest.json"


def run(cmd, *, cwd=REPO_ROOT, **kwargs):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, **kwargs)


def ensure_git():
    r = run(["git", "--version"])
    if r.returncode != 0:
        raise SystemExit("git is required on PATH")


def clone_once():
    TARGET_DIR.mkdir(parents=True, exist_ok=True)
    r = run(["git", "clone", "--no-checkout", UPSTREAM_URL, str(TARGET_DIR)])
    if r.returncode != 0:
        raise SystemExit(f"git clone failed: {r.stderr.strip()}")
    r = run(["git", "fetch", "origin", DEFAULT_REF], cwd=TARGET_DIR)
    if r.returncode != 0:
        raise SystemExit(f"git fetch failed: {r.stderr.strip()}")


def hard_reset(ref):
    r = run(["git", "reset", "--hard", ref], cwd=TARGET_DIR)
    if r.returncode != 0:
        raise SystemExit(f"git reset --hard {ref} failed: {r.stderr.strip()}")


def current_ref():
    r = run(["git", "rev-parse", "HEAD"], cwd=TARGET_DIR)
    if r.returncode != 0:
        raise SystemExit("cannot read HEAD in automath mirror")
    return r.stdout.strip()


def current_branch_or_tag():
    r = run(["git", "describe", "--tags", "--exact-match", "HEAD"], cwd=TARGET_DIR)
    if r.returncode == 0:
        return r.stdout.strip()
    r = run(["git", "symbolic-ref", "--short", "HEAD"], cwd=TARGET_DIR)
    if r.returncode == 0:
        return r.stdout.strip()
    return "DETACHED"


def list_changes(old_rev, new_rev):
    if not old_rev:
        return {"added": [], "removed": [], "changed": []}
    r = run(["git", "diff", "--name-status", old_rev, new_rev], cwd=TARGET_DIR)
    if r.returncode != 0:
        return {"added": [], "removed": [], "changed": [], "error": r.stderr.strip()}
    added, removed, changed = [], [], []
    for line in r.stdout.strip().splitlines():
        parts = line.split("\t")
        if len(parts) != 2:
            continue
        status, path = parts[0], parts[1]
        if status == "A":
            added.append(path)
        elif status == "D":
            removed.append(path)
        elif status == "M":
            changed.append(path)
        else:
            changed.append(path)
    return {"added": sorted(added), "removed": sorted(removed), "changed": sorted(changed)}


def head_exists():
    return (TARGET_DIR / ".git").exists() and TARGET_DIR.exists()


def main():
    ensure_git()
    old_rev = None
    if MANIFEST_PATH.exists():
        try:
            m = json.loads(MANIFEST_PATH.read_text())
            old_rev = m.get("commit")
        except Exception:
            old_rev = None

    if not head_exists():
        clone_once()

    r = run(["git", "fetch", "origin", DEFAULT_REF], cwd=TARGET_DIR)
    if r.returncode != 0:
        raise SystemExit(f"git fetch failed: {r.stderr.strip()}")

    # Best-effort local ref before reset
    new_rev = None
    if head_exists():
        rr = run(["git", "rev-parse", "origin/" + DEFAULT_REF], cwd=TARGET_DIR)
        if rr.returncode == 0:
            new_rev = rr.stdout.strip()

    # Capture manifest before changing tree
    pre_manifest = {
        "commit": current_ref() if head_exists() else None,
        "branch": current_branch_or_tag() if head_exists() else None,
        "target_dir": str(TARGET_DIR.relative_to(REPO_ROOT)),
        "upstream_url": UPSTREAM_URL,
    }

    hard_reset("origin/" + DEFAULT_REF)
    new_manifest = {
        "commit": current_ref(),
        "branch": current_branch_or_tag(),
        "target_dir": str(TARGET_DIR.relative_to(REPO_ROOT)),
        "upstream_url": UPSTREAM_URL,
        "synced_at_utc": datetime.now(timezone.utc).isoformat(),
    }

    changes = list_changes(old_rev, new_manifest["commit"])

    record = {
        "pre_manifest": pre_manifest,
        "post_manifest": new_manifest,
        "changes": changes,
        "summary": {
            "added": len(changes.get("added", [])),
            "removed": len(changes.get("removed", [])),
            "changed": len(changes.get("changed", [])),
        },
    }

    MANIFEST_PATH.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
