#!/usr/bin/env python3
"""send_openai_dispatch.py — Outreach runner for the OpenAI Navier-Stokes formalization team dispatch.

Features:
  1. Validates all draft artifacts (academic letter, X thread, GitHub discussion, Zulip post).
  2. Generates 1-click prefilled GitHub Discussion URLs for browser submission.
  3. Integrates with outreach_approval.py ledger for strict human-in-the-loop tracking.
  4. Checks git push status to ensure all 71+ latest formalization commits are on remote.
  5. Formats X broadcast command with safety checks.

Usage:
  python3 tools/community-outreach/send_openai_dispatch.py --preview
  python3 tools/community-outreach/send_openai_dispatch.py --generate-links
  python3 tools/community-outreach/send_openai_dispatch.py --record-approval --action post_issue
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import urllib.parse
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "tools/community-outreach"))

try:
    from outreach_approval import record_approval, list_approvals
except ImportError:
    record_approval = None
    list_approvals = None

DRAFTS_DIR = REPO_ROOT / "tools/community-outreach/drafts"
DISPATCH_MD = DRAFTS_DIR / "openai_navier_stokes_dispatch.md"
TWEET_TXT = DRAFTS_DIR / "openai_navier_stokes_tweet.txt"
GITHUB_ISSUE_MD = DRAFTS_DIR / "openai_navier_stokes_github_issue.md"
ZULIP_MD = DRAFTS_DIR / "openai_navier_stokes_zulip.md"

TARGET_ID = "OPENAI-NS"
TARGET_REPO = "openai/NavierStokesAndEuler"
TARGET_DISCUSSIONS_URL = f"https://github.com/{TARGET_REPO}/discussions/new"


def check_git_status() -> dict:
    """Check commits ahead of origin/main."""
    res = subprocess.run(
        ["git", "rev-list", "--count", "origin/main..HEAD"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    ahead = int(res.stdout.strip() or "0") if res.returncode == 0 else -1
    return {"ahead_of_origin": ahead}


def validate_drafts() -> bool:
    """Validate existence and constraints of all outreach drafts."""
    all_ok = True
    print("=== Validating Outreach Drafts ===")

    for path, name in [
        (DISPATCH_MD, "Full Academic & Rogue Dispatch"),
        (TWEET_TXT, "X / Twitter Thread"),
        (GITHUB_ISSUE_MD, "GitHub Issue/Discussion Draft"),
        (ZULIP_MD, "Lean Zulip Draft"),
    ]:
        if not path.exists():
            print(f"[FAIL] Missing {name}: {path}")
            all_ok = False
        else:
            size = path.stat().st_size
            print(f"[OK] {name} exists ({size:,} bytes): {path.relative_to(REPO_ROOT)}")

    # Validate tweets length
    if TWEET_TXT.exists():
        from x_broadcast import _parse_draft_file

        tweets = _parse_draft_file(TWEET_TXT)
        print(f"\nValidating {len(tweets)} tweets in X thread:")
        for idx, t in enumerate(tweets, 1):
            length = len(t)
            status = "OK" if length <= 280 else "EXCEEDS LIMIT"
            print(f"  Tweet {idx}: {length}/280 chars [{status}]")
            if length > 280:
                all_ok = False

    return all_ok


def generate_browser_links() -> dict:
    """Generate 1-click pre-filled browser submission links."""
    if not GITHUB_ISSUE_MD.exists():
        return {}

    content = GITHUB_ISSUE_MD.read_text(encoding="utf-8")
    title = (
        "Beyond the Fluid Horizon: Arnold Geodesics, Cuntz Colimits, "
        "and an Open Quantum Geometry Benchmark for the Swarm"
    )

    # Cut preamble if present
    body = content
    if "---" in body:
        parts = body.split("---", 1)
        body = parts[1].strip()

    params = {
        "title": title,
        "body": body,
        "category": "General",
    }
    encoded_url = f"{TARGET_DISCUSSIONS_URL}?{urllib.parse.urlencode(params)}"
    return {
        "title": title,
        "browser_discussion_url": encoded_url,
        "raw_body": body,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="OpenAI Navier-Stokes Swarm Outreach Runner")
    parser.add_argument("--preview", action="store_true", help="Preview all draft texts")
    parser.add_argument("--validate", action="store_true", help="Validate draft constraints")
    parser.add_argument("--generate-links", action="store_true", help="Generate 1-click submission links")
    parser.add_argument(
        "--record-approval",
        action="store_true",
        help="Record human approval into approval_ledger.jsonl",
    )
    parser.add_argument(
        "--action",
        default="post_issue",
        choices=["post_issue", "post_x", "post_forum"],
        help="Outreach action to record approval for",
    )
    parser.add_argument("--note", default="Approved dispatch for OpenAI team", help="Approval note")

    args = parser.parse_args()

    if not any([args.preview, args.validate, args.generate_links, args.record_approval]):
        # Default: run validate + generate-links
        args.validate = True
        args.generate_links = True

    if args.validate:
        ok = validate_drafts()
        git_info = check_git_status()
        print(f"\nGit Status: {git_info['ahead_of_origin']} commits ahead of origin/main.")
        if git_info["ahead_of_origin"] > 0:
            print("  [!] Run `git push origin main` so remote contains latest theorems before sending.")
        if not ok:
            return 1

    if args.preview:
        print("\n" + "=" * 80)
        print("PREVIEW: Full Dispatch Markdown")
        print("=" * 80)
        print(DISPATCH_MD.read_text(encoding="utf-8"))

    if args.generate_links:
        links = generate_browser_links()
        print("\n" + "=" * 80)
        print("TRANSMISSION VECTOR 1: GitHub Discussions (1-Click Browser Submission)")
        print("=" * 80)
        print(f"Target: {TARGET_REPO} Discussions")
        print(f"Title: {links.get('title')}")
        print("\nClickable Pre-Filled Submission URL:")
        print(links.get("browser_discussion_url"))
        print("\n" + "=" * 80)
        print("TRANSMISSION VECTOR 2: X (Twitter) Broadcast via x_broadcast.py")
        print("=" * 80)
        print(f"Draft file: {TWEET_TXT.relative_to(REPO_ROOT)}")
        print("Posting command (once approved):")
        print(f"  python3 tools/community-outreach/x_broadcast.py post {TARGET_ID} --confirm-post --approval-id <ID>")
        print("\n" + "=" * 80)
        print("TRANSMISSION VECTOR 3: Lean Zulip Post")
        print("=" * 80)
        print(f"File: {ZULIP_MD.relative_to(REPO_ROOT)}")
        print("Target Streams: #general or #machine learning for theorem proving")

    if args.record_approval:
        if record_approval is None:
            print("Error: outreach_approval module not available", file=sys.stderr)
            return 1
        payload = record_approval(
            target_id=TARGET_ID,
            action=args.action,
            artifact=str(GITHUB_ISSUE_MD.relative_to(REPO_ROOT)),
            note=args.note,
        )
        print(f"\n[SUCCESS] Recorded approval in ledger:")
        print(json.dumps(payload, indent=2))
        print(f"\nApproval ID: {payload['approval_id']}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
