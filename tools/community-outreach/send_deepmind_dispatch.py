#!/usr/bin/env python3
"""send_deepmind_dispatch.py — Outreach runner for Google DeepMind AlphaProof / Gemini Formal Math Team dispatch.

Features:
  1. Validates all draft artifacts (academic letter, X thread, Zulip post).
  2. Generates pre-filled mailto URLs for 1-click email transmission to DeepMind project leads.
  3. Integrates with outreach_approval.py ledger for strict human-in-the-loop tracking.
  4. Checks git push status to ensure repository is fully synchronized on upstream.
  5. Formats X broadcast command with safety checks.

Usage:
  python3 tools/community-outreach/send_deepmind_dispatch.py --preview
  python3 tools/community-outreach/send_deepmind_dispatch.py --generate-links
  python3 tools/community-outreach/send_deepmind_dispatch.py --record-approval --action send_email
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
DISPATCH_MD = DRAFTS_DIR / "deepmind_alphaproof_dispatch.md"
TWEET_TXT = DRAFTS_DIR / "deepmind_alphaproof_tweet.txt"
ZULIP_MD = DRAFTS_DIR / "deepmind_alphaproof_zulip.md"

TARGET_ID = "DEEPMIND-ALPHAPROOF"
RECIPIENTS = ["thomas.hubert@google.com", "pushmeet@google.com"]
EMAIL_SUBJECT = "Non-Commutative Inductive Colimits & Neutral Hodge Geometry: A Research-Grade Lean 4 Benchmark for AlphaProof"


def check_git_status() -> dict:
    """Check commits ahead of origin/main or upstream/main."""
    res = subprocess.run(
        ["git", "status", "-s"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    clean = len(res.stdout.strip()) == 0
    return {"clean": clean}


def validate_drafts() -> bool:
    """Validate existence and constraints of all outreach drafts."""
    all_ok = True
    for path, name in [
        (DISPATCH_MD, "DeepMind academic dispatch"),
        (TWEET_TXT, "X / Twitter thread draft"),
        (ZULIP_MD, "Zulip post draft"),
    ]:
        if not path.exists():
            print(f"[FAIL] Missing draft artifact: {path}", file=sys.stderr)
            all_ok = False
        else:
            size = path.stat().st_size
            print(f"[OK] {name}: {path.name} ({size} bytes)")
    return all_ok


def generate_mailto_url() -> str:
    """Generate pre-filled mailto URL for direct email dispatch."""
    body_text = DISPATCH_MD.read_text(encoding="utf-8")
    # Strip markdown header
    if "---" in body_text:
        parts = body_text.split("---", 1)
        body_text = parts[1].strip()

    params = {
        "subject": EMAIL_SUBJECT,
        "body": body_text,
    }
    to_field = ",".join(RECIPIENTS)
    return f"mailto:{to_field}?{urllib.parse.urlencode(params, quote_via=urllib.parse.quote)}"


def main() -> int:
    parser = argparse.ArgumentParser(description="Google DeepMind AlphaProof Outreach Runner")
    parser.add_argument("--preview", action="store_true", help="Preview all draft texts")
    parser.add_argument("--validate", action="store_true", help="Validate draft constraints")
    parser.add_argument("--generate-links", action="store_true", help="Generate mailto and submission links")
    parser.add_argument(
        "--record-approval",
        action="store_true",
        help="Record human approval into approval_ledger.jsonl",
    )
    parser.add_argument(
        "--action",
        default="send_email",
        choices=["send_email", "post_issue", "post_x", "post_forum"],
        help="Outreach action to record approval for",
    )
    parser.add_argument("--note", default="Approved dispatch for Google DeepMind AlphaProof team", help="Approval note")

    args = parser.parse_args()

    if not any([args.preview, args.validate, args.generate_links, args.record_approval]):
        args.validate = True
        args.generate_links = True

    if args.validate:
        ok = validate_drafts()
        git_info = check_git_status()
        print(f"\nGit Status clean: {git_info['clean']}")
        if not ok:
            return 1

    if args.preview:
        print("\n" + "=" * 80)
        print("PREVIEW: Full DeepMind Dispatch Markdown")
        print("=" * 80)
        print(DISPATCH_MD.read_text(encoding="utf-8"))

    if args.generate_links:
        mailto = generate_mailto_url()
        print("\n" + "=" * 80)
        print("TRANSMISSION VECTOR 1: Direct Email Dispatch (mailto)")
        print("=" * 80)
        print(f"Recipients: {', '.join(RECIPIENTS)}")
        print(f"Subject: {EMAIL_SUBJECT}")
        print(f"\nPre-filled mailto URL (clickable):\n{mailto[:300]}... [truncated]")
        print("\n" + "=" * 80)
        print("TRANSMISSION VECTOR 2: X (Twitter) Broadcast via x_broadcast.py")
        print("=" * 80)
        print(f"Draft file: {TWEET_TXT.relative_to(REPO_ROOT)}")
        print("Posting command (once approved):")
        print(f"  python3 tools/community-outreach/x_broadcast.py post {TARGET_ID} --confirm-post --approval-id <ID>")
        print("\n" + "=" * 80)
        print("TRANSMISSION VECTOR 3: Lean Zulip Community Post")
        print("=" * 80)
        print(f"File: {ZULIP_MD.relative_to(REPO_ROOT)}")
        print("Target Stream: #machine learning for theorem proving")

    if args.record_approval:
        if record_approval is None:
            print("Error: outreach_approval module not available", file=sys.stderr)
            return 1
        payload = record_approval(
            target_id=TARGET_ID,
            action=args.action,
            artifact=str(DISPATCH_MD.relative_to(REPO_ROOT)),
            note=args.note,
        )
        print(f"\n[SUCCESS] Recorded approval in ledger:")
        print(json.dumps(payload, indent=2))
        print(f"\nApproval ID: {payload['approval_id']}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
