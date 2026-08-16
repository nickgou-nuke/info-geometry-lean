#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
    from tools.quality.common import load_json
else:
    from tools.pathing import normalize_user_path, repo_root
    from tools.quality.common import load_json


ROOT = repo_root()
DEFAULT_POLICY = ROOT / "tools" / "quality" / "closure_debt_gate.json"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Enforce closure-debt no-regression gates on scoped module clusters: "
            "no banned tokens and required theorem-anchor presence."
        )
    )
    parser.add_argument(
        "--policy",
        default=str(DEFAULT_POLICY.relative_to(ROOT)),
        help="Path to closure debt gate policy JSON.",
    )
    return parser.parse_args()


def tokenize_count(text: str, token: str) -> int:
    return len(re.findall(rf"\b{re.escape(token)}\b", text))


def collect_group_modules(policy: dict[str, Any]) -> list[tuple[str, Path]]:
    rows = policy.get("groups", [])
    if not isinstance(rows, list) or not rows:
        raise SystemExit("[closure-gate] policy has no `groups` rows")
    out: list[tuple[str, Path]] = []
    for row in rows:
        if not isinstance(row, dict):
            raise SystemExit("[closure-gate] invalid group row (expected object)")
        name = str(row.get("name", "")).strip() or "unnamed"
        modules = row.get("modules", [])
        if not isinstance(modules, list) or not modules:
            raise SystemExit(f"[closure-gate] group `{name}` has no modules")
        for module in modules:
            if not isinstance(module, str) or not module.strip():
                raise SystemExit(f"[closure-gate] invalid module path in group `{name}`")
            path = normalize_user_path(module, ROOT / module)
            out.append((name, path))
    return out


def main() -> int:
    args = parse_args()
    policy_path = normalize_user_path(args.policy, DEFAULT_POLICY)
    if not policy_path.exists():
        print(f"[closure-gate] missing policy: {policy_path}")
        return 1

    policy = load_json(policy_path)
    banned_tokens = policy.get("bannedTokens", [])
    if not isinstance(banned_tokens, list) or not banned_tokens:
        print("[closure-gate] policy must define non-empty `bannedTokens`")
        return 1
    banned_tokens = [str(x).strip() for x in banned_tokens if str(x).strip()]
    if not banned_tokens:
        print("[closure-gate] policy has empty `bannedTokens` after normalization")
        return 1

    failures: list[str] = []
    print("[closure-gate] scanning closure frontier modules")
    for group_name, module_path in collect_group_modules(policy):
        if not module_path.exists():
            failures.append(f"[{group_name}] missing module: {module_path}")
            continue
        text = module_path.read_text(encoding="utf-8")
        row_counts: list[str] = []
        for token in banned_tokens:
            count = tokenize_count(text, token)
            row_counts.append(f"{token}={count}")
            if count > 0:
                failures.append(
                    f"[{group_name}] banned token `{token}` count={count} in {module_path}"
                )
        print(f"  - [{group_name}] {module_path}: " + ", ".join(row_counts))

    anchors = policy.get("requiredAnchors", [])
    if not isinstance(anchors, list):
        print("[closure-gate] invalid `requiredAnchors` (expected list)")
        return 1

    print("[closure-gate] checking required theorem anchors")
    for row in anchors:
        if not isinstance(row, dict):
            failures.append("invalid required anchor row (expected object)")
            continue
        rel = str(row.get("path", "")).strip()
        pattern = str(row.get("pattern", "")).strip()
        if not rel or not pattern:
            failures.append("invalid required anchor row (missing path/pattern)")
            continue
        path = normalize_user_path(rel, ROOT / rel)
        if not path.exists():
            failures.append(f"required anchor path missing: {path}")
            continue
        text = path.read_text(encoding="utf-8")
        if re.search(pattern, text, flags=re.MULTILINE) is None:
            failures.append(f"required anchor missing: pattern `{pattern}` in {path}")
        else:
            print(f"  - OK: `{pattern}` in {path}")

    if failures:
        print("[closure-gate] FAILED")
        for msg in failures:
            print(f"  - {msg}")
        return 1

    print("[closure-gate] PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

