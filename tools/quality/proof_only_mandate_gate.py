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
    from tools.quality.witness_pattern_scanner import scan_directory
else:
    from tools.pathing import normalize_user_path, repo_root
    from tools.quality.witness_pattern_scanner import scan_directory


ROOT = repo_root()
DEFAULT_POLICY = ROOT / "tools" / "quality" / "proof_only_mandate_policy.json"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=(
            "Hard gate for proof-only policy: no axiom/postulate decls, "
            "no sorry/admit terms, no Prop witness-pack surfaces."
        )
    )
    p.add_argument(
        "--policy",
        default=str(DEFAULT_POLICY.relative_to(ROOT)),
        help="Path to mandate policy JSON.",
    )
    return p.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception as ex:
        raise SystemExit(f"[proof-only-gate] failed reading {path}: {ex}") from ex
    if not isinstance(payload, dict):
        raise SystemExit(f"[proof-only-gate] expected object JSON at {path}")
    return payload


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    in_char = False

    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out.extend("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                if ch == "\"":
                    in_string = False
                i += 1
            continue

        if in_char:
            out.append(ch)
            if ch == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                if ch == "'":
                    in_char = False
                i += 1
            continue

        if ch == "-" and nxt == "-":
            out.extend(" " for _ in iter(text[i:].split("\n", 1)[0]))
            i += len(text[i:].split("\n", 1)[0])
            continue

        if ch == "/" and nxt == "-":
            depth = 1
            out.extend("  ")
            i += 2
            continue

        if ch == "\"":
            in_string = True
        elif ch == "'":
            in_char = True
        out.append(ch)
        i += 1

    return "".join(out)


def main() -> int:
    args = parse_args()
    policy_path = normalize_user_path(args.policy, DEFAULT_POLICY)
    policy = load_json(policy_path)

    root_rel = str(policy.get("root", "lean/InfoGeometry")).strip()
    root = normalize_user_path(root_rel, ROOT / root_rel)
    if not root.exists():
        print(f"[proof-only-gate] missing root: {root}")
        return 1

    decl_keywords = policy.get("forbiddenDeclarationKeywords", [])
    decl_name_regex = policy.get("forbiddenDeclarationNameRegex", [])
    term_regex = policy.get("forbiddenTermRegex", [])
    prop_field_regex = policy.get("forbiddenPropFieldRegex", [])
    field_name_regex = policy.get("forbiddenFieldNameRegex", [])
    if (
        not isinstance(decl_keywords, list)
        or not isinstance(decl_name_regex, list)
        or not isinstance(term_regex, list)
        or not isinstance(prop_field_regex, list)
        or not isinstance(field_name_regex, list)
    ):
        print("[proof-only-gate] invalid policy lists")
        return 1

    decl_keywords = [str(x).strip() for x in decl_keywords if str(x).strip()]
    decl_name_regex = [str(x).strip() for x in decl_name_regex if str(x).strip()]
    term_regex = [str(x).strip() for x in term_regex if str(x).strip()]
    prop_field_regex = [str(x).strip() for x in prop_field_regex if str(x).strip()]
    field_name_regex = [str(x).strip() for x in field_name_regex if str(x).strip()]
    if not decl_keywords or not term_regex or not prop_field_regex:
        print("[proof-only-gate] empty forbidden keyword/regex set(s)")
        return 1

    decl_patterns = [
        re.compile(rf"^\s*{re.escape(kw)}\b", re.MULTILINE) for kw in decl_keywords
    ]
    decl_name_patterns = [re.compile(rx, re.MULTILINE) for rx in decl_name_regex]
    term_patterns = [re.compile(rx, re.MULTILINE) for rx in term_regex]
    prop_field_patterns = [re.compile(rx, re.MULTILINE) for rx in prop_field_regex]
    field_name_patterns = [re.compile(rx, re.MULTILINE) for rx in field_name_regex]

    failures: list[str] = []
    files = sorted(root.rglob("*.lean"))
    print(f"[proof-only-gate] scanning {len(files)} Lean files under {root}")
    for path in files:
        text = path.read_text(encoding="utf-8")
        stripped = strip_lean_comments(text)
        for kw, pat in zip(decl_keywords, decl_patterns):
            if pat.search(stripped):
                failures.append(f"forbidden declaration `{kw}` in {path}")
        for rx, pat in zip(decl_name_regex, decl_name_patterns):
            if pat.search(stripped):
                failures.append(f"forbidden declaration-name pattern /{rx}/ in {path}")
        for rx, pat in zip(term_regex, term_patterns):
            if pat.search(stripped):
                failures.append(f"forbidden placeholder pattern /{rx}/ in {path}")
        for rx, pat in zip(prop_field_regex, prop_field_patterns):
            if pat.search(stripped):
                failures.append(f"forbidden Prop hypothesis-field pattern /{rx}/ in {path}")
        for rx, pat in zip(field_name_regex, field_name_patterns):
            if pat.search(stripped):
                failures.append(f"forbidden field-name pattern /{rx}/ in {path}")

    witness_hits = scan_directory(root)
    if witness_hits:
        failures.append(
            f"witness-pack debt found: {len(witness_hits)} hit(s) under {root}"
        )

    if failures:
        print("[proof-only-gate] FAILED")
        for msg in failures:
            print(f"  - {msg}")
        return 1

    print("[proof-only-gate] PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
