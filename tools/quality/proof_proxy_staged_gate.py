#!/usr/bin/env python3
"""Pre-commit gate for proof-cleanup: reject newly staged proof-proxy carriers."""

from __future__ import annotations

import re
import subprocess
import sys

FIELD_RE = re.compile(r"^\s{2,}([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(?!=)(.+?)\s*$")
PROHIBITED_NAME_RE = re.compile(
    r"(?:^|_)(law|laws|certificate|cert|witness|valid|guard|socket|readback|assumption|axiom|proof)(?:_|$)",
    re.IGNORECASE,
)
PROPISH_TYPE_RE = re.compile(r"\bProp\b|=|↔|<->|≤|>=|≥|<|>|∈|∉|⊆|⊂|⊇|∧|∨|∀|∃")
TOP_ANY_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\n]+\]\s*)?(axiom|theorem|lemma|def|abbrev|structure|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
DEBT_BURIAL_COMMENT_RE = re.compile(
    r"\b(DEBT|OPEN CLOSURE DEBT|missing proof|not a proof|removed|no Lean declaration|owner-side proof)\b",
    re.IGNORECASE,
)


def git(args: list[str]) -> str:
    return subprocess.check_output(["git", *args], text=True)


def main() -> int:
    out = git(["diff", "--cached", "--unified=0", "--", "*.lean"])
    failures: list[str] = []
    path = ""
    line_no: int | None = None
    removed_decl_files: set[str] = set()
    debt_comment_files: set[str] = set()
    for line in out.splitlines():
        if line.startswith("+++ b/"):
            path = line[6:]
            continue
        if line.startswith("@@"):
            m = re.search(r"\+(\d+)(?:,(\d+))?", line)
            line_no = int(m.group(1)) if m else None
            continue
        if line.startswith("-") and not line.startswith("---"):
            if TOP_ANY_DECL_RE.match(line[1:].strip()):
                removed_decl_files.add(path)
            continue
        if not line.startswith("+") or line.startswith("+++"):
            if line_no is not None:
                line_no += 1
            continue
        added = line[1:]
        loc = f"{path}:{line_no}" if line_no is not None else path
        stripped = added.strip()
        if stripped.startswith(("--", "/-", "*")):
            if DEBT_BURIAL_COMMENT_RE.search(stripped):
                debt_comment_files.add(path)
            if line_no is not None:
                line_no += 1
            continue
        if "`" in stripped or '"' in stripped:
            if line_no is not None:
                line_no += 1
            continue
        if re.search(r"^\s*(axiom|postulate)\b|\b(admit|sorry)\b", stripped):
            failures.append(f"{loc}: staged forbidden placeholder `{stripped}`")
        fm = FIELD_RE.match(added)
        if fm and not stripped.startswith("have "):
            name, typ = fm.group(1), fm.group(2)
            if PROHIBITED_NAME_RE.search(name):
                failures.append(f"{loc}: staged prohibited proof-carrier field name `{name}`")
        if line_no is not None:
            line_no += 1
    for buried in sorted(removed_decl_files & debt_comment_files):
        failures.append(
            f"{buried}: staged deletion of Lean declarations with natural-language debt comments; keep open debt compiler-visible instead of burying it in prose"
        )

    if failures:
        print("proof_proxy_staged_gate: FAIL", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1
    print("proof_proxy_staged_gate: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
