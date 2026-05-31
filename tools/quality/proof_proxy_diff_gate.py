#!/usr/bin/env python3
"""Reject proof-cleanup diffs that hide proof debt in new wrappers/fields.

This gate is intentionally syntactic and conservative.  It is for proof-cleanup
workflows, where allowed edits are ordinary definitions/lemmas/theorems and
local proof bodies, not carrier/witness redesigns.
"""

from __future__ import annotations

import argparse
import re
import difflib
import subprocess
import sys
from pathlib import Path

TOP_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\n]+\]\s*)?(structure|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
FIELD_RE = re.compile(r"^\s{2,}([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(?!=)(.+?)\s*$")
TOP_ANY_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\n]+\]\s*)?(axiom|theorem|lemma|def|abbrev|structure|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
DEBT_BURIAL_COMMENT_RE = re.compile(
    r"\b(DEBT|OPEN CLOSURE DEBT|missing proof|not a proof|removed|no Lean declaration|owner-side proof)\b",
    re.IGNORECASE,
)
END_RE = re.compile(
    r"^\s*(def|theorem|lemma|abbrev|structure|class|inductive|namespace|section|end|variable|open|import)\b"
)
PROHIBITED_NAME_RE = re.compile(
    r"(?:^|_)(law|laws|certificate|cert|witness|valid|guard|socket|readback|assumption|axiom|proof)(?:_|$)",
    re.IGNORECASE,
)
PROXY_DECL_NAME_RE = re.compile(
    r"(Witness|Certificate|Certified|Socket|Guard|Law|Proxy|Readback|Assumption|Packet|(?:^|_)of_witness(?:_|$))",
    re.IGNORECASE,
)
PROXY_FILE_RE = re.compile(
    r"(Witness|Certificate|Socket|Proxy|Packet|Carrier)\.lean$",
    re.IGNORECASE,
)
PROPISH_TYPE_RE = re.compile(
    r"\bProp\b|=|↔|<->|≤|>=|≥|<|>|∈|∉|⊆|⊂|⊇|∧|∨|∀|∃"
)


def git(args: list[str], *, text: bool = True) -> str:
    return subprocess.check_output(["git", *args], text=text)


def read_at(ref: str, path: str) -> str:
    try:
        return git(["show", f"{ref}:{path}"])
    except subprocess.CalledProcessError:
        return ""


def read_current(path: str) -> str:
    try:
        return Path(path).read_text()
    except FileNotFoundError:
        return ""


def structure_fields(src: str) -> dict[str, set[str]]:
    fields: dict[str, set[str]] = {}
    current: str | None = None
    for line in src.splitlines():
        m = TOP_DECL_RE.match(line)
        if m:
            current = m.group(2)
            fields.setdefault(current, set())
            continue
        if current is not None:
            if END_RE.match(line) and not line.startswith((" ", "\t")):
                current = None
                m2 = TOP_DECL_RE.match(line)
                if m2:
                    current = m2.group(2)
                    fields.setdefault(current, set())
                continue
            fm = FIELD_RE.match(line)
            if fm and not line.lstrip().startswith(("--", "/-", "where")):
                fields.setdefault(current, set()).add(fm.group(1))
    return fields


def lean_pathspecs(paths: list[str]) -> list[str]:
    if not paths:
        return ["*.lean"]
    specs: list[str] = []
    for path in paths:
        p = Path(path)
        if path.endswith(".lean") or p.is_file():
            specs.append(path)
        else:
            specs.append(f"{path.rstrip('/')}/**/*.lean")
    return specs


def added_lean_files(base: str, paths: list[str]) -> list[str]:
    out = git(["diff", "--name-only", base, "--", *lean_pathspecs(paths)])
    return [line.strip() for line in out.splitlines() if line.strip()]


def diff_added_lines(base: str, paths: list[str]) -> list[tuple[str, int | None, str]]:
    out = git(["diff", "--unified=0", base, "--", *lean_pathspecs(paths)])
    return parse_added_lines(out)


def parse_added_lines(out: str) -> list[tuple[str, int | None, str]]:
    path = ""
    new_line: int | None = None
    results: list[tuple[str, int | None, str]] = []
    for line in out.splitlines():
        if line.startswith("+++ b/"):
            path = line[6:]
            continue
        if line.startswith("@@"):
            m = re.search(r"\+(\d+)(?:,(\d+))?", line)
            new_line = int(m.group(1)) if m else None
            continue
        if line.startswith("+") and not line.startswith("+++"):
            results.append((path, new_line, line[1:]))
            if new_line is not None:
                new_line += 1
        elif not line.startswith("-") and new_line is not None:
            new_line += 1
    return results


def parse_removed_decl_files(out: str) -> set[str]:
    return {path for path, _kind, _name in parse_removed_decl_entries(out)}


def parse_removed_decl_entries(out: str) -> list[tuple[str, str, str]]:
    path = ""
    removed: list[tuple[str, str, str]] = []
    for line in out.splitlines():
        if line.startswith("--- a/"):
            path = line[6:]
            continue
        if line.startswith("-") and not line.startswith("---"):
            m = TOP_ANY_DECL_RE.match(line[1:].strip())
            if m:
                removed.append((path, m.group(1), m.group(2)))
    return removed


def diff_removed_decl_files(base: str, paths: list[str]) -> set[str]:
    out = git(["diff", "--unified=0", base, "--", *lean_pathspecs(paths)])
    return parse_removed_decl_files(out)


def diff_removed_decl_entries(base: str, paths: list[str]) -> list[tuple[str, str, str]]:
    out = git(["diff", "--unified=0", base, "--", *lean_pathspecs(paths)])
    return parse_removed_decl_entries(out)


def snapshot_removed_decl_files(snapshot: Path, files: list[str]) -> set[str]:
    return {path for path, _kind, _name in snapshot_removed_decl_entries(snapshot, files)}


def snapshot_removed_decl_entries(snapshot: Path, files: list[str]) -> list[tuple[str, str, str]]:
    removed: set[str] = set()
    entries: list[tuple[str, str, str]] = []
    for path in files:
        before = snapshot / path
        before_lines = (before.read_text() if before.exists() else "").splitlines()
        after_lines = read_current(path).splitlines()
        diff = "\n".join(
            difflib.unified_diff(before_lines, after_lines, fromfile=f"a/{path}", tofile=f"b/{path}", n=0, lineterm="")
        )
        entries.extend(parse_removed_decl_entries(diff))
    return entries


def snapshot_changed_files(snapshot: Path, paths: list[str]) -> list[str]:
    changed: list[str] = []
    candidates: set[str] = set()
    for root in paths:
        p = Path(root)
        if p.is_file() and p.suffix == ".lean":
            candidates.add(str(p))
        elif p.is_dir():
            candidates.update(str(q) for q in p.rglob("*.lean"))
    for path in sorted(candidates):
        before = snapshot / path
        before_text = before.read_text() if before.exists() else ""
        after_text = read_current(path)
        if before_text != after_text:
            changed.append(path)
    return changed


def snapshot_added_lines(snapshot: Path, files: list[str]) -> list[tuple[str, int | None, str]]:
    results: list[tuple[str, int | None, str]] = []
    for path in files:
        before = snapshot / path
        before_lines = (before.read_text() if before.exists() else "").splitlines()
        after_lines = read_current(path).splitlines()
        diff = "\n".join(
            difflib.unified_diff(before_lines, after_lines, fromfile=f"a/{path}", tofile=f"b/{path}", n=0, lineterm="")
        )
        results.extend(parse_added_lines(diff))
    return results


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default="HEAD", help="base git ref to compare against")
    ap.add_argument("--snapshot", help="pre-edit snapshot directory; overrides --base and handles dirty worktrees")
    ap.add_argument("paths", nargs="*", default=["lean"], help="paths to compare when --snapshot is used")
    ap.add_argument("--allow-new-structures", action="store_true")
    args = ap.parse_args()

    failures: list[str] = []
    snapshot = Path(args.snapshot) if args.snapshot else None
    changed_files = snapshot_changed_files(snapshot, args.paths) if snapshot else added_lean_files(args.base, args.paths)
    added_lines = snapshot_added_lines(snapshot, changed_files) if snapshot else diff_added_lines(args.base, args.paths)
    removed_decl_files = (
        snapshot_removed_decl_files(snapshot, changed_files)
        if snapshot
        else diff_removed_decl_files(args.base, args.paths)
    )
    removed_decl_entries = (
        snapshot_removed_decl_entries(snapshot, changed_files)
        if snapshot
        else diff_removed_decl_entries(args.base, args.paths)
    )
    debt_comment_files: set[str] = set()

    for path, line_no, line in added_lines:
        loc = f"{path}:{line_no}" if line_no is not None else path
        stripped = line.strip()
        if stripped.startswith(("--", "/-", "*")):
            if DEBT_BURIAL_COMMENT_RE.search(stripped):
                debt_comment_files.add(path)
            continue
        if "`" in stripped or '"' in stripped:
            continue
        if re.search(r"^\s*(axiom|postulate)\b|\b(admit|sorry)\b", stripped):
            failures.append(f"{loc}: added forbidden placeholder `{stripped}`")
        if re.match(r"(?:structure|class)\s+", stripped):
            failures.append(f"{loc}: added new carrier declaration `{stripped}`")
        fm = FIELD_RE.match(line)
        if fm and not stripped.startswith("have "):
            name, typ = fm.group(1), fm.group(2)
            if PROHIBITED_NAME_RE.search(name):
                failures.append(f"{loc}: added prohibited proof-carrier field name `{name}`")

    for path in sorted(removed_decl_files & debt_comment_files):
        failures.append(
            f"{path}: deleted Lean declarations while adding natural-language debt comments; keep open debt compiler-visible instead of burying it in prose"
        )

    for path, kind, name in removed_decl_entries:
        if PROXY_FILE_RE.search(path):
            continue
        if not PROXY_DECL_NAME_RE.search(name):
            failures.append(
                f"{path}: deleted non-proxy Lean declaration `{kind} {name}` during proof cleanup"
            )

    for path in changed_files:
        before_text = (snapshot / path).read_text() if snapshot and (snapshot / path).exists() else read_at(args.base, path)
        before = structure_fields(before_text)
        after = structure_fields(read_current(path))
        for struct_name in sorted(after.keys() - before.keys()):
            if not args.allow_new_structures:
                failures.append(f"{path}: added new structure/class `{struct_name}` during proof cleanup")
        for struct_name in sorted(after.keys() & before.keys()):
            added = sorted(after[struct_name] - before[struct_name])
            if added:
                failures.append(
                    f"{path}: added fields to existing structure/class `{struct_name}`: {', '.join(added)}"
                )

    if failures:
        print("proof_proxy_diff_gate: FAIL")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("proof_proxy_diff_gate: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
