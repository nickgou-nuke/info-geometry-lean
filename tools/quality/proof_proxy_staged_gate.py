#!/usr/bin/env python3
"""Pre-commit gate for staged Lean headers and proof-integrity violations."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

TOP_ANY_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\n]+\]\s*)?(axiom|theorem|lemma|def|abbrev|structure|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
PROP_STRUCTURE_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\n]+\]\s*)*(?:private\s+|protected\s+)?structure\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\b([^\n]*)\n((?:[ \t]*\n|[ \t]+[^\s\n][^\n]*\n)*)"
)
PROP_RESULT_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\n]+\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|example)\b"
    r"[^\n]*?:\s*([A-Za-z_][A-Za-z0-9_'.]*)\b(?:[^\n]*?\b(where)\b|\s*:=)"
)
FIELD_ASSIGN_RE = re.compile(r"(?m)^\s+([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*([^\n]+)")
DEBT_BURIAL_COMMENT_RE = re.compile(
    r"\b(DEBT|OPEN CLOSURE DEBT|missing proof|not a proof|removed|no Lean declaration|owner-side proof)\b",
    re.IGNORECASE,
)
REQUIRED_LEAN_COPYRIGHT_HEADER = (
    "/-\n"
    "Copyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Authors: InfoGeometry Engine Contributors\n"
    "-/\n"
)
EXECUTED_GATE_SOURCES = (
    "tools/quality/proof_proxy_staged_gate.py",
    "tools/infra/opengauss_screener.py",
)


def git(args: list[str]) -> str:
    return subprocess.check_output(["git", *args], text=True)


def checker_index_mismatches(repo_root: Path | None = None) -> list[str]:
    """Return gate source paths whose worktree contents differ from the index.

    The hook executes these files from the worktree while reading Lean payloads
    from stage-0 index blobs. Refuse that mixed snapshot if checker edits have
    not been staged (or unstaged) consistently.
    """
    result = subprocess.run(
        ["git", "diff", "--quiet", "--", *EXECUTED_GATE_SOURCES],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        return []
    if result.returncode == 1:
        changed = subprocess.run(
            ["git", "diff", "--name-only", "--", *EXECUTED_GATE_SOURCES],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=True,
        ).stdout
        return [line for line in changed.splitlines() if line]
    detail = result.stderr.strip() or f"git diff exited {result.returncode}"
    return [f"gate-source-index-comparison-failed: {detail}"]


def aggregate_prop_constructors(source: str) -> list[tuple[str, str]]:
    """Find theorem/def constructors that merely bundle a Prop structure's fields.

    Predicate structures are allowed. This catches the aggregate theorem wrapper
    structurally, independent of names chosen for its type, theorem, or fields,
    across `where`, `{ ... }`, `⟨...⟩`, and `.mk` constructor styles.
    """
    try:
        from tools.infra.opengauss_screener import _strip_lean_comments_and_strings
        source = _strip_lean_comments_and_strings(source)
    except ImportError:
        pass
    found: list[tuple[str, str]] = []
    for structure in PROP_STRUCTURE_RE.finditer(source):
        type_name, header, body = structure.groups()
        if not re.search(r":\s*Prop\s+where\s*$", header):
            continue
        fields = [
            item.group(1)
            for item in re.finditer(r"(?m)^\s+([A-Za-z_][A-Za-z0-9_']*)\s*:", body)
        ]
        field_set = set(fields)
        if len(field_set) < 2:
            continue
        for constructor in PROP_RESULT_RE.finditer(source):
            if constructor.group(1) != type_name:
                continue
            is_where = constructor.group(2) == "where"
            tail = source[constructor.end():]
            next_decl = re.search(r"(?m)^\S", tail)
            if next_decl:
                tail = tail[:next_decl.start()]
            if is_where:
                assignments = FIELD_ASSIGN_RE.findall(tail)
                selected = [(name, value.strip()) for name, value in assignments if name in field_set]
                if field_set <= {name for name, _ in selected} and all(
                    re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*(?:\s+[^\n]+)?", value)
                    for _, value in selected
                ):
                    found.append((type_name, constructor.group(0).strip()))
            else:
                rhs = tail.strip()
                brace_assignments = re.findall(
                    r"([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*([^,}\n]+)", rhs
                )
                selected = [(name, value.strip()) for name, value in brace_assignments if name in field_set]
                if field_set <= {name for name, _ in selected}:
                    found.append((type_name, constructor.group(0).strip()))
                    continue
                anon = re.search(r"⟨([^⟩]+)⟩", rhs)
                if anon and len([p for p in anon.group(1).split(",") if p.strip()]) >= len(field_set):
                    found.append((type_name, constructor.group(0).strip()))
                    continue
                if re.search(rf"\b{re.escape(type_name)}\.mk\b", rhs):
                    found.append((type_name, constructor.group(0).strip()))
    return found


def check_text(lean_path: str, source: str) -> list[str]:
    """Check staged Lean source for its required header and proof-integrity violations."""
    failures: list[str] = []
    if not source.startswith(REQUIRED_LEAN_COPYRIGHT_HEADER):
        failures.append(
            f"{lean_path}: missing or malformed required InfoGeometry copyright and license header"
        )
    try:
        from tools.infra.opengauss_screener import check_authored_axioms_and_holes
        for violation in check_authored_axioms_and_holes(source):
            failures.append(
                f"{lean_path}:{violation.line_number}: {violation.message} ({violation.matched_text})"
            )
    except ImportError:
        failures.append(
            f"{lean_path}: cannot load the canonical QMS source checker; refusing to certify this staged Lean file"
        )
    for type_name, constructor in aggregate_prop_constructors(source):
        failures.append(
            f"{lean_path}: `{constructor}` constructs Prop structure `{type_name}` by bundling field proofs; audit the owner theorems directly"
        )
    return failures


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
        if re.search(r"^\s*(?:axiom|postulate)\s+(?:«[^»\n]+»|[^\W\d][\w'.]*)\s*:|^\s*(?:admit|sorry|sorryAx)\b", stripped):
            failures.append(f"{loc}: staged forbidden placeholder `{stripped}`")
        if line_no is not None:
            line_no += 1
    staged_lean_paths = set(
        path
        for path in subprocess.check_output(
            ["git", "diff", "--cached", "--name-only", "-z", "--diff-filter=ACMRT", "--", "*.lean"]
        ).split(b"\0")
        if path
    )
    if staged_lean_paths:
        mismatches = checker_index_mismatches()
        if mismatches:
            failures.append(
                "executed QMS gate source differs from staged index; stage or discard checker edits before committing: "
                + ", ".join(mismatches)
            )
    staged_entries = subprocess.check_output(["git", "ls-files", "-s", "-z", "--", "*.lean"])
    blob_by_path: dict[bytes, str] = {}
    for entry in staged_entries.split(b"\0"):
        if not entry:
            continue
        metadata, raw_path = entry.split(b"\t", 1)
        fields = metadata.decode("ascii").split()
        if len(fields) == 3 and fields[2] == "0":
            blob_by_path[raw_path] = fields[1]
    missing_stage_blobs = staged_lean_paths - blob_by_path.keys()
    for raw_path in sorted(missing_stage_blobs):
        failures.append(
            f"{raw_path.decode('utf-8', errors='replace')}: staged Lean path has no stage-0 index blob to validate"
        )
    paths_and_blobs = [
        (path, blob_by_path[path]) for path in sorted(staged_lean_paths) if path in blob_by_path
    ]
    blob_data = subprocess.run(
        ["git", "cat-file", "--batch"],
        input=("\n".join(blob for _, blob in paths_and_blobs) + "\n").encode(),
        capture_output=True,
        check=True,
    ).stdout
    cursor = 0
    for raw_path, _blob in paths_and_blobs:
        header_end = blob_data.index(b"\n", cursor)
        header = blob_data[cursor:header_end].split()
        size = int(header[2])
        start = header_end + 1
        source = blob_data[start:start + size].decode("utf-8", errors="replace")
        cursor = start + size + 1
        lean_path = raw_path.decode("utf-8", errors="replace")
        failures.extend(check_text(lean_path, source))
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
