#!/usr/bin/env python3
"""Enforce PhysLean theorem discipline in Lean 4 files.

Rules enforced:
  1. Every ``theorem`` declaration must have a preceding ``/-- ... -/`` docstring
     (intervening ``@[...]`` attributes and declaration modifiers are permitted).
  2. The ``theorem`` keyword may only appear in files listed in
     ``scripts/lint/exemptions/Theorems.txt`` (non-exempted files should use
     ``lemma`` for intermediate results, reserving ``theorem`` for exempted
     landmark/canonical owner files).
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_THEOREMS_EXEMPTIONS = REPO_ROOT / "scripts" / "lint" / "exemptions" / "Theorems.txt"

THEOREM_LINE_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|private|protected|scoped|local|unsafe|partial)\s+)*"
    r"theorem\s+([A-Za-z0-9_'.«»]+)"
)
ATTR_OR_MOD_LINE_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]|(?:noncomputable|private|protected|scoped|local|unsafe|partial))\s*$"
)


def rel_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def load_exemptions(path: Path | None) -> set[str]:
    if path is None or not path.exists():
        return set()
    out: set[str] = set()
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            out.add(line)
            if line.startswith("lean/"):
                out.add("src/" + line[5:])
            elif line.startswith("src/"):
                out.add("lean/" + line[4:])
    return out


def git_changed_lean_files(base_ref: str | None, staged: bool) -> list[Path]:
    cmd = ["git", "diff", "--name-only", "--diff-filter=ACMR"]
    if staged:
        cmd.append("--cached")
    elif base_ref:
        cmd.extend([base_ref, "HEAD"])
    res = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True, text=True, check=True)
    out: list[Path] = []
    for line in res.stdout.splitlines():
        line = line.strip()
        if line.endswith(".lean"):
            p = REPO_ROOT / line
            if p.is_file():
                out.append(p)
    return sorted(set(out))


def collect_lean_files(paths: list[str]) -> list[Path]:
    collected: list[Path] = []
    for raw in paths:
        p = Path(raw)
        if not p.is_absolute():
            p = REPO_ROOT / p
        if p.is_file() and p.suffix == ".lean":
            collected.append(p)
        elif p.is_dir():
            for child in sorted(p.rglob("*.lean")):
                if any(part.startswith(".") or part == "lake-packages" for part in child.parts):
                    continue
                collected.append(child)
    return sorted(set(collected))


def has_preceding_docstring(lines: list[str], theorem_idx: int) -> bool:
    """Check whether line `theorem_idx` (0-based) is preceded by a `/-- ... -/` docstring."""
    j = theorem_idx - 1
    while j >= 0:
        s = lines[j].strip()
        if not s or ATTR_OR_MOD_LINE_RE.match(s):
            j -= 1
            continue
        break
    if j < 0:
        return False

    # Walk backward from line j to find the opening of a block comment `-/`
    if not lines[j].rstrip().endswith("-/"):
        return False

    k = j
    while k >= 0:
        line_k = lines[k]
        if "/--" in line_k:
            return True
        if "/-!" in line_k or (
            "/-" in line_k and "/--" not in line_k and "/-!" not in line_k
        ):
            return False
        k -= 1
    return False


def scan_file(path: Path) -> list[tuple[int, str, bool]]:
    """Return list of (1-based line, theorem_name, has_docstring) for each theorem in `path`."""
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError):
        return []

    results: list[tuple[int, str, bool]] = []
    in_block_comment = 0

    for idx, raw in enumerate(lines):
        # Track nested block comments coarsely outside strings
        stripped = raw.strip()
        if in_block_comment > 0:
            in_block_comment += raw.count("/-") - raw.count("-/")
            if in_block_comment < 0:
                in_block_comment = 0
            continue

        if stripped.startswith("--"):
            continue

        if stripped.startswith("/-"):
            delta = raw.count("/-") - raw.count("-/")
            if delta > 0:
                in_block_comment += delta
            continue

        m = THEOREM_LINE_RE.match(raw)
        if m:
            thm_name = m.group(1)
            has_doc = has_preceding_docstring(lines, idx)
            results.append((idx + 1, thm_name, has_doc))

    return results


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Enforce theorem docstrings and scripts/lint/exemptions/Theorems.txt allowlist."
    )
    parser.add_argument(
        "paths",
        nargs="*",
        default=["lean/InfoGeometry"],
        help="Lean files or directories to lint (default: lean/InfoGeometry).",
    )
    parser.add_argument(
        "--exemptions",
        type=Path,
        default=DEFAULT_THEOREMS_EXEMPTIONS,
        help="Allowlist of files permitted to use the `theorem` keyword.",
    )
    parser.add_argument(
        "--staged",
        action="store_true",
        help="Only lint staged .lean files.",
    )
    parser.add_argument(
        "--changed-since",
        default=None,
        help="Only lint .lean files changed since the given git ref.",
    )
    parser.add_argument(
        "--write-exemptions",
        action="store_true",
        help="Populate scripts/lint/exemptions/Theorems.txt with all scanned files currently containing `theorem`.",
    )
    args = parser.parse_args()

    if args.staged or args.changed_since:
        files = git_changed_lean_files(args.changed_since, args.staged)
    else:
        files = collect_lean_files(args.paths)

    if args.write_exemptions:
        files_with_theorems: list[str] = []
        for path in files:
            thms = scan_file(path)
            if thms:
                files_with_theorems.append(rel_path(path))
        args.exemptions.parent.mkdir(parents=True, exist_ok=True)
        header = (
            "# Files exempted to use the `theorem` keyword (PhysLean model).\n"
            "# Non-exempted files must use `lemma` unless added here.\n"
            "# Every `theorem` in any file must have a `/-- ... -/` docstring.\n"
        )
        args.exemptions.write_text(
            header + "\n".join(sorted(set(files_with_theorems))) + "\n",
            encoding="utf-8",
        )
        print(
            f"[theorem_lint] wrote {len(files_with_theorems)} exempted file(s) to {rel_path(args.exemptions)}"
        )
        return 0

    exempted_files = load_exemptions(args.exemptions)
    unexempted_violations: list[str] = []
    undocumented_violations: list[str] = []
    total_theorems = 0

    for path in files:
        rel = rel_path(path)
        thms = scan_file(path)
        if not thms:
            continue
        total_theorems += len(thms)
        if rel not in exempted_files:
            first_line, first_name, _ = thms[0]
            unexempted_violations.append(
                f"{rel}:{first_line}: `theorem {first_name}` (+ {len(thms) - 1} more) in non-exempted file "
                f"(use `lemma` or add `{rel}` to {rel_path(args.exemptions)})"
            )
        for line_no, thm_name, has_doc in thms:
            if not has_doc:
                undocumented_violations.append(
                    f"{rel}:{line_no}: `theorem {thm_name}` is missing a `/-- ... -/` docstring"
                )

    if unexempted_violations or undocumented_violations:
        print(
            f"[theorem_lint] FAILED "
            f"(unexempted files: {len(unexempted_violations)}, "
            f"undocumented theorems: {len(undocumented_violations)}):"
        )
        for v in (unexempted_violations + undocumented_violations)[:100]:
            print(f"  - {v}")
        total_v = len(unexempted_violations) + len(undocumented_violations)
        if total_v > 100:
            print(f"  ... and {total_v - 100} more")
        return 1

    print(
        f"[theorem_lint] PASSED ({len(files)} file(s) scanned, {total_theorems} theorem(s) verified)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
