#!/usr/bin/env python3
"""Reject cleanup cycles that make touched Lean files semantically worse."""

from __future__ import annotations

import argparse
import subprocess
from pathlib import Path

import semantic_vacuity_gate as vacuity


def git(args: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], text=True, capture_output=True, check=check)


def git_text_at(ref: str, path: str) -> str:
    proc = git(["show", f"{ref}:{path}"], check=False)
    return proc.stdout if proc.returncode == 0 else ""


def current_lean_files(paths: list[str]) -> set[str]:
    files: set[str] = set()
    for root in paths:
        p = Path(root)
        if p.is_file() and p.suffix == ".lean":
            files.add(str(p))
        elif p.is_dir():
            files.update(str(q) for q in p.rglob("*.lean"))
    return files


def snapshot_lean_files(snapshot: Path, paths: list[str]) -> set[str]:
    files: set[str] = set()
    for root in paths:
        snap_root = snapshot / root
        if snap_root.is_file() and snap_root.suffix == ".lean":
            files.add(root)
        elif snap_root.is_dir():
            files.update(str(q.relative_to(snapshot)) for q in snap_root.rglob("*.lean"))
    return files


def changed_files(snapshot: Path, paths: list[str]) -> list[str]:
    candidates = current_lean_files(paths) | snapshot_lean_files(snapshot, paths)
    changed: list[str] = []
    for file in sorted(candidates):
        before = snapshot / file
        after = Path(file)
        before_text = before.read_text(encoding="utf-8") if before.exists() else ""
        after_text = after.read_text(encoding="utf-8") if after.exists() else ""
        if before_text != after_text:
            changed.append(file)
    return changed


def changed_files_from_git(base: str, paths: list[str]) -> list[str]:
    out = git(["diff", "--name-only", base, "--", *paths]).stdout
    return sorted(line for line in out.splitlines() if line.endswith(".lean"))


def finding_counts_text(path: str, text: str, categories: dict) -> tuple[int, int]:
    findings = vacuity.audit_text(path, text, categories)
    errors = sum(1 for f in findings if f.severity == "error")
    return len(findings), errors


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", type=Path)
    ap.add_argument("--base", default="HEAD", help="git ref to compare against when --snapshot is absent")
    ap.add_argument("--patterns", type=Path, default=vacuity.DEFAULT_PATTERNS)
    ap.add_argument("paths", nargs="*", default=["lean"])
    args = ap.parse_args()

    policy = vacuity.load_patterns(args.patterns)
    categories = policy["categories"]
    failures: list[str] = []
    checked = 0

    files = changed_files(args.snapshot, args.paths) if args.snapshot else changed_files_from_git(args.base, args.paths)

    for file in files:
        after = Path(file)
        if args.snapshot:
            before = args.snapshot / file
            before_text = before.read_text(encoding="utf-8") if before.exists() else ""
        else:
            before_text = git_text_at(args.base, file)
        after_text = after.read_text(encoding="utf-8") if after.exists() else ""
        before_total, before_errors = finding_counts_text(file, before_text, categories)
        after_total, after_errors = finding_counts_text(file, after_text, categories)
        checked += 1
        if after_errors > before_errors or after_total > before_total:
            failures.append(
                f"{file}: semantic vacuity regressed "
                f"errors {before_errors}->{after_errors}, total {before_total}->{after_total}"
            )

    if failures:
        print("semantic_regression_gate: FAIL")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print(f"semantic_regression_gate: ok ({checked} changed Lean files)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
