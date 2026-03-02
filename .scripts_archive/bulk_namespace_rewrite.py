#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
from pathlib import Path

# Heuristics
NS_RE = re.compile(r"^(\s*)namespace\s+([A-Za-z0-9_.']+)\s*$")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z0-9_.']+)?\s*$")
IMPORT_RE = re.compile(r"^\s*import\s+")
MODULE_DOC_START_RE = re.compile(r"^\s*/-!")
MODULE_DOC_END_RE = re.compile(r".*-\s*/\s*$")
DECL_RE = re.compile(
    r"^\s*(def|theorem|lemma|abbrev|opaque|instance|structure|class|inductive|syntax|macro_rules|elab)\b"
)

SKIP_BASENAMES = {
    "BlueprintTags.lean",
    "auto_blueprints.lean",
    "Library.lean",       # usually aggregator
    "Experimental.lean",  # often aggregator
}
SKIP_RELATIVE = {
    "InfoGeometry/BlueprintTags.lean",
    "InfoGeometry/auto_blueprints.lean",
}

def path_to_namespace(src_root: Path, file: Path, project_ns: str) -> str:
    rel = file.relative_to(src_root).with_suffix("")  # Projective/FaithfulKL
    parts = [project_ns] + list(rel.parts)
    return ".".join(parts)

def find_first_namespace(lines: list[str]) -> tuple[int, str] | None:
    for i, line in enumerate(lines):
        m = NS_RE.match(line)
        if m:
            return i, m.group(2)
    return None

def has_declarations(lines: list[str]) -> bool:
    return any(DECL_RE.match(line) for line in lines)

def insertion_index_after_header(lines: list[str]) -> int:
    i = 0
    n = len(lines)

    # imports
    while i < n and (lines[i].strip() == "" or IMPORT_RE.match(lines[i])):
        i += 1

    # optional module docstring immediately after imports/blank lines
    if i < n and MODULE_DOC_START_RE.match(lines[i]):
        i += 1
        while i < n and not MODULE_DOC_END_RE.match(lines[i]):
            i += 1
        if i < n:
            i += 1

    # consume following blank lines
    while i < n and lines[i].strip() == "":
        i += 1

    return i

def classify(file: Path, src_root: Path, project_ns: str, wrapAll: bool = False) -> tuple[str, str]:
    text = file.read_text(encoding="utf-8", errors="ignore")
    lines = text.splitlines()
    suggested = path_to_namespace(src_root, file, project_ns)

    if file.name in SKIP_BASENAMES or str(file).replace("\\", "/") in SKIP_RELATIVE:
        return "skip", suggested
    if not wrapAll and not has_declarations(lines):
        return "skip-no-decls", suggested

    ns = find_first_namespace(lines)
    if ns is None:
        return "wrap", suggested
    _, current = ns
    if current == project_ns or current.startswith(project_ns + "."):
        return "ok", suggested
    return "rewrite-first-namespace", suggested

def apply_rewrite(file: Path, src_root: Path, project_ns: str) -> str:
    text = file.read_text(encoding="utf-8", errors="ignore")
    lines = text.splitlines()
    suggested = path_to_namespace(src_root, file, project_ns)

    ns = find_first_namespace(lines)

    if ns is None:
        idx = insertion_index_after_header(lines)
        new_lines = []
        new_lines.extend(lines[:idx])
        if idx > 0 and (len(new_lines) == 0 or new_lines[-1].strip() != ""):
            new_lines.append("")
        new_lines.append(f"namespace {suggested}")
        new_lines.append("")
        new_lines.extend(lines[idx:])
        if len(new_lines) > 0 and new_lines[-1].strip() != "":
            new_lines.append("")
        new_lines.append(f"end {suggested.split('.')[-1]}")
        out = "\n".join(new_lines) + "\n"
        file.write_text(out, encoding="utf-8")
        return f"wrapped with namespace {suggested}"

    i, current = ns
    # Replace first namespace only
    lines[i] = re.sub(
        r"^(\s*)namespace\s+[A-Za-z0-9_.']+\s*$",
        lambda m: f"{m.group(1)}namespace {suggested}",
        lines[i],
    )
    out = "\n".join(lines) + ("\n" if not text.endswith("\n") else "")
    file.write_text(out, encoding="utf-8")
    return f"rewrote first namespace {current} -> {suggested}"

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src-root", default="InfoGeometry")
    ap.add_argument("--project-ns", default="InfoGeometry")
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--only", default="", help="Only files whose path contains this substring")
    ap.add_argument("--wrap-all", action="store_true", help="Wrap files even if they contain no declarations (e.g. tests/headers)")
    args = ap.parse_args()

    src_root = Path(args.src_root)
    if not src_root.exists():
        alt = Path("lean") / args.src_root
        if alt.exists():
            src_root = alt
        else:
            raise SystemExit(f"src-root not found: {args.src_root}")

    rows: list[tuple[str, Path, str]] = []
    for f in sorted(src_root.rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        rels = str(f).replace("\\", "/")
        if args.only and args.only not in rels:
            continue
        status, suggested = classify(f, src_root, args.project_ns, args.wrap_all)
        rows.append((status, f, suggested))

    # Report first
    counts = {}
    for st, _, _ in rows:
        counts[st] = counts.get(st, 0) + 1

    print("[bulk_namespace_rewrite] summary")
    for k in sorted(counts):
        print(f"  {k:24s} {counts[k]}")

    print("\n[bulk_namespace_rewrite] planned changes")
    for st, f, suggested in rows:
        if st in {"wrap", "rewrite-first-namespace"}:
            print(f"  {st:22s} {f}  ->  {suggested}")

    if not args.apply:
        print("\n[dry-run] No files changed. Re-run with --apply to modify files.")
        return 0

    print("\n[apply] writing changes...")
    for st, f, _ in rows:
        if st in {"wrap", "rewrite-first-namespace"}:
            msg = apply_rewrite(f, src_root, args.project_ns)
            print(f"  {f}: {msg}")

    print("[apply] done")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
