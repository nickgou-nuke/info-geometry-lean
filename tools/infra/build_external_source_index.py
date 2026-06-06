#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path

TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']{1,}")
SKIP_DIRS = {
    ".git",
    ".lake",
    ".mypy_cache",
    ".pytest_cache",
    ".tox",
    "__pycache__",
    "build",
    "dist",
    "node_modules",
    "target",
    "venv",
}
DEFAULT_EXTENSIONS = {
    ".lean",
    ".md",
    ".py",
    ".pxd",
    ".pxi",
    ".pyx",
    ".rst",
    ".sage",
    ".tex",
}

DECL_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("theorem", re.compile(r"^\s*theorem\s+([A-Za-z0-9_'.]+)")),
    ("lemma", re.compile(r"^\s*lemma\s+([A-Za-z0-9_'.]+)")),
    ("def", re.compile(r"^\s*def\s+([A-Za-z0-9_'.]+)")),
    ("structure", re.compile(r"^\s*structure\s+([A-Za-z0-9_'.]+)")),
    ("inductive", re.compile(r"^\s*inductive\s+([A-Za-z0-9_'.]+)")),
    ("class", re.compile(r"^\s*class\s+([A-Za-z0-9_'.]+)")),
    ("abbrev", re.compile(r"^\s*abbrev\s+([A-Za-z0-9_'.]+)")),
    ("instance", re.compile(r"^\s*instance\s+([A-Za-z0-9_'.]+)")),
    ("py_class", re.compile(r"^\s*class\s+([A-Za-z_][A-Za-z0-9_]*)\b")),
    ("py_def", re.compile(r"^\s*(?:async\s+)?def\s+([A-Za-z_][A-Za-z0-9_]*)\b")),
    ("cy_def", re.compile(r"^\s*(?:cpdef|cdef)\s+(?:[A-Za-z_][A-Za-z0-9_*\s]*\s+)?([A-Za-z_][A-Za-z0-9_]*)\b")),
]


def tokenize(text: str) -> list[str]:
    return [t.lower() for t in TOKEN_RE.findall(text)]


def should_skip(path: Path) -> bool:
    return any(part in SKIP_DIRS for part in path.parts)


def iter_source_files(root: Path, extensions: set[str], max_bytes: int) -> list[Path]:
    out: list[Path] = []
    for p in root.rglob("*"):
        if should_skip(p.relative_to(root)):
            continue
        if not p.is_file() or p.suffix.lower() not in extensions:
            continue
        try:
            if p.stat().st_size > max_bytes:
                continue
        except OSError:
            continue
        out.append(p)
    return sorted(out)


def module_name_for(root: Path, p: Path) -> str:
    rel = p.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def window(lines: list[str], start: int, width: int) -> str:
    return "\n".join(lines[start : min(len(lines), start + width)]).strip()


def slug(text: str) -> str:
    words = tokenize(text)
    return "_".join(words[:12]) or "section"


def parse_declarations(text: str, file_suffix: str) -> list[tuple[str, str, int, str]]:
    lines = text.splitlines()
    out: list[tuple[str, str, int, str]] = []
    for i, line in enumerate(lines):
        for kind, rx in DECL_PATTERNS:
            m = rx.match(line)
            if m:
                out.append((kind, m.group(1), i + 1, window(lines, i, 24)))
                break

        stripped = line.strip()
        if file_suffix in {".md", ".rst"}:
            if stripped.startswith("#"):
                out.append(("section", slug(stripped), i + 1, window(lines, i, 18)))
            elif i + 1 < len(lines) and set(lines[i + 1].strip()) in ({"="}, {"-"}, {"~"}):
                out.append(("section", slug(stripped), i + 1, window(lines, i, 18)))
        elif file_suffix == ".tex" and re.match(r"\\(section|subsection|subsubsection|begin\{theorem\}|begin\{lemma\})", stripped):
            out.append(("tex_section", slug(stripped), i + 1, window(lines, i, 18)))
    return out


def build_index(root: Path, out_dir: Path, extensions: set[str], max_bytes: int) -> dict[str, object]:
    files = iter_source_files(root, extensions, max_bytes)
    declarations: list[dict[str, object]] = []
    kw = Counter()

    for f in files:
        try:
            text = f.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue

        rel = str(f)
        module = module_name_for(root, f)
        file_summary = window(text.splitlines(), 0, 40)
        declarations.append(
            {
                "name": module,
                "kind": "file",
                "module": module,
                "file": rel,
                "line": 1,
                "doc": file_summary,
                "type": "",
            }
        )
        kw.update(tokenize(module))
        kw.update(tokenize(file_summary))

        for kind, name, line, doc in parse_declarations(text, f.suffix.lower()):
            row = {
                "name": name,
                "kind": kind,
                "module": module,
                "file": rel,
                "line": line,
                "doc": doc,
                "type": "",
            }
            declarations.append(row)
            kw.update(tokenize(name))
            kw.update(tokenize(module))
            kw.update(tokenize(doc))

    out_dir.mkdir(parents=True, exist_ok=True)
    index_payload = {
        "schema": "external.source.index.v1",
        "root": str(root),
        "sourceFiles": len(files),
        "declarations": declarations,
    }
    keyword_payload = {
        "schema": "external.source.keyword_index.v1",
        "root": str(root),
        "termIndex": [{"term": t, "count": c} for t, c in kw.most_common()],
    }
    summary = {
        "root": str(root),
        "out": str(out_dir),
        "source_files": len(files),
        "declarations": len(declarations),
        "terms": len(keyword_payload["termIndex"]),
    }

    (out_dir / "index.json").write_text(json.dumps(index_payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (out_dir / "keyword_index.json").write_text(json.dumps(keyword_payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (out_dir / "bridge_summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build query_external_corpus-compatible indexes for non-Lean external source mirrors."
    )
    parser.add_argument("roots", nargs="+", help="External source roots to index.")
    parser.add_argument("--out-base", default="artifacts/external_source_index")
    parser.add_argument("--name", action="append", help="Optional output name for each root, in order.")
    parser.add_argument("--extensions", help="Comma-separated extension allowlist. Defaults to common source/docs.")
    parser.add_argument("--max-bytes", type=int, default=2_000_000)
    args = parser.parse_args()

    roots = [Path(r).resolve() for r in args.roots]
    names = args.name or []
    if names and len(names) != len(roots):
        parser.error("--name must be supplied once per root when used")

    extensions = DEFAULT_EXTENSIONS
    if args.extensions:
        extensions = {e if e.startswith(".") else f".{e}" for e in args.extensions.split(",") if e}

    out_base = Path(args.out_base)
    results = []
    for idx, root in enumerate(roots):
        if not root.exists() or not root.is_dir():
            continue
        out_name = names[idx] if names else root.name
        results.append(build_index(root, out_base / out_name, extensions, args.max_bytes))

    print(json.dumps({"updated": results, "count": len(results)}, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
