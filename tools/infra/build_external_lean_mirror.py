#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path

TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']{1,}")
SKIP_SEGMENTS = ("/.lake/", "/build/", "/.git/")


def tokenize(text: str) -> list[str]:
    return [t.lower() for t in TOKEN_RE.findall(text)]


def lean_files(root: Path) -> list[Path]:
    out: list[Path] = []
    for p in root.rglob("*.lean"):
        s = str(p)
        if any(seg in s for seg in SKIP_SEGMENTS):
            continue
        out.append(p)
    return sorted(out)


def module_name_for(root: Path, p: Path) -> str:
    rel = p.relative_to(root)
    no_ext = rel.with_suffix("")
    return ".".join(no_ext.parts)


def parse_decls(text: str) -> list[tuple[str, str, int]]:
    decls: list[tuple[str, str, int]] = []
    patterns = [
        ("theorem", re.compile(r"^\s*theorem\s+([A-Za-z0-9_'.]+)")),
        ("lemma", re.compile(r"^\s*lemma\s+([A-Za-z0-9_'.]+)")),
        ("def", re.compile(r"^\s*def\s+([A-Za-z0-9_'.]+)")),
        ("structure", re.compile(r"^\s*structure\s+([A-Za-z0-9_'.]+)")),
        ("inductive", re.compile(r"^\s*inductive\s+([A-Za-z0-9_'.]+)")),
        ("class", re.compile(r"^\s*class\s+([A-Za-z0-9_'.]+)")),
        ("abbrev", re.compile(r"^\s*abbrev\s+([A-Za-z0-9_'.]+)")),
        ("instance", re.compile(r"^\s*instance\s+([A-Za-z0-9_'.]+)")),
    ]
    for i, line in enumerate(text.splitlines(), start=1):
        for kind, rx in patterns:
            m = rx.match(line)
            if m:
                decls.append((kind, m.group(1), i))
                break
    return decls


def build_mirror(root: Path) -> dict:
    files = lean_files(root)
    declarations = []
    kw = Counter()

    for f in files:
        rel = str(f)
        try:
            text = f.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        module = module_name_for(root, f)
        for kind, name, line in parse_decls(text):
            row = {
                "name": name,
                "kind": kind,
                "module": module,
                "file": rel,
                "line": line,
                "doc": "",
                "type": "",
            }
            declarations.append(row)
            kw.update(tokenize(name))
            kw.update(tokenize(module))

    keyword_rows = [{"term": t, "count": c} for t, c in kw.most_common()]
    index_payload = {
        "schema": "external.mirror.index.v1",
        "root": str(root),
        "declarations": declarations,
    }
    keyword_payload = {
        "schema": "external.mirror.keyword_index.v1",
        "root": str(root),
        "termIndex": keyword_rows,
    }
    (root / "index.json").write_text(json.dumps(index_payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (root / "keyword_index.json").write_text(json.dumps(keyword_payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (root / "bridge_summary.json").write_text(
        json.dumps(
            {
                "root": str(root),
                "lean_files": len(files),
                "declarations": len(declarations),
                "terms": len(keyword_rows),
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n",
        encoding="utf-8",
    )
    return {
        "root": str(root),
        "lean_files": len(files),
        "declarations": len(declarations),
        "terms": len(keyword_rows),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Build lightweight external Lean mirror indexes for GraphRAG.")
    ap.add_argument("roots", nargs="+", help="One or more directory roots to scan (e.g. external_refs external)")
    ap.add_argument("--min-lean-files", type=int, default=1)
    args = ap.parse_args()

    results = []
    for base in [Path(r) for r in args.roots]:
        if not base.exists() or not base.is_dir():
            continue
        for child in sorted(p for p in base.iterdir() if p.is_dir()):
            n = len(lean_files(child))
            if n < args.min_lean_files:
                continue
            results.append(build_mirror(child))

    print(json.dumps({"updated": results, "count": len(results)}, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
