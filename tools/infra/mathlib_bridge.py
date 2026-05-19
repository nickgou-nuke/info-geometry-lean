#!/usr/bin/env python3
from __future__ import annotations

"""Index the vendored Mathlib checkout for local GraphRAG/external search.

Mathlib is proof authority for Lean, but in the GraphRAG mirror layer it is
also a retrieval corpus. This bridge turns the vendored checkout under
``.lake/packages/mathlib`` into the two files expected by the unified
external-corpus search stack:

- ``index.json``
- ``keyword_index.json``

The output is written to ``external_refs/mathlib`` by default so the unified
explorer discovers it automatically alongside the other mirrored corpora.
"""

import argparse
import json
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from tools.infra.leansearch_local import tokenize

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SOURCE = ROOT / ".lake" / "packages" / "mathlib"
DEFAULT_OUTPUT_DIR = ROOT / "external_refs" / "mathlib"
DECL_RE = re.compile(
    r"^\s*(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive|example)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
MODULE_DIRS = ("Mathlib", "MathlibTest", "docs")


def load_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="ignore")


def extract_status(source_root: Path) -> dict[str, Any]:
    payload: dict[str, Any] = {"source": str(source_root)}
    lean_toolchain = source_root / "lean-toolchain"
    lakefile = source_root / "lakefile.lean"
    manifest = source_root / "lake-manifest.json"
    if lean_toolchain.exists():
        payload["lean_toolchain"] = load_text(lean_toolchain).strip()
    if lakefile.exists():
        payload["lakefile"] = True
    if manifest.exists():
        payload["lake_manifest"] = True
    return payload


def should_index(path: Path, source_root: Path) -> bool:
    try:
        rel = path.relative_to(source_root)
    except ValueError:
        return False
    if path.suffix != ".lean":
        return False
    return bool(rel.parts) and rel.parts[0] in MODULE_DIRS


def module_from_path(path: Path, source_root: Path) -> str:
    rel = path.relative_to(source_root)
    return ".".join(rel.with_suffix("").parts)


def extract_declarations(path: Path, source_root: Path) -> list[dict[str, Any]]:
    text = load_text(path)
    decls: list[dict[str, Any]] = []
    for idx, line in enumerate(text.splitlines(), start=1):
        m = DECL_RE.match(line)
        if not m:
            continue
        kind = m.group("kind") or "declaration"
        name = m.group("name") or ""
        if not name:
            continue
        stmt = line.strip()
        decls.append(
            {
                "source": "Lean/mathlib",
                "name": name,
                "decl": name,
                "kind": kind,
                "module": module_from_path(path, source_root),
                "file": str(path.relative_to(source_root)),
                "line": idx,
                "doc": stmt,
                "type": stmt,
                "snippet": stmt,
                "context_only": True,
                "retrieval_only": True,
                "source_path": str(path),
            }
        )
    return decls


def build_index(source_root: Path) -> dict[str, Any]:
    lean_files = sorted(path for path in source_root.rglob("*.lean") if should_index(path, source_root))
    declarations: list[dict[str, Any]] = []
    for path in lean_files:
        declarations.extend(extract_declarations(path, source_root))
    return {
        "schema": "info_geometry.external_mathlib.index.v1",
        "source": str(source_root),
        "status": extract_status(source_root),
        "files": len(lean_files),
        "declarations": declarations,
    }


def build_keyword_index(index: dict[str, Any]) -> dict[str, Any]:
    term_docs: dict[str, Counter[str]] = defaultdict(Counter)
    for decl in index.get("declarations", []):
        if not isinstance(decl, dict):
            continue
        name = str(decl.get("name") or "")
        file_path = str(decl.get("file") or "")
        module = str(decl.get("module") or "")
        kind = str(decl.get("kind") or "")
        line = decl.get("line")
        text = " ".join([name, file_path, module, kind, str(line or ""), str(decl.get("doc") or "")])
        for term in tokenize(text):
            term_docs[term][file_path] += 1

    term_index = []
    for term, counts in sorted(term_docs.items()):
        term_index.append(
            {
                "term": term,
                "count": int(sum(counts.values())),
                "files": [
                    {"file": file_path, "count": count}
                    for file_path, count in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
                ],
            }
        )
    return {
        "schema": "info_geometry.external_mathlib.keyword_index.v1",
        "source": index.get("source", ""),
        "status": index.get("status", {}),
        "termIndex": term_index,
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")


def build_bridge(*, source_root: Path = DEFAULT_SOURCE, output_dir: Path = DEFAULT_OUTPUT_DIR) -> dict[str, Any]:
    index = build_index(source_root)
    keyword_index = build_keyword_index(index)
    output_dir.mkdir(parents=True, exist_ok=True)
    write_json(output_dir / "index.json", index)
    write_json(output_dir / "keyword_index.json", keyword_index)
    summary = {
        "schema": "info_geometry.external_mathlib.bridge.summary.v1",
        "source": str(source_root),
        "output_dir": str(output_dir),
        "files": index.get("files", 0),
        "declarations": len(index.get("declarations", [])),
        "terms": len(keyword_index.get("termIndex", [])),
        "status": index.get("status", {}),
    }
    write_json(output_dir / "bridge_summary.json", summary)
    return summary


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    ap.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    summary = build_bridge(source_root=args.source, output_dir=args.output_dir)
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
