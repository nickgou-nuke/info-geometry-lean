#!/usr/bin/env python3
from __future__ import annotations

"""Index the FrogBird theorem mirror for local GraphRAG/external search.

The FrogBird mirror is a retrieval corpus, not proof authority. This bridge
transforms ``external/FrogBird/theorem_index.json`` into the two files expected by
the unified external-corpus search stack:

- ``index.json``
- ``keyword_index.json``

The output is written to ``external_refs/FrogBird`` by default so the unified
explorer discovers it automatically alongside the other mirrored corpora.
"""

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from tools.infra.leansearch_local import tokenize

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SOURCE = ROOT / "external" / "FrogBird" / "theorem_index.json"
DEFAULT_OUTPUT_DIR = ROOT / "external_refs" / "FrogBird"


def load_source(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"expected JSON object in {path}")
    return payload


def module_from_file(path: str) -> str:
    p = Path(path)
    parts = p.with_suffix("").parts
    if len(parts) >= 1:
        return ".".join(parts)
    return path.replace("/", ".").removesuffix(".lean")


def build_index(source: dict[str, Any], *, source_path: Path) -> dict[str, Any]:
    decls = source.get("declarations", [])
    declarations: list[dict[str, Any]] = []
    for row in decls:
        if not isinstance(row, dict):
            continue
        name = str(row.get("decl") or "").strip()
        file_path = str(row.get("file") or "").strip()
        stmt = str(row.get("stmt") or "").strip()
        line = row.get("line")
        if not name or not file_path:
            continue
        declarations.append(
            {
                "source": "external/FrogBird",
                "name": name,
                "decl": name,
                "kind": "theorem" if stmt.startswith("theorem") else "def",
                "module": module_from_file(file_path),
                "file": file_path,
                "line": line,
                "doc": stmt,
                "type": stmt,
                "snippet": stmt,
                "context_only": True,
                "retrieval_only": True,
                "source_path": str(source_path),
            }
        )
    return {
        "schema": "info_geometry.external_frogbird.index.v1",
        "source": "external/FrogBird/theorem_index.json",
        "commit": source.get("commit", ""),
        "stats": source.get("stats", {}),
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
        text = " ".join([name, file_path, module, kind, str(line or "") , str(decl.get("doc") or "")])
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
        "schema": "info_geometry.external_frogbird.keyword_index.v1",
        "source": "external/FrogBird/theorem_index.json",
        "commit": index.get("commit", ""),
        "termIndex": term_index,
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")


def build_bridge(*, source_path: Path = DEFAULT_SOURCE, output_dir: Path = DEFAULT_OUTPUT_DIR) -> dict[str, Any]:
    source = load_source(source_path)
    index = build_index(source, source_path=source_path)
    keyword_index = build_keyword_index(index)
    output_dir.mkdir(parents=True, exist_ok=True)
    write_json(output_dir / "index.json", index)
    write_json(output_dir / "keyword_index.json", keyword_index)
    summary = {
        "schema": "info_geometry.external_frogbird.bridge.summary.v1",
        "source": str(source_path),
        "output_dir": str(output_dir),
        "commit": index.get("commit", ""),
        "stats": index.get("stats", {}),
        "declarations": len(index.get("declarations", [])),
        "terms": len(keyword_index.get("termIndex", [])),
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
    summary = build_bridge(source_path=args.source, output_dir=args.output_dir)
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
