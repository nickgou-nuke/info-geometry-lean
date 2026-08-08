#!/usr/bin/env python3
"""Extract a lightweight AST-style dependency graph from Lean files (excluding vendored deps)."""

from __future__ import annotations

import json
import os
import re
from typing import Dict, List, Optional, Tuple

ROOT = "/home/goutev/auto"
EXCLUDE_DIRS = {
    ".git",
    ".venv",
    "external",
    "node_modules",
    ".lake",
    "_target",
    ".obsidian",
    ".pytest_cache",
    "venv",
    "dist",
    "build",
}
OUT_PATH = "/home/goutev/auto/all_lean_ast_graph.json"

DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(theorem|lemma|def|instance|axiom|class|structure|abbrev|inductive|example|def)\s+([a-zA-Z_][a-zA-Z0-9_]*)",
    re.MULTILINE,
)
TOKEN_RE = re.compile(r"[a-zA-Z_][a-zA-Z0-9_]*")


def class_kind(kind: str) -> str:
    return {
        "theorem": "Theorem",
        "lemma": "Lemma",
        "def": "Definition",
        "instance": "Instance",
        "axiom": "Axiom",
        "class": "Class",
        "structure": "Structure",
        "abbrev": "Definition",
        "inductive": "Inductive",
        "example": "Example",
    }.get(kind, "Declaration")


def should_skip_dir(dirname: str) -> bool:
    return dirname in EXCLUDE_DIRS or dirname.startswith(".")


def collect_lean_files(root: str) -> List[str]:
    paths: List[str] = []
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if not should_skip_dir(d)]
        for fn in files:
            if fn.endswith(".lean"):
                paths.append(os.path.join(base, fn))
    return sorted(paths)


def iter_decl_ranges(text: str) -> List[Tuple[str, str, int, int]]:
    matches = list(DECL_RE.finditer(text))
    decls = []
    for i, m in enumerate(matches):
        kind, name = m.group(1), m.group(2)
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        decls.append((kind, name, start, end))
    return decls


def declaration_node_id(file_rel: str, name: str) -> str:
    return f"{file_rel}::{name}"


def main() -> None:
    lean_files = collect_lean_files(ROOT)

    decls = []
    name_to_ids: Dict[str, List[str]] = {}

    for path in lean_files:
        rel = os.path.relpath(path, ROOT)
        with open(path, "r", encoding="utf-8", errors="ignore") as f:
            text = f.read()

        for kind, name, start, end in iter_decl_ranges(text):
            node_id = declaration_node_id(rel, name)
            node = {
                "id": node_id,
                "name": name,
                "kind": class_kind(kind),
                "file": rel,
                "span": [start, end],
            }
            decls.append((path, rel, node, text[start:end]))
            name_to_ids.setdefault(name, []).append(node_id)

    edges: List[Dict[str, str]] = []
    seen_edges = set()

    for path, rel, node, body in decls:
        tokens = set(TOKEN_RE.findall(body))
        source = node["id"]

        # Prefer same-file declarations, fallback to other files for any same-name hits
        for tok in tokens:
            if tok not in name_to_ids:
                continue
            for target_id in name_to_ids[tok]:
                if target_id == source:
                    continue
                # prioritize same file target when both same-file and foreign exist
                edge = (source, target_id)
                if edge not in seen_edges:
                    seen_edges.add(edge)
                    edges.append({"source": source, "target": target_id, "type": "references"})

    nodes = [n for _, _, n, _ in decls]
    payload = {
        "nodes": nodes,
        "edges": edges,
        "meta": {
            "input_files": len(lean_files),
            "nodes": len(nodes),
            "edges": len(edges),
            "path": ROOT,
        },
    }

    with open(OUT_PATH, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)

    print(f"Lean files scanned: {len(lean_files)}")
    print(f"Nodes: {len(nodes)}")
    print(f"Edges: {len(edges)}")
    print(f"Saved AST graph to: {OUT_PATH}")


if __name__ == "__main__":
    main()
