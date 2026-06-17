#!/usr/bin/env python3
"""
Lightweight AST-style declaration and reference graph extraction from Lean files.

Parses every `.lean` file under a root directory, extracts declarations
(theorem/lemma/def/structure/inductive/etc.) and their token-level references
to other declarations. Produces a JSON node-edge graph suitable for ArangoDB
ingest, NetworkX DAG analysis, or causal-cone extraction.

Usage:
  python3 tools/leantrail/ast_extract.py                      \
    --root lean/                                                \
    --out artifacts/leantrail/lean_ast_graph.json               \
    --exclude .lake,.git,lean_sandbox,external_refs             \
    [--jsonl]  # write nodes.jsonl + edges.jsonl for ArangoDB
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

REPO_ROOT = Path(__file__).resolve().parents[2]

# ---------------------------------------------------------------------------
# Regex patterns
# ---------------------------------------------------------------------------

DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?"
    r"(theorem|lemma|def|instance|axiom|class|structure|abbrev|inductive|example)\s+"
    r"([a-zA-Z_]['\w]*)",
    re.MULTILINE,
)

IMPORT_RE = re.compile(
    r"^\s*import\s+([\w.]+(?:\s+[\w.]+)*)",
    re.MULTILINE,
)

NAMESPACE_RE = re.compile(
    r"^\s*namespace\s+([\w.]+)",
    re.MULTILINE,
)

TOKEN_RE = re.compile(r"[a-zA-Z_]['\w]*")

# Tokens that are never declaration references
IGNORE_TOKENS: Set[str] = {
    "by", "have", "let", "fun", "intro", "apply", "exact", "refine", "rw",
    "simp", "calc", "omega", "ring", "abel", "nlinarith", "ext", "cases",
    "rcases", "constructor", "assumption", "rfl", "trivial", "sorry",
    "match", "if", "then", "else", "forall", "exists", "λ", "from",
    "using", "with", "in", "at", "do", "return", "set_option",
    "open", "import", "namespace", "end", "section", "variable",
    "deriving", "where", "extends", "mutual", "partial", "nonrec",
    "hiding", "renaming", "export", "attribute", "macro", "elab",
    "syntax", "macro_rules", "initialize", "builtin_initialize",
    "unsafe", "noncomputable", "scoped", "local", "private", "protected",
    "instance", "class", "structure", "inductive", "abbrev", "theorem",
    "lemma", "def", "example", "axiom", "opaque", "coe", "notation",
    "infix", "infixl", "infixr", "postfix", "prefix", "declare_syntax_cat",
    "Type", "Prop", "Type_", "Type u", "Type v",
}

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

DECL_KIND_MAP: Dict[str, str] = {
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
}

DEFAULT_EXCLUDE: Set[str] = {
    ".git", ".lake", ".venv", "venv", "__pycache__",
    "node_modules", "dist", "build", ".obsidian",
    "lean_sandbox", "external_refs",
}


def classify_kind(kind: str) -> str:
    return DECL_KIND_MAP.get(kind, "Declaration")


def should_skip(dirname: str, exclude: Set[str]) -> bool:
    return dirname in exclude or dirname.startswith(".")


def collect_lean_files(root: Path, exclude: Set[str]) -> List[Path]:
    paths: List[Path] = []
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if not should_skip(d, exclude)]
        for fn in files:
            if fn.endswith(".lean"):
                paths.append(Path(base) / fn)
    return sorted(paths)


def iter_decl_ranges(text: str) -> List[Tuple[str, str, int, int, int]]:
    """Return (kind, name, line, start_byte, end_byte) for each declaration."""
    matches = list(DECL_RE.finditer(text))
    decls = []
    for i, m in enumerate(matches):
        kind, name = m.group(1), m.group(2)
        line = text[:m.start()].count("\n") + 1
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        decls.append((kind, name, line, start, end))
    return decls


def extract_imports(text: str) -> List[str]:
    return [m.group(1).strip() for m in IMPORT_RE.finditer(text)]


def extract_namespace(text: str) -> Optional[str]:
    m = NAMESPACE_RE.search(text)
    return m.group(1) if m else None


def module_name_from_rel(file_rel: str) -> str:
    """Convert `InfoGeometry/Foo.lean` to `InfoGeometry.Foo`."""
    no_suffix = str(Path(file_rel).with_suffix(""))
    return no_suffix.replace(os.sep, ".").replace("/", ".")


def qualified_decl_name(namespace: Optional[str], name: str) -> str:
    if "." in name or not namespace:
        return name
    return f"{namespace}.{name}"


def arango_key(raw: str) -> str:
    """ASCII-safe deterministic key for Arango documents."""
    safe = "".join(ch if (ch.isascii() and (ch.isalnum() or ch in "_:-")) else "_" for ch in raw)
    safe = safe.strip("_")[:180]
    digest = hashlib.sha1(raw.encode("utf-8")).hexdigest()[:12]
    return f"{safe}_{digest}" if safe else digest


def node_id(file_rel: str, name: str, line: int) -> str:
    return f"{file_rel}::{name}:L{line}"


def decl_key(file_rel: str, name: str) -> str:
    return f"{file_rel}::{name}"


# ---------------------------------------------------------------------------
# Main extraction
# ---------------------------------------------------------------------------


def extract_graph(
    root: Path,
    exclude: Optional[Set[str]] = None,
    *,
    include_tokens: bool = True,
    include_imports: bool = True,
    max_token_fanout: int = 4,
) -> Dict[str, Any]:
    """Extract a full AST dependency graph from all .lean files under `root`.

    Returns a dict with ``nodes``, ``edges``, and ``meta``.
    """
    exclude = exclude or DEFAULT_EXCLUDE
    lean_files = collect_lean_files(root, exclude)

    decls: List[Tuple[Path, str, Dict[str, Any], str]] = []
    name_to_ids: Dict[str, List[str]] = defaultdict(list)
    imports_by_file: Dict[str, List[str]] = {}

    for path in lean_files:
        rel = str(path.relative_to(root))
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue

        imports = extract_imports(text)
        namespace = extract_namespace(text)
        try:
            module_rel = str(path.relative_to(REPO_ROOT / "lean"))
        except ValueError:
            module_rel = rel
        module = module_name_from_rel(module_rel)
        if include_imports:
            imports_by_file[rel] = imports

        for kind, name, line, start, end in iter_decl_ranges(text):
            qname = qualified_decl_name(namespace, name)
            nid = node_id(rel, qname, line)
            key = arango_key(nid)
            node = {
                "_key": key,
                "id": nid,
                "decl_key": decl_key(rel, qname),
                "name": qname,
                "shortName": name,
                "kind": classify_kind(kind),
                "file": rel,
                "module": module,
                "namespace": namespace,
                "line": line,
                "span": [start, end],
            }
            decls.append((path, rel, node, text[start:end]))
            name_to_ids[name].append(nid)
            name_to_ids[qname].append(nid)

    # Build edges
    edges: List[Dict[str, str]] = []
    seen_edges: Set[Tuple[str, str]] = set()

    for _path, rel, node, body in decls:
        if not include_tokens:
            continue
        tokens = set(TOKEN_RE.findall(body)) - IGNORE_TOKENS
        source = node["id"]
        for tok in tokens:
            if tok not in name_to_ids:
                continue
            target_ids = name_to_ids[tok]
            if max_token_fanout > 0 and len(target_ids) > max_token_fanout:
                continue
            for target_id in target_ids:
                if target_id == source:
                    continue
                edge_key = (source, target_id)
                if edge_key not in seen_edges:
                    seen_edges.add(edge_key)
                    source_key = arango_key(source)
                    target_key = arango_key(target_id)
                    edges.append({
                        "_key": arango_key(f"{source}->{target_id}"),
                        "_from": f"leantrail_ast_nodes/{source_key}",
                        "_to": f"leantrail_ast_nodes/{target_key}",
                        "source": source,
                        "target": target_id,
                        "kind": "depends_value",
                        "type": "references",
                        "evidence_ref": f"{node['file']}:{node['line']}",
                    })

    nodes = [n for _, _, n, _ in decls]

    return {
        "nodes": nodes,
        "edges": edges,
        "imports": imports_by_file if include_imports else {},
        "meta": {
            "input_files": len(lean_files),
            "nodes": len(nodes),
            "edges": len(edges),
            "root": str(root),
        },
    }


def save_graph(
    graph: Dict[str, Any],
    out_path: Path,
    *,
    jsonl: bool = False,
    pretty: bool = False,
) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    json_text = (
        json.dumps(graph, indent=2, ensure_ascii=True)
        if pretty
        else json.dumps(graph, ensure_ascii=True, separators=(",", ":"))
    )
    out_path.write_text(
        json_text + "\n",
        encoding="utf-8",
    )
    print(f"Graph: {out_path}")

    if jsonl:
        nodes_path = out_path.parent / (out_path.stem + "_nodes.jsonl")
        edges_path = out_path.parent / (out_path.stem + "_edges.jsonl")
        with nodes_path.open("w", encoding="utf-8") as f:
            for n in graph["nodes"]:
                f.write(json.dumps(n, ensure_ascii=True) + "\n")
        with edges_path.open("w", encoding="utf-8") as f:
            for e in graph["edges"]:
                f.write(json.dumps(e, ensure_ascii=True) + "\n")
        print(f"Nodes: {nodes_path} ({len(graph['nodes'])} records)")
        print(f"Edges: {edges_path} ({len(graph['edges'])} records)")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Extract a Lean AST declaration-reference graph."
    )
    parser.add_argument(
        "--root", default="lean",
        help="Root directory containing .lean files (default: lean/)",
    )
    parser.add_argument(
        "--out", default="artifacts/leantrail/lean_ast_graph.json",
        help="Output JSON graph path",
    )
    parser.add_argument(
        "--exclude", default="",
        help="Comma-separated directory names to exclude",
    )
    parser.add_argument(
        "--jsonl", action="store_true",
        help="Write nodes.jsonl + edges.jsonl for ArangoDB ingest",
    )
    parser.add_argument(
        "--no-tokens", action="store_true",
        help="Skip token-level reference edges (faster, smaller output)",
    )
    parser.add_argument(
        "--no-imports", action="store_true",
        help="Skip import extraction",
    )
    parser.add_argument(
        "--max-token-fanout", type=int, default=4,
        help="Skip token references that match more than this many declarations; 0 disables the cap",
    )
    parser.add_argument(
        "--pretty", action="store_true",
        help="Pretty-print the JSON graph; default is compact JSON for large repos",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    root = Path(args.root).resolve()
    exclude = DEFAULT_EXCLUDE.copy()
    if args.exclude:
        exclude.update(d.strip() for d in args.exclude.split(",") if d.strip())

    print(f"Scanning: {root}")
    print(f"Excluding: {sorted(exclude)}")

    graph = extract_graph(
        root,
        exclude=exclude,
        include_tokens=not args.no_tokens,
        include_imports=not args.no_imports,
        max_token_fanout=args.max_token_fanout,
    )

    out_path = Path(args.out).resolve()
    save_graph(graph, out_path, jsonl=args.jsonl, pretty=args.pretty)

    meta = graph["meta"]
    print(f"Files: {meta['input_files']}  Nodes: {meta['nodes']}  Edges: {meta['edges']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
