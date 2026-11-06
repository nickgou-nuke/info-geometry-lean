#!/usr/bin/env python3
"""
Export Lean 4 declaration graph to Neo4j-compatible Cypher.

Parses Lean 4 source files to extract declarations (theorem, def, lemma,
instance, class, structure, axiom) and their dependencies, then generates
Cypher CREATE statements for Neo4j ingestion.

Nodes: (:LeanDecl {name, kind, file, line, statement, fully_qualified_name})
Relationships: (:LeanDecl)-[:DEPENDS_ON]->(:LeanDecl), (:LeanDecl)-[:IMPORTS]->(:LeanFile)

Usage:
  python3 tools/export_lean_to_neo4j.py --output lean_graph.cypher
  python3 tools/export_lean_to_neo4j.py --files lean/InfoGeometry/OperatorAlgebra/PeirceSpine/MetriplecticCausalPlabicKreinYangianPoset.lean --output single_file.cypher
"""

import argparse
import re
import sys
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional
from dataclasses import dataclass, asdict, field
import json

REPO_ROOT = Path(__file__).resolve().parent.parent

LEAN_FILE_PATTERNS = ["**/*.lean"]

# Match declaration headers at the start of a line (allowing leading whitespace for sections)
DECL_PATTERN = re.compile(
    r'^\s*(theorem|def|lemma|instance|class|structure|axiom|primitive)\s+([\w\.]+)(?:\s*[\(:]|\s*$)',
    re.MULTILINE,
)

# Match import lines
IMPORT_PATTERN = re.compile(r'^\s*import\s+([\w\.]+)', re.MULTILINE)

# Match namespace declarations to build fully qualified names
NAMESPACE_PATTERN = re.compile(r'^\s*namespace\s+([\w\.]+)', re.MULTILINE)
END_NAMESPACE_PATTERN = re.compile(r'^\s*end\s+([\w\.]*)', re.MULTILINE)

# Match variable declarations
VARIABLE_PATTERN = re.compile(r'^\s*variable\s+\{?([\w]+)', re.MULTILINE)


@dataclass
class LeanDecl:
    name: str
    kind: str
    file: str
    line: int
    statement: str
    fully_qualified_name: str = ""
    namespace: str = ""

    @property
    def node_id(self) -> str:
        """Unique node identifier: fully_qualified_name or file:name fallback."""
        return self.fully_qualified_name or f"{self.file}:{self.name}"


@dataclass
class LeanFile:
    path: str  # relative to repo root
    imports: List[str] = field(default_factory=list)
    declarations: List[LeanDecl] = field(default_factory=list)


def parse_lean_file(file_path: Path) -> LeanFile:
    """Parse a single Lean file, extracting declarations and imports."""
    content = file_path.read_text(encoding="utf-8", errors="replace")
    rel_path = file_path.relative_to(REPO_ROOT).as_posix()

    lf = LeanFile(path=rel_path)

    # Extract imports
    for m in IMPORT_PATTERN.finditer(content):
        lf.imports.append(m.group(1))

    # Build namespace stack to construct fully qualified names
    namespace_stack: List[str] = []

    lines = content.split("\n")
    for i, line in enumerate(lines):
        # Track namespace open/close
        ns_m = NAMESPACE_PATTERN.match(line)
        if ns_m:
            namespace_stack.append(ns_m.group(1))
            continue
        end_ns_m = END_NAMESPACE_PATTERN.match(line)
        if end_ns_m and end_ns_m.group(1):
            if namespace_stack and namespace_stack[-1] == end_ns_m.group(1):
                namespace_stack.pop()
            continue
        if end_ns_m and not end_ns_m.group(1):
            if namespace_stack:
                namespace_stack.pop()
            continue

        # Match declarations
        decl_m = DECL_PATTERN.match(line)
        if decl_m:
            kind = decl_m.group(1)
            short_name = decl_m.group(2)
            ns_prefix = ".".join(namespace_stack)
            fqn = f"{ns_prefix}.{short_name}" if ns_prefix else short_name

            lf.declarations.append(
                LeanDecl(
                    name=short_name,
                    kind=kind,
                    file=rel_path,
                    line=i + 1,
                    statement=line.strip(),
                    fully_qualified_name=fqn,
                    namespace=ns_prefix,
                )
            )

    return lf


def discover_lean_files(root: Path = REPO_ROOT, patterns: Optional[List[str]] = None) -> List[Path]:
    """Discover all Lean files under the repo root."""
    if patterns is None:
        patterns = LEAN_FILE_PATTERNS
    files: Set[Path] = set()
    skip_dirs = {".lake", ".git", "__pycache__", ".changes", "node_modules", ".venv", "venv"}
    for pat in patterns:
        for f in root.glob(pat):
            if f.is_file() and not any(d in f.parts for d in skip_dirs):
                files.add(f)
    return sorted(files)


def build_dependency_edges(
    files: List[LeanFile],
    all_decls_by_fqn: Dict[str, LeanDecl],
) -> Tuple[List[dict], List[dict]]:
    """
    Build dependency edges between declarations and import edges between files.

    Returns (decl_edges, import_edges) where each edge is a dict suitable for
    Cypher generation.
    """
    decl_edges: List[dict] = []
    import_edges: List[dict] = []

    # Map short names within each file to FQNs for local dep resolution
    for lf in files:
        # Local short-name -> FQN map (for declarations in this file)
        local_short_to_fqn: Dict[str, str] = {}
        for decl in lf.declarations:
            local_short_to_fqn[decl.name] = decl.fully_qualified_name

        # For each declaration, try to resolve its dependencies.
        # We use a simple heuristic: look at the statement text for references
        # to other declaration names. This is an approximation since Lean's
        # actual dependency graph requires the elaborator, but it captures
        # most direct references.
        for decl in lf.declarations:
            stmt_words = set(re.findall(r'[\w\.]+', decl.statement))
            for word in stmt_words:
                # Try exact FQN match first
                if word in all_decls_by_fqn:
                    target = all_decls_by_fqn[word]
                    if target.node_id != decl.node_id:
                        decl_edges.append({
                            "source": decl.node_id,
                            "target": target.node_id,
                            "relation": "DEPENDS_ON",
                        })
                        continue
                # Try short name within same file
                if word in local_short_to_fqn:
                    target_fqn = local_short_to_fqn[word]
                    if target_fqn != decl.fully_qualified_name:
                        decl_edges.append({
                            "source": decl.node_id,
                            "target": target_fqn,
                            "relation": "DEPENDS_ON",
                        })

    # Import edges between files
    import_map: Dict[str, str] = {}  # import path -> file path (relative)
    for lf in files:
        import_map[lf.path] = lf.path

    for lf in files:
        for imp in lf.imports:
            # Convert dotted import to possible file paths
            candidates = [
                f"{imp}.lean",
                f"{imp.replace('.', '/')}.lean",
                imp,
                imp.replace(".", "/"),
            ]
            found = False
            for cand in candidates:
                if cand in import_map:
                    import_edges.append({
                        "source": lf.path,
                        "target": cand,
                        "relation": "IMPORTS",
                    })
                    found = True
                    break
            if not found:
                # Import not resolvable to a local file (e.g., Mathlib)
                import_edges.append({
                    "source": lf.path,
                    "target": imp,
                    "relation": "IMPORTS_EXTERNAL",
                })

    return decl_edges, import_edges


def cypher_escape(s: str) -> str:
    """Escape a string for use in a Cypher string literal."""
    return s.replace("\\", "\\\\").replace('"', '\\"')


def cypher_node(decl: LeanDecl) -> str:
    """Generate a Cypher MERGE statement for a declaration node."""
    props = {
        "name": decl.name,
        "kind": decl.kind,
        "file": decl.file,
        "line": decl.line,
        "fully_qualified_name": decl.fully_qualified_name,
        "namespace": decl.namespace,
        "statement": decl.statement[:500],  # truncate for safety
    }
    parts = []
    for k, v in props.items():
        if isinstance(v, int):
            parts.append(f'{k}: {v}')
        else:
            parts.append(f'{k}: "{cypher_escape(str(v))}"')
    prop_str = ", ".join(parts)
    fqn = decl.fully_qualified_name or decl.name
    return (
        'MERGE (n:LeanDecl {fully_qualified_name: "'
        + cypher_escape(fqn)
        + '"}) ON CREATE SET '
        + prop_str
        + " RETURN n"
    )


def cypher_file_node(lf: LeanFile) -> str:
    """Generate a Cypher MERGE statement for a file node."""
    props = {
        "path": lf.path,
        "declaration_count": len(lf.declarations),
        "import_count": len(lf.imports),
    }
    parts = []
    for k, v in props.items():
        if isinstance(v, int):
            parts.append(f"{k}: {v}")
        else:
            parts.append(f'{k}: "{cypher_escape(str(v))}"')
    prop_str = ", ".join(parts)
    return (
        'MERGE (f:LeanFile {path: "'
        + cypher_escape(lf.path)
        + '"}) ON CREATE SET '
        + prop_str
        + " RETURN f"
    )


def cypher_decl_edge(edge: dict) -> str:
    """Generate a Cypher MERGE statement for a declaration dependency edge."""
    src = cypher_escape(edge["source"])
    tgt = cypher_escape(edge["target"])
    rel = edge["relation"]
    return (
        'MATCH (s:LeanDecl {fully_qualified_name: "'
        + src
        + '"}) '
        'MATCH (t:LeanDecl {fully_qualified_name: "'
        + tgt
        + '"}) '
        'MERGE (s)-[:'
        + rel
        + "]->(t)"
    )


def cypher_file_decl_edge(file_path: str, decl: LeanDecl) -> str:
    """Generate a Cypher MERGE statement linking a file to its declarations."""
    fqn = decl.fully_qualified_name or decl.name
    return (
        'MATCH (f:LeanFile {path: "'
        + cypher_escape(file_path)
        + '"}) '
        'MATCH (d:LeanDecl {fully_qualified_name: "'
        + cypher_escape(fqn)
        + '"}) '
        "MERGE (f)-[:CONTAINS]->(d)"
    )


def cypher_import_edge(edge: dict) -> str:
    """Generate a Cypher MERGE statement for a file import edge."""
    src = cypher_escape(edge["source"])
    tgt = cypher_escape(edge["target"])
    rel = edge["relation"]
    return (
        'MATCH (s:LeanFile {path: "'
        + src
        + '"}) '
        'MERGE (t:LeanFile {path: "'
        + tgt
        + '"}) '
        'MERGE (s)-[:'
        + rel
        + "]->(t)"
    )


def export_cypher(
    files: List[LeanFile],
    decl_edges: List[dict],
    import_edges: List[dict],
    output: Path,
    include_constraints: bool = True,
    include_indexes: bool = True,
):
    """Write all Cypher statements to the output file."""
    # Build lookup: FQN -> decl
    all_decls_by_fqn: Dict[str, LeanDecl] = {}
    for lf in files:
        for decl in lf.declarations:
            key = decl.fully_qualified_name or f"{lf.path}:{decl.name}"
            all_decls_by_fqn[key] = decl

    lines: List[str] = []
    lines.append("// ============================================================")
    lines.append("// Lean 4 Declaration Graph - Neo4j Cypher Export")
    lines.append(f"// Generated by tools/export_lean_to_neo4j.py")
    lines.append(f"// Repository: {REPO_ROOT}")
    lines.append(f"// Files: {len(files)}, Declarations: {sum(len(lf.declarations) for lf in files)}")
    lines.append("// ============================================================")
    lines.append("")

    if include_constraints:
        lines.append("// --- Constraints ---")
        lines.append(
            'CREATE CONSTRAINT lean_decl_fqn IF NOT EXISTS '
            'FOR (n:LeanDecl) REQUIRE n.fully_qualified_name IS UNIQUE;'
        )
        lines.append(
            'CREATE CONSTRAINT lean_file_path IF NOT EXISTS '
            'FOR (f:LeanFile) REQUIRE f.path IS UNIQUE;'
        )
        lines.append("")

    if include_indexes:
        lines.append("// --- Indexes ---")
        lines.append('CREATE INDEX lean_decl_name IF NOT EXISTS FOR (n:LeanDecl) ON (n.name);')
        lines.append('CREATE INDEX lean_decl_kind IF NOT EXISTS FOR (n:LeanDecl) ON (n.kind);')
        lines.append('CREATE INDEX lean_decl_file IF NOT EXISTS FOR (n:LeanDecl) ON (n.file);')
        lines.append("")

    lines.append("// --- File Nodes ---")
    for lf in files:
        lines.append(cypher_file_node(lf))
    lines.append("")

    lines.append("// --- Declaration Nodes ---")
    for lf in files:
        for decl in lf.declarations:
            lines.append(cypher_node(decl))
    lines.append("")

    lines.append("// --- File Contains Declaration Edges ---")
    for lf in files:
        for decl in lf.declarations:
            lines.append(cypher_file_decl_edge(lf.path, decl))
    lines.append("")

    lines.append("// --- Declaration Dependency Edges ---")
    for edge in decl_edges:
        lines.append(cypher_decl_edge(edge))
    lines.append("")

    lines.append("// --- File Import Edges ---")
    for edge in import_edges:
        lines.append(cypher_import_edge(edge))
    lines.append("")

    lines.append("// --- Summary Queries ---")
    lines.append('// MATCH (n:LeanDecl) RETURN count(n) AS declaration_count;')
    lines.append('// MATCH (f:LeanFile) RETURN count(f) AS file_count;')
    lines.append('// MATCH ()-[r:DEPENDS_ON]->() RETURN count(r) AS dependency_count;')
    lines.append('// MATCH ()-[r:IMPORTS]->() RETURN count(r) AS import_count;')
    lines.append("")
    lines.append("// End of export")

    output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Exported Cypher to {output}")
    print(f"  Files: {len(files)}")
    print(f"  Declarations: {sum(len(lf.declarations) for lf in files)}")
    print(f"  Decl->Decl edges: {len(decl_edges)}")
    print(f"  Import edges: {len(import_edges)}")


def main():
    parser = argparse.ArgumentParser(
        description="Export Lean 4 declaration graph to Neo4j Cypher"
    )
    parser.add_argument(
        "--output",
        default="lean_graph.cypher",
        help="Output Cypher file path (default: lean_graph.cypher)",
    )
    parser.add_argument(
        "--files",
        nargs="+",
        help="Specific Lean files to process (relative to repo root)",
    )
    parser.add_argument(
        "--no-constraints",
        action="store_true",
        help="Skip creating uniqueness constraints",
    )
    parser.add_argument(
        "--no-indexes",
        action="store_true",
        help="Skip creating indexes",
    )
    parser.add_argument(
        "--discover",
        action="store_true",
        default=True,
        help="Automatically discover all .lean files (default: true)",
    )
    parser.add_argument(
        "--stats-only",
        action="store_true",
        help="Print statistics without writing Cypher file",
    )
    args = parser.parse_args()

    if args.files:
        files = [REPO_ROOT / f for f in args.files]
    else:
        files = discover_lean_files(REPO_ROOT)

    print(f"Discovered {len(files)} Lean files")

    parsed_files: List[LeanFile] = []
    for f in files:
        if f.exists():
            lf = parse_lean_file(f)
            parsed_files.append(lf)
        else:
            print(f"  WARNING: {f} not found", file=sys.stderr)

    total_decls = sum(len(lf.declarations) for lf in parsed_files)
    print(f"Parsed {len(parsed_files)} files, {total_decls} declarations")

    if args.stats_only:
        # Print per-file stats
        for lf in sorted(parsed_files, key=lambda x: -len(x.declarations))[:20]:
            print(f"  {lf.path}: {len(lf.declarations)} decls, {len(lf.imports)} imports")
        return

    # Build dependency edges
    all_decls_by_fqn: Dict[str, LeanDecl] = {}
    for lf in parsed_files:
        for decl in lf.declarations:
            key = decl.fully_qualified_name or f"{lf.path}:{decl.name}"
            all_decls_by_fqn[key] = decl

    decl_edges, import_edges = build_dependency_edges(parsed_files, all_decls_by_fqn)

    output = Path(args.output)
    if not output.is_absolute():
        output = REPO_ROOT / output

    export_cypher(
        parsed_files,
        decl_edges,
        import_edges,
        output,
        include_constraints=not args.no_constraints,
        include_indexes=not args.no_indexes,
    )


if __name__ == "__main__":
    main()
