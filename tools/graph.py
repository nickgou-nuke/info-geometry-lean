#!/usr/bin/env python3
"""Canonical Graph System for InfoGeometry Lean 4 Codebase."""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Iterable, List, Optional, Set, Tuple

try:
    import networkx as nx
except ImportError:
    # Fallback to avoid breaking tools if networkx is missing in some environments
    nx = None

from tools.pathing import (
    default_docs_map_root,
    lean_root,
    repo_root,
)


class ProjectGraph:
    """A canonical, NetworkX-based representation of the Lean 4 dependency graph.
    
    This class serves as the 'brain' for agentic navigation of the codebase.
    It links declaration names to their logical dependencies and physical source files.
    """

    def __init__(self, graph_path: Optional[Path] = None):
        if nx is None:
            raise ImportError("networkx is required for ProjectGraph. Run 'pip install networkx'.")
        
        self.graph_path = graph_path or (default_docs_map_root() / "graph.json")
        self.g = nx.MultiDiGraph()
        self.load()

    def load(self) -> None:
        """Load the graph from graph.json."""
        self.g.clear()
        if not self.graph_path.exists():
            print(f"[ProjectGraph] Warning: {self.graph_path} not found. Graph is empty.")
            return

        with open(self.graph_path, "r", encoding="utf-8") as f:
            data = json.load(f)

        nodes = data.get("nodes", [])
        self.g.add_nodes_from(nodes)

        for edge in data.get("edges", []):
            if len(edge) == 2:
                u, target_info = edge
                if isinstance(target_info, list) and len(target_info) == 2:
                    v, kind = target_info
                    self.g.add_edge(u, v, kind=kind)
                else:
                    # Fallback for simple [u, v] pairs
                    v = target_info
                    self.g.add_edge(u, v, kind="unknown")
            elif len(edge) == 3:
                u, v, kind = edge
                self.g.add_edge(u, v, kind=kind)

    def rebuild(self) -> None:
        """Invoke the Lean export script to rebuild the graph.json and reload it."""
        print("[ProjectGraph] Rebuilding graph from Lean environment...")
        subprocess.run(
            ["python3", "-m", "scripts", "make-graph"],
            check=True,
            cwd=repo_root(),
        )
        self.load()

    def get_neighbors(self, node: str, direction: str = "out") -> List[str]:
        """Get direct dependencies (out) or things that depend on this node (in)."""
        if node not in self.g:
            return []
        if direction == "out":
            return list(self.g.successors(node))
        return list(self.g.predecessors(node))

    def get_shortest_path(self, source: str, target: str) -> Optional[List[str]]:
        """Find the logical path between two declarations."""
        try:
            return nx.shortest_path(self.g, source, target)
        except (nx.NetworkXNoPath, nx.NodeNotFound):
            return None

    def get_ancestors(self, node: str) -> Set[str]:
        """Find everything that this node transitively depends on."""
        if node not in self.g:
            return set()
        return nx.ancestors(self.g, node)

    def get_descendants(self, node: str) -> Set[str]:
        """Find everything that transitively depends on this node."""
        if node not in self.g:
            return set()
        return nx.descendants(self.g, node)

    def filter_noise(self) -> nx.MultiDiGraph:
        """Return a subgraph excluding generated internal nodes (._proof, .match_)."""
        noise_patterns = ["._", ".match_", ".proof_", ".brecOn", ".below", ".injEq", ".sizeOf_spec"]
        clean_nodes = [
            n for n in self.g.nodes 
            if not any(p in n for p in noise_patterns)
        ]
        return self.g.subgraph(clean_nodes)

    def get_module_of(self, node: str) -> Optional[str]:
        """Infer the module name from the declaration name."""
        # This assumes standard Lean naming: InfoGeometry.KL.klDiv -> InfoGeometry.KL
        parts = node.split(".")
        if len(parts) > 1:
            return ".".join(parts[:-1])
        return None

    def get_file_path(self, node: str) -> Optional[Path]:
        """Map a declaration to its .lean source file."""
        module = self.get_module_of(node)
        if not module:
            return None
        
        # Convert InfoGeometry.KL to lean/InfoGeometry/KL.lean
        rel_path = Path(*module.split(".")).with_suffix(".lean")
        
        # Check potential roots
        roots = [lean_root(), repo_root()]
        for root in roots:
            full_path = root / rel_path
            if full_path.exists():
                # Verify if the declaration is likely in this file
                content = full_path.read_text(encoding="utf-8", errors="ignore")
                short_name = node.split(".")[-1]
                if short_name in content:
                    return full_path
            
            # If not in the module file, it might be in a submodule directory
            # e.g. InfoGeometry.Core.SymmetricLieAlgebra might be in InfoGeometry/Core/SymmetricLie.lean
            # Let's search in the directory corresponding to the parent namespace
            parent_ns = ".".join(module.split(".")[:-1])
            if parent_ns:
                parent_dir = root / Path(*parent_ns.split("."))
                if parent_dir.exists() and parent_dir.is_dir():
                    short_name = node.split(".")[-1]
                    for lean_file in parent_dir.rglob("*.lean"):
                        content = lean_file.read_text(encoding="utf-8", errors="ignore")
                        if f" {short_name}" in content or f"\n{short_name}" in content:
                             return lean_file

        return None

    def get_source_code(self, node: str) -> Optional[str]:
        """Extract the source code block for the given node."""
        path = self.get_file_path(node)
        if not path:
            return None
        
        # Simple heuristic: find line with declaration name
        # In a real agentic workflow, we'd use 'grep' or 'read_file' with line context.
        content = path.read_text(encoding="utf-8")
        lines = content.splitlines()
        
        short_name = node.split(".")[-1]
        for i, line in enumerate(lines):
            if short_name in line and ("def" in line or "theorem" in line or "lemma" in line or "inductive" in line):
                # Return 20 lines of context as a starting point
                return "\n".join(lines[i:i+20])
        return None

    def generate_latex_stub(self, node: str) -> str:
        """Generate a LaTeX snippet for the blueprint node."""
        label = node.replace(".", ":").lower()
        return (
            f"\\begin{{theorem}}[blueprint=\"{label}\"]\n"
            f"  \\inputleannode{{{node}}}\n"
            f"\\end{{theorem}}\n"
        )

# For backward compatibility with existing scripts
def load_graph(path: Path) -> dict[str, Any]:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def edges_as_tuples(data: dict[str, Any]) -> Iterable[Tuple[str, str]]:
    for e in data.get('edges', []):
        yield (e[0], e[1])

def nodes(data: dict[str, Any]) -> Iterable[str]:
    return data.get('nodes', [])
