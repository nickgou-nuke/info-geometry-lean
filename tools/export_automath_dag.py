#!/usr/bin/env python3
"""
Export Lean 4 derivation DAG from verified owner files to JSONL/GraphML
for Arango/Sisyphus ingestion.

Usage:
  python3 tools/export_automath_dag.py --output derivation_dag.jsonl
  python3 tools/export_automath_dag.py --graphml derivation_dag.graphml
"""

import json
import subprocess
import sys
import re
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional
from dataclasses import dataclass, asdict
import argparse

REPO_ROOT = Path(__file__).parent.parent

# Verified owner files (kernel-green, 0 sorry)
VERIFIED_FILES = [
    "lean/InfoGeometry/Algebra/GellMannBasis.lean",
    "lean/InfoGeometry/Algebra/GellMannTraceOrthogonality.lean",
    "lean/InfoGeometry/Algebra/StructureConstants.lean",
    "lean/InfoGeometry/Algebra/SpecialUnitary.lean",
    "lean/InfoGeometry/Algebra/KillingFormSU.lean",
    "lean/InfoGeometry/Algebra/Cl11Fermions.lean",
    "lean/InfoGeometry/Algebra/TripotentClSUSYBridge.lean",
    "lean/InfoGeometry/Algebra/FreudenthalComplete.lean",
    "lean/InfoGeometry/Algebra/GoldenMeanShift.lean",
    "lean/InfoGeometry/Algebra/Hypothesis1.lean",
]

# Also include Cuntz/Fibonacci/Braid infrastructure
INFRA_FILES = [
    "lean/InfoGeometry/Algebra/CuntzTensorQuotient.lean",
    "lean/InfoGeometry/Algebra/CuntzFibonacciBraidInclusion.lean",
    "lean/InfoGeometry/Algebra/FibonacciGrothendieckRing.lean",
]

@dataclass
class LeanDecl:
    name: str
    kind: str  # theorem, def, lemma, instance, class, structure
    file: str
    line: int
    deps: List[str]  # fully qualified names
    statement: str
    proof_term: Optional[str] = None

@dataclass
class DagNode:
    id: str
    label: str
    type: str
    file: str
    line: int

@dataclass
class DagEdge:
    source: str
    target: str
    relation: str  # "depends_on", "uses", "proves"

def extract_decls(file_path: Path) -> List[LeanDecl]:
    """Extract declarations from a Lean file using lake env lean --deps."""
    # Use lean --deps to get dependency graph
    result = subprocess.run(
        ["lake", "env", "lean", "--deps", str(file_path)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=60
    )
    if result.returncode != 0:
        print(f"Warning: lean --deps failed for {file_path}: {result.stderr}")
        return []

    # Parse the output
    deps = {}
    for line in result.stdout.strip().split('\n'):
        if ':' in line:
            parts = line.split(':', 1)
            if len(parts) == 2:
                target = parts[0].strip()
                sources = [s.strip() for s in parts[1].split() if s.strip()]
                deps[target] = sources

    # Now extract declarations using a simple regex approach
    content = file_path.read_text()
    decls = []
    
    # Pattern for theorems, defs, lemmas, instances
    pattern = re.compile(
        r'^(theorem|def|lemma|instance|class|structure)\s+(\w+)(?:\s*[\(:]|\s*$)',
        re.MULTILINE
    )
    
    lines = content.split('\n')
    for i, line in enumerate(lines):
        m = pattern.match(line)
        if m:
            kind = m.group(1)
            name = m.group(2)
            full_name = f"{file_path.stem}.{name}"  # approximate
            decl_deps = deps.get(name, [])
            decls.append(LeanDecl(
                name=name,
                kind=kind,
                file=str(file_path.relative_to(REPO_ROOT)),
                line=i + 1,
                deps=decl_deps,
                statement=line.strip()
            ))
    
    return decls

def build_dag(all_decls: List[LeanDecl]) -> Tuple[List[DagNode], List[DagEdge]]:
    """Build DAG nodes and edges from declarations."""
    name_to_decl = {d.name: d for d in all_decls}
    nodes = []
    edges = []
    
    for decl in all_decls:
        node = DagNode(
            id=decl.name,
            label=f"{decl.kind} {decl.name}",
            type=decl.kind,
            file=decl.file,
            line=decl.line
        )
        nodes.append(node)
        
        for dep in decl.deps:
            if dep in name_to_decl:
                edges.append(DagEdge(
                    source=decl.name,
                    target=dep,
                    relation="depends_on"
                ))
    
    return nodes, edges

def export_jsonl(nodes: List[DagNode], edges: List[DagEdge], output: Path):
    """Export as JSONL (one node/edge per line)."""
    with open(output, 'w') as f:
        for node in nodes:
            f.write(json.dumps({"type": "node", **asdict(node)}) + '\n')
        for edge in edges:
            f.write(json.dumps({"type": "edge", **asdict(edge)}) + '\n')
    print(f"Exported {len(nodes)} nodes, {len(edges)} edges to {output}")

def export_graphml(nodes: List[DagNode], edges: List[DagEdge], output: Path):
    """Export as GraphML for Gephi/Arango import."""
    lines = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<graphml xmlns="http://graphml.graphdrawing.org/xmlns">',
        '  <key id="label" for="node" attr.name="label" attr.type="string"/>',
        '  <key id="type" for="node" attr.name="type" attr.type="string"/>',
        '  <key id="file" for="node" attr.name="file" attr.type="string"/>',
        '  <key id="line" for="node" attr.name="line" attr.type="int"/>',
        '  <key id="relation" for="edge" attr.name="relation" attr.type="string"/>',
        '  <graph id="G" edgedefault="directed">',
    ]
    
    for node in nodes:
        lines.append(f'    <node id="{node.id}">')
        lines.append(f'      <data key="label">{node.label}</data>')
        lines.append(f'      <data key="type">{node.type}</data>')
        lines.append(f'      <data key="file">{node.file}</data>')
        lines.append(f'      <data key="line">{node.line}</data>')
        lines.append('    </node>')
    
    for edge in edges:
        lines.append(f'    <edge id="e{edge.source}->{edge.target}" source="{edge.source}" target="{edge.target}">')
        lines.append(f'      <data key="relation">{edge.relation}</data>')
        lines.append('    </edge>')
    
    lines.extend([
        '  </graph>',
        '</graphml>'
    ])
    
    output.write_text('\n'.join(lines))
    print(f"Exported GraphML to {output}")

def main():
    parser = argparse.ArgumentParser(description="Export Lean derivation DAG")
    parser.add_argument("--output", default="derivation_dag.jsonl", help="Output JSONL file")
    parser.add_argument("--graphml", help="Also output GraphML file")
    parser.add_argument("--files", nargs="+", help="Specific files to process")
    args = parser.parse_args()

    files_to_process = []
    if args.files:
        files_to_process = [REPO_ROOT / f for f in args.files]
    else:
        files_to_process = [REPO_ROOT / f for f in VERIFIED_FILES + INFRA_FILES]

    print(f"Processing {len(files_to_process)} files...")
    
    all_decls = []
    for f in files_to_process:
        if f.exists():
            decls = extract_decls(f)
            print(f"  {f.relative_to(REPO_ROOT)}: {len(decls)} decls")
            all_decls.extend(decls)
        else:
            print(f"  WARNING: {f} not found")

    print(f"Total declarations: {len(all_decls)}")
    
    nodes, edges = build_dag(all_decls)
    print(f"DAG: {len(nodes)} nodes, {len(edges)} edges")
    
    export_jsonl(nodes, edges, Path(args.output))
    
    if args.graphml:
        export_graphml(nodes, edges, Path(args.graphml))

if __name__ == "__main__":
    main()