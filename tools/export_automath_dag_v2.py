#!/usr/bin/env python3
"""
Extract declaration-level dependency DAG from Lean 4 source files.
Uses proper parsing of theorem/def/lemma/instance declarations and their references.
"""

import re
import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Set, Tuple
from dataclasses import dataclass, asdict
from collections import defaultdict
import argparse

REPO_ROOT = Path(__file__).parent.parent

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

INFRA_FILES = [
    "lean/InfoGeometry/Algebra/CuntzTensorQuotient.lean",
    "lean/InfoGeometry/Algebra/CuntzFibonacciBraidInclusion.lean",
    "lean/InfoGeometry/Algebra/FibonacciGrothendieckRing.lean",
]

REPO_ROOT = Path(__file__).parent.parent

# Regex patterns for Lean 4 declarations
DECL_PATTERNS = [
    (re.compile(r'^(theorem|lemma|def|instance|class|structure)\s+(\w+)', re.MULTILINE), 'decl'),
    (re.compile(r'^@\[.*?\]\s*(theorem|lemma|def|instance|class|structure)\s+(\w+)', re.MULTILINE), 'decl'),
]

# Pattern to find references to other declarations (capitalized identifiers)
REF_PATTERN = re.compile(r'\b([A-Z][a-zA-Z0-9_]*|[a-z][a-zA-Z0-9_]*\.[a-zA-Z0-9_]+)\b')

# Keywords to exclude from reference matching
LEAN_KEYWORDS = {
    'theorem', 'lemma', 'def', 'instance', 'class', 'structure', 'inductive',
    'namespace', 'open', 'import', 'variable', 'variables', 'section', 'end',
    'noncomputable', 'partial', 'protected', 'private', 'public', 'abstract',
    'mutual', 'where', 'have', 'show', 'by', 'calc', 'obtain', 'let', 'match',
    'if', 'then', 'else', 'fun', 'forall', 'exists', 'intro', 'intros',
    'apply', 'rw', 'simp', 'norm_num', 'linarith', 'ring_nf', 'field_simp',
    'exact', 'refine', 'constructor', 'cases', 'induction', 'rcases', 'rcases',
    'simp_all', 'norm_cast', 'ring', 'abel', 'tauto', 'aesop', 'decide',
    'trivial', 'rfl', 'done', 'admit', 'sorry', 'using', 'with', 'at',
    'hypotheses', 'local', 'notation', 'infix', 'prefix', 'postfix',
    'precedence', 'left', 'right', 'as', ':=', ':', '|', '->', '∀', '∃',
    '∧', '∨', '¬', '→', '←', '↔', '=', '≠', '<', '>', '≤', '≥', '∈', '∉',
    '∪', '∩', '⊆', '⊇', '⊂', '⊃', '∈', '∉', '∅', '∑', '∏', '∫',
    '∂', '∇', '∞', 'ℝ', 'ℂ', 'ℕ', 'ℤ', 'ℚ', 'ℙ', '𝔸', '𝔹', '𝔽',
    'True', 'False', 'None', 'Some', 'Option', 'List', 'Array', 'Finset',
    'Fintype', 'DecidableEq', 'Decidable', 'Inhabited', 'Nonempty',
    'Unique', 'Subsingleton', 'Contr', 'Prop', 'Type', 'Sort', 'Set',
    'Function', 'Relation', 'Equiv', 'Ordering', 'LinearOrder',
    'PartialOrder', 'Preorder', 'TotalOrder', 'Lattice', 'CompleteLattice',
    'DistribLattice', 'Heyting', 'Boolean', 'Algebra', 'Module', 'Ring',
    'Field', 'CommRing', 'CommSemiring', 'Semiring', 'Semigroup',
    'Monoid', 'Group', 'AbelianGroup', 'AddGroup', 'AddMonoid', 'AddSemigroup',
    'NormedSpace', 'InnerProductSpace', 'HilbertSpace', 'BanachSpace',
    'TopologicalSpace', 'MetricSpace', 'CompleteSpace', 'CompactSpace',
    'ConnectedSpace', 'PathConnected', 'Continuous', 'Differentiable',
    'Smooth', 'Analytic', 'Holomorphic', 'Meromorphic', 'Entire',
    'Real', 'Imag', 'Complex', 'abs', 'norm', 'dist', 'inner',
    'sin', 'cos', 'tan', 'exp', 'log', 'sqrt', 'pow', 'factorial',
    'Nat', 'Int', 'Rat', 'Float', 'String', 'Char', 'Bool', 'Unit',
    'PUnit', 'Empty', 'Unit', 'PUnit', 'Sum', 'Prod', 'Sigma', 'Pi',
    'Subtype', 'Quotient', 'Quot', 'QuotientGroup', 'QuotientRing',
    'Localization', 'FractionRing', 'Polynomial', 'PowerSeries',
    'FormalPowerSeries', 'Matrix', 'Vec', 'Fin', 'Finset', 'Multiset',
    'List', 'Array', 'Buffer', 'String', 'ByteArray', 'IO', 'Task',
    'Future', 'Promise', 'Async', 'Await', 'Parallel', 'Channel',
    'Mutex', 'Semaphore', 'Lock', 'RWLock', 'CondVar', 'Barrier',
    'Atomic', 'Ref', 'Cell', 'Once', 'Lazy', 'Option', 'Result',
    'Either', 'These', 'NEither', 'NEither', 'WithBot', 'WithTop',
    'OrderBot', 'OrderTop', 'ConditionallyCompleteLinearOrder',
    'ConditionallyCompleteLattice', 'DistribLattice', 'HeytingAlgebra',
    'BooleanAlgebra', 'CompleteBooleanAlgebra', 'StoneAlgebra',
    'DeMorganAlgebra', 'OrthomodularLattice', 'ModularLattice',
    'ComplementedLattice', 'OrthocomplementedLattice', 'Ortholattice',
    'Quantale', 'Frame', 'Locale', 'HeytingAlgebra', 'BiHeytingAlgebra',
    'ResiduatedLattice', 'FLew', 'FL', 'MTL', 'BL', 'MV', 'Godel',
    'Product', 'Coproduct', 'Limit', 'Colimit', 'Pullback', 'Pushout',
    'Equalizer', 'Coequalizer', 'Kernel', 'Cokernel', 'Image', 'Coimage',
    'Monomorphism', 'Epimorphism', 'Isomorphism', 'Section', 'Retraction',
    'SplitMono', 'SplitEpi', 'Bimorphism', 'RegularMono', 'RegularEpi',
    'StrongMono', 'StrongEpi', 'ExtremalMono', 'ExtremalEpi', 'Image',
    'Coimage', 'Factorization', 'EpiMonoFactorization', 'MonoEpiFactorization',
    'Exact', 'ShortExact', 'LongExact', 'Derived', 'Homology', 'Cohomology',
    'Tor', 'Ext', 'Hom', 'Tensor', 'Exterior', 'Symmetric', 'DividedPower',
    'Gamma', 'Beta', 'Zeta', 'Gamma', 'Riemann', 'Lerch', 'Polylog',
    'Harmonic', 'Bernoulli', 'Euler', 'Stirling', 'Catalan', 'Bell',
    'Fibonacci', 'Lucas', 'Pell', 'Tribonacci', 'Tetranacci', 'Narayana',
    'Motzkin', 'Schroder', 'Delannoy', 'Riordan', 'Shapiro', 'Large',
    'Schroder', 'Hahn', 'Meixner', 'Krawtchouk', 'Charlier', 'Meixner',
    'Pollaczek', 'Racah', 'Wilson', 'Askey', 'AskeyWilson', 'qHahn',
    'qMeixner', 'qKrawtchouk', 'qCharlier', 'qRacah', 'qWilson',
    'AskeyWilson', 'qHahn', 'qMeixner', 'qKrawtchouk', 'qCharlier',
    'qRacah', 'qWilson', 'AskeyWilson', 'qHahn', 'qMeixner', 'qKrawtchouk',
    'qCharlier', 'qRacah', 'qWilson', 'AskeyWilson', 'qHahn', 'qMeixner',
    'qKrawtchouk', 'qCharlier', 'qRacah', 'qWilson', 'AskeyWilson',
}

@dataclass
class LeanDecl:
    name: str
    kind: str
    file: str
    line: int
    full_name: str
    raw_line: str

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
    relation: str

def extract_declarations(file_path: Path) -> List[Dict]:
    """Extract theorem/def/lemma/instance declarations from a Lean file."""
    content = file_path.read_text()
    lines = content.split('\n')
    
    decls = []
    current_decl = None
    paren_depth = 0
    brace_depth = 0
    
    for i, line in enumerate(lines):
        stripped = line.strip()
        
        # Skip comments
        if stripped.startswith('--') or stripped.startswith('/-'):
            continue
            
        # Track parentheses/brackets for multi-line declarations
        paren_depth += line.count('(') - line.count(')')
        brace_depth += line.count('{') - line.count('}')
        
        # Match declaration headers
        for pattern, _ in DECL_PATTERNS:
            m = pattern.match(line)
            if m:
                kind = m.group(1)
                name = m.group(2)
                decls.append({
                    'name': name,
                    'kind': kind,
                    'file': str(file_path.relative_to(REPO_ROOT)),
                    'line': i + 1,
                    'full_name': name,  # will be qualified later
                    'raw_line': line.strip(),
                })
                break
    
    return decls

def extract_references(file_path: Path, all_decl_names: Set[str]) -> Dict[str, List[str]]:
    """Extract references to other declarations within a file."""
    content = file_path.read_text()
    refs = defaultdict(list)
    
    # Simple approach: find all capitalized identifiers that match known decl names
    for decl_name in all_decl_names:
        # Skip very short names to avoid false positives
        if len(decl_name) < 3:
            continue
        # Find references (but not the declaration itself)
        pattern = re.compile(rf'\b{re.escape(decl_name)}\b')
        for match in pattern.finditer(content):
            # Find which declaration this reference appears in
            line_num = content[:match.start()].count('\n') + 1
            refs[decl_name].append(f"line {line_num}")
    
    return refs

def build_full_names(decls: List[Dict]) -> Dict[str, str]:
    """Map short names to fully qualified names based on file."""
    name_map = {}
    for d in decls:
        file_stem = Path(d['file']).stem
        full = f"{file_stem}.{d['name']}"
        name_map[d['name']] = full
    return name_map

def main():
    parser = argparse.ArgumentParser(description="Export Lean derivation DAG")
    parser.add_argument("--output", default="derivation_dag.jsonl")
    parser.add_argument("--graphml", help="Also output GraphML")
    parser.add_argument("--files", nargs="+", help="Specific files")
    args = parser.parse_args()

    files_to_process = []
    if args.files:
        files_to_process = [REPO_ROOT / f for f in args.files]
    else:
        files_to_process = [REPO_ROOT / f for f in VERIFIED_FILES + INFRA_FILES]

    print(f"Processing {len(files_to_process)} files...")
    
    # First pass: extract all declarations
    all_decls = []
    for f in [REPO_ROOT / f for f in VERIFIED_FILES + INFRA_FILES]:
        if f.exists():
            decls = extract_declarations(f)
            for d in decls:
                d['file'] = str(f.relative_to(REPO_ROOT))
            print(f"  {f.relative_to(REPO_ROOT)}: {len(decls)} decls")
            all_decls.extend(decls)
        else:
            print(f"  WARNING: {f} not found")

    print(f"Total declarations: {len(all_decls)}")
    
    # Build name map
    name_map = build_full_names(all_decls)
    
    # Build reference graph
    all_names = set(d['name'] for d in all_decls)
    edges = []
    
    for f in [REPO_ROOT / f for f in VERIFIED_FILES + INFRA_FILES]:
        if f.exists():
            refs = extract_references(f, set(name_map.keys()))
            for src, targets in refs.items():
                for tgt in targets:
                    if src in name_map:
                        edges.append({
                            'source': name_map[src],
                            'target': tgt,
                            'relation': 'depends_on'
                        })
    
    # Build nodes
    nodes = []
    for d in all_decls:
        nodes.append({
            'id': name_map.get(d['name'], d['name']),
            'label': f"{d['kind']} {d['name']}",
            'type': d['kind'],
            'file': d['file'],
            'line': d['line']
        })
    
    print(f"DAG: {len(nodes)} nodes, {len(edges)} edges")
    
    # Export JSONL
    with open('derivation_dag.jsonl', 'w') as f:
        for node in nodes:
            f.write(json.dumps({"type": "node", **node}) + '\n')
        for edge in edges:
            f.write(json.dumps({"type": "edge", **edge}) + '\n')
    
    print(f"Exported to derivation_dag.jsonl")

if __name__ == "__main__":
    main()