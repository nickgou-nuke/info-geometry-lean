#!/usr/bin/env python3
"""Heuristic theorem vacuity triage — Layer B of the vacuity enforcement system.

Reads the DAG-exported declaration and edge JSONs and produces a per-theorem
rule-based vacuity classification. Combined with the Lean-side linter (Layer A,
``Vacuity.lean``) and the CI policy gate (Layer C, ``check_vacuity_policy.py``),
this gives a three-layer vacuity enforcement system.

Violation classes produced:

  V0  syntactic vacuity — rfl-like proof screen
  V1  public wrapper inflation — proof forwards to single prior theorem
  V2  dead public theorem — zero reverse edges, no capstone annotation
  V3  statement redundancy — (placeholder, not yet computed)
  V4  bridge infrastructure promoted — infrastructure in bridge file
  V5  unjustified canonicality — (requires NLP, placeholder)
  V6  quotient fraud — (requires semantic analysis, placeholder)

Usage::

    python3 tools/theorem_significance.py \\
        [--decls FILE] [--edges FILE] \\
        [--out FILE] [--md FILE] \\
        [--strict-paths PREFIX ...] \\
        [--bridge-hints WORD ...]

Output:  JSON array of classified declarations and a Markdown summary report.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))

from pathing import repo_root
from vacuity_policy_config import (
    BRIDGE_HINTS_DEFAULT,
    EXEMPT_ATTRS,
    STRICT_PATHS_DEFAULT,
    expected_violation_level,
    is_bridge_file,
    is_strict_file,
)

# ─── data model ───────────────────────────────────────────────

@dataclass
class DeclInfo:
    name: str
    kind: str              # theorem | def | inductive | constructor | …
    file: str | None = None
    module: str | None = None
    line: int = 0
    doc: str = ""
    attrs: list[str] = field(default_factory=list)

@dataclass
class GraphStats:
    reverse_type: int = 0   # how many declarations reference this in type position
    reverse_value: int = 0  # how many declarations reference this in value (proof) position
    forward_type: int = 0   # how many declarations this references in type position
    forward_value: int = 0  # how many declarations this references in value position
    reverse_public_fan_in: int = 0      # distinct reverse users with type-edge dependency
    reverse_proof_only_reuse: int = 0   # distinct reverse users with value-only dependency
    is_sink: bool = False   # no forward value edges
    depth: int = 0          # longest reverse-chain length in condensation DAG
    transitive_reverse_reach: int = 0   # number of transitive reverse dependents
    descendant_mass: int = 0            # number of transitive forward dependencies
    scc_size: int = 1                   # strongly connected component size
    scc_role: str = "acyclic"          # SCC role: acyclic/self-cycle/cycle-*


@dataclass
class ReverseUseProfile:
    public_fan_in: int = 0
    proof_only_reuse: int = 0


@dataclass
class StructuralProfile:
    depth: int = 0
    transitive_reverse_reach: int = 0
    descendant_mass: int = 0
    scc_size: int = 1
    scc_role: str = "acyclic"

@dataclass
class ProofShapeInfo:
    """Proof-shape classification inferred from the edge graph (no Lean elaboration)."""
    forward_value_targets: list[str] = field(default_factory=list)
    forward_theorem_targets: list[str] = field(default_factory=list)
    n_forward_value: int = 0
    n_forward_theorem: int = 0

    @property
    def is_exact_forward(self) -> bool:
        return self.n_forward_value == 1 and self.n_forward_theorem == 1

    @property
    def exact_forward_target(self) -> str | None:
        if not self.is_exact_forward or len(self.forward_theorem_targets) != 1:
            return None
        return self.forward_theorem_targets[0]

    @property
    def is_rfl_like(self) -> bool:
        return self.n_forward_value == 0

@dataclass
class ScoredDecl:
    name: str
    kind: str
    file: str | None
    module: str | None
    attrs: list[str]
    graph: GraphStats
    proof: ProofShapeInfo
    tags: list[str] = field(default_factory=list)
    violations: list[tuple[str, str]] = field(default_factory=list)  # (level, code)
    vacuity_suspicion_score: float = 0.0
    vacuity_suspicion_confidence: float = 0.0
    vacuity_suspicion_factors: list[dict[str, str | float]] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "kind": self.kind,
            "file": self.file,
            "module": self.module,
            "attrs": self.attrs,
            "reverse_type": self.graph.reverse_type,
            "reverse_value": self.graph.reverse_value,
            "forward_type": self.graph.forward_type,
            "forward_value": self.graph.forward_value,
            "reverse_public_fan_in": self.graph.reverse_public_fan_in,
            "reverse_proof_only_reuse": self.graph.reverse_proof_only_reuse,
            "is_sink": self.graph.is_sink,
            "depth": self.graph.depth,
            "transitive_reverse_reach": self.graph.transitive_reverse_reach,
            "descendant_mass": self.graph.descendant_mass,
            "scc_size": self.graph.scc_size,
            "scc_role": self.graph.scc_role,
            "n_forward_value": self.proof.n_forward_value,
            "n_forward_theorem": self.proof.n_forward_theorem,
            "tags": self.tags,
            "violations": [{"level": v[0], "code": v[1]} for v in self.violations],
            "vacuity_suspicion": {
                "score": round(self.vacuity_suspicion_score, 4),
                "confidence": round(self.vacuity_suspicion_confidence, 4),
                "factors": self.vacuity_suspicion_factors,
            },
        }


# ─── classification engine ────────────────────────────────────

# Name suffixes that identify Lean-generated theorems (inductive eliminators,
# injection lemmas, sizeof specs, etc.).  These are auto-generated by the
# kernel or deriving handlers and should not receive vacuity violations.
_GENERATED_SUFFIXES = (
    ".rec", ".recOn", ".casesOn", ".below", ".brecOn", ".noConfusion",
    ".noConfusionType", ".sizeOf_spec", ".mk.inj", ".mk.injEq",
    ".eq_def", ".eta",
    ".eq_1", ".eq_2", ".eq_3",
    ".congr_simp",
    ".ofNat_ctorIdx",
)
# Name fragments that identify generated families regardless of position.
_GENERATED_FRAGMENTS = (
    ".match_", ".proof_", "._uniq.",
)


def _is_generated(name: str) -> bool:
    """Return True if the declaration name matches a Lean auto-generated pattern."""
    if any(name.endswith(s) for s in _GENERATED_SUFFIXES):
        return True
    return any(f in name for f in _GENERATED_FRAGMENTS)


def classify_tags(decl: DeclInfo, graph: GraphStats, proof: ProofShapeInfo) -> list[str]:
    """Assign semantic tags based on graph role and proof shape."""
    tags: list[str] = []

    # Dead candidate: no reverse edges at all
    if graph.reverse_type == 0 and graph.reverse_value == 0:
        tags.append("dead-candidate")

    # Statement-bearing: has reverse type consumers
    if graph.reverse_type > 0:
        tags.append("statement-bearing")

    # Proof-infrastructure: used in proofs but not in statements
    if graph.reverse_value > 0 and graph.reverse_type == 0:
        tags.append("proof-infrastructure")

    # Wrapper candidate: exact forwarding proof
    if proof.is_exact_forward:
        tags.append("wrapper-candidate")

    # rfl-like: proof body references zero value edges (trivial)
    if proof.is_rfl_like:
        tags.append("rfl-like")

    # Capstone candidate: sink with significant dependency cone
    if graph.is_sink and (graph.forward_value + graph.forward_type) >= 5:
        tags.append("capstone-candidate")

    # High fan-in: many reverse consumers
    if graph.reverse_type + graph.reverse_value >= 10:
        tags.append("high-fan-in")

    return sorted(set(tags))


def compute_violations(
    decl: DeclInfo,
    tags: list[str],
    file_path: str | None,
    bridge_hints: list[str],
    strict_paths: list[str],
) -> list[tuple[str, str]]:
    """Determine violations based on tags and file context."""
    out: list[tuple[str, str]] = []
    if file_path is None:
        return out

    is_bridge = is_bridge_file(file_path, bridge_hints)

    # V0: syntactic vacuity (rfl-like proof)
    if "rfl-like" in tags:
        level = expected_violation_level(
            "V0/syntactic-vacuity", file_path, strict_paths, bridge_hints
        )
        if level is None:
            level = "warning"
        out.append((level, "V0/syntactic-vacuity"))

    # V1: public wrapper inflation (exact forwarding proof)
    if "wrapper-candidate" in tags:
        level = expected_violation_level(
            "V1/public-wrapper-inflation", file_path, strict_paths, bridge_hints
        )
        if level is None:
            level = "warning"
        out.append((level, "V1/public-wrapper-inflation"))

    # V2: dead public theorem
    if "dead-candidate" in tags:
        level = expected_violation_level(
            "V2/dead-public-theorem", file_path, strict_paths, bridge_hints
        )
        if level is None:
            level = "warning"
        out.append((level, "V2/dead-public-theorem"))

    # V4: bridge infrastructure promoted (rfl-like or wrapper in bridge file)
    if is_bridge and ("rfl-like" in tags or "wrapper-candidate" in tags):
        if "dead-candidate" not in tags:  # don't double-count with V2
            level = expected_violation_level(
                "V4/bridge-infrastructure-promoted", file_path, strict_paths, bridge_hints
            )
            if level is None:
                level = "warning"
            out.append((level, "V4/bridge-infrastructure-promoted"))

    return out


def _clamp01(value: float) -> float:
    if value < 0.0:
        return 0.0
    if value > 1.0:
        return 1.0
    return value


def compute_vacuity_suspicion(
    decl: DeclInfo,
    graph: GraphStats,
    proof: ProofShapeInfo,
    tags: list[str],
    file_path: str | None,
    bridge_hints: list[str],
    strict_paths: list[str],
) -> tuple[float, float, list[dict[str, str | float]]]:
    """Compute an explainable structural vacuity suspicion ranking signal.

    This is telemetry/ranking output only. It does not affect violation severity.
    """
    factors: list[tuple[str, float, float, str]] = []

    def add(signal: str, contribution: float, reliability: float, rationale: str) -> None:
        factors.append((signal, contribution, reliability, rationale))

    # Shape signals.
    if proof.is_exact_forward:
        add("shape.exact-forward", 0.33, 0.90, "single theorem value dependency")
    if proof.is_rfl_like:
        add("shape.rfl-like", 0.24, 0.86, "zero value dependencies")

    # Structural footprint signals.
    if graph.descendant_mass == 0:
        add("structure.low-descendant-mass", 0.18, 0.80, "descendant_mass = 0")
    elif graph.descendant_mass <= 2:
        add("structure.low-descendant-mass", 0.12, 0.75, f"descendant_mass = {graph.descendant_mass}")
    elif graph.descendant_mass <= 5:
        add("structure.low-descendant-mass", 0.06, 0.70, f"descendant_mass = {graph.descendant_mass}")

    if graph.reverse_public_fan_in == 0:
        add("structure.low-public-fan-in", 0.14, 0.82, "reverse_public_fan_in = 0")
    elif graph.reverse_public_fan_in == 1:
        add("structure.low-public-fan-in", 0.07, 0.76, "reverse_public_fan_in = 1")

    if graph.reverse_proof_only_reuse >= 3:
        add(
            "structure.proof-only-reuse",
            0.16,
            0.80,
            f"reverse_proof_only_reuse = {graph.reverse_proof_only_reuse}",
        )
    elif graph.reverse_proof_only_reuse == 2:
        add("structure.proof-only-reuse", 0.11, 0.75, "reverse_proof_only_reuse = 2")
    elif graph.reverse_proof_only_reuse == 1:
        add("structure.proof-only-reuse", 0.05, 0.68, "reverse_proof_only_reuse = 1")

    if graph.depth <= 1:
        add("structure.shallow-depth", 0.08, 0.66, f"depth = {graph.depth}")
    elif graph.depth >= 4:
        add("structure.deep-embedding", -0.08, 0.70, f"depth = {graph.depth}")

    if graph.scc_size > 1:
        add("structure.scc-cycle", -0.10, 0.78, f"scc_size = {graph.scc_size}, role = {graph.scc_role}")
    elif graph.scc_role == "acyclic":
        add("structure.acyclic", 0.03, 0.62, "acyclic declaration")

    # Context signals.
    if is_bridge_file(file_path, bridge_hints):
        add("context.bridge-file", 0.08, 0.72, "bridge hint matched file stem")
    if is_strict_file(file_path, strict_paths):
        add("context.strict-file", 0.04, 0.68, "strict path policy applies")

    # Exemption suppression (ranking only; violations remain independently computed).
    if "auto-generated" in tags:
        add("policy.auto-generated-exempt", -0.95, 0.95, "generated theorem exemption")
    if "role-exempt" in tags:
        add("policy.role-exempt", -0.90, 0.95, "attribute-based exemption")

    raw_score = sum(contribution for _, contribution, _, _ in factors)
    score = _clamp01(raw_score)

    denom = sum(abs(contribution) for _, contribution, _, _ in factors)
    confidence = 0.0
    if denom > 0:
        weighted = sum(abs(contribution) * reliability for _, contribution, reliability, _ in factors)
        confidence = _clamp01(weighted / denom)

    factors_sorted = sorted(factors, key=lambda item: abs(item[1]), reverse=True)
    factor_dicts: list[dict[str, str | float]] = [
        {
            "signal": signal,
            "contribution": round(contribution, 4),
            "reliability": round(reliability, 4),
            "rationale": rationale,
        }
        for signal, contribution, reliability, rationale in factors_sorted
    ]

    return score, confidence, factor_dicts


# ─── data loading ─────────────────────────────────────────────

def load_decls(path: Path) -> dict[str, DeclInfo]:
    decls: dict[str, DeclInfo] = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            d = json.loads(line)
            decls[d["name"]] = DeclInfo(
                name=d["name"],
                kind=d["kind"],
                file=d.get("file"),
                module=d.get("module"),
                line=d.get("line", 0),
                doc=d.get("doc", ""),
                attrs=list(d.get("attrs", [])),
            )
    return decls


def load_edges(path: Path) -> tuple[
    dict[str, list[tuple[str, str]]],   # forward: src -> [(dst, kind)]
    dict[str, list[tuple[str, str]]],   # reverse: dst -> [(src, kind)]
]:
    forward: dict[str, list[tuple[str, str]]] = defaultdict(list)
    reverse: dict[str, list[tuple[str, str]]] = defaultdict(list)
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            e = json.loads(line)
            src, dst, kind = e["src"], e["dst"], e["kind"]
            forward[src].append((dst, kind))
            reverse[dst].append((src, kind))
    return dict(forward), dict(reverse)


# ─── scoring pipeline ─────────────────────────────────────────

def build_graph_stats(
    name: str,
    forward: dict[str, list[tuple[str, str]]],
    reverse: dict[str, list[tuple[str, str]]],
    reverse_use: ReverseUseProfile | None = None,
    structural: StructuralProfile | None = None,
) -> GraphStats:
    fwd = forward.get(name, [])
    rev = reverse.get(name, [])
    gs = GraphStats()
    for _, kind in rev:
        if kind == "type":
            gs.reverse_type += 1
        elif kind == "value":
            gs.reverse_value += 1
    for _, kind in fwd:
        if kind == "type":
            gs.forward_type += 1
        elif kind == "value":
            gs.forward_value += 1
    gs.is_sink = gs.forward_value == 0
    if reverse_use is not None:
        gs.reverse_public_fan_in = reverse_use.public_fan_in
        gs.reverse_proof_only_reuse = reverse_use.proof_only_reuse
    if structural is not None:
        gs.depth = structural.depth
        gs.transitive_reverse_reach = structural.transitive_reverse_reach
        gs.descendant_mass = structural.descendant_mass
        gs.scc_size = structural.scc_size
        gs.scc_role = structural.scc_role
    return gs


def build_reverse_use_profiles(
    reverse: dict[str, list[tuple[str, str]]],
) -> dict[str, ReverseUseProfile]:
    profiles: dict[str, ReverseUseProfile] = {}
    for dst, incoming in reverse.items():
        kinds_by_src: dict[str, set[str]] = defaultdict(set)
        for src, kind in incoming:
            kinds_by_src[src].add(kind)
        public_fan_in = 0
        proof_only_reuse = 0
        for kinds in kinds_by_src.values():
            if "type" in kinds:
                public_fan_in += 1
            elif "value" in kinds:
                proof_only_reuse += 1
        profiles[dst] = ReverseUseProfile(
            public_fan_in=public_fan_in,
            proof_only_reuse=proof_only_reuse,
        )
    return profiles


def _all_nodes(
    decls: dict[str, DeclInfo],
    forward: dict[str, list[tuple[str, str]]],
    reverse: dict[str, list[tuple[str, str]]],
) -> set[str]:
    nodes: set[str] = set(decls.keys())
    for src, outs in forward.items():
        nodes.add(src)
        for dst, _ in outs:
            nodes.add(dst)
    for dst, ins in reverse.items():
        nodes.add(dst)
        for src, _ in ins:
            nodes.add(src)
    return nodes


def build_structural_profiles(
    decls: dict[str, DeclInfo],
    forward: dict[str, list[tuple[str, str]]],
    reverse: dict[str, list[tuple[str, str]]],
) -> dict[str, StructuralProfile]:
    nodes = sorted(_all_nodes(decls, forward, reverse))
    adj: dict[str, set[str]] = {n: set() for n in nodes}
    self_loop_nodes: set[str] = set()

    for src, outs in forward.items():
        if src not in adj:
            adj[src] = set()
        for dst, _ in outs:
            adj[src].add(dst)
            if src == dst:
                self_loop_nodes.add(src)

    # Tarjan SCC decomposition
    index = 0
    index_of: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    sccs: list[list[str]] = []

    def strongconnect(v: str) -> None:
        nonlocal index
        index_of[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)

        for w in adj.get(v, set()):
            if w not in index_of:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index_of[w])

        if lowlink[v] == index_of[v]:
            component: list[str] = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                component.append(w)
                if w == v:
                    break
            sccs.append(component)

    for node in nodes:
        if node not in index_of:
            strongconnect(node)

    node_to_scc: dict[str, int] = {}
    scc_sizes: list[int] = []
    for sid, members in enumerate(sccs):
        scc_sizes.append(len(members))
        for member in members:
            node_to_scc[member] = sid

    scc_out: dict[int, set[int]] = {sid: set() for sid in range(len(sccs))}
    scc_in: dict[int, set[int]] = {sid: set() for sid in range(len(sccs))}

    for src, outs in forward.items():
        src_sid = node_to_scc.get(src)
        if src_sid is None:
            continue
        for dst, _ in outs:
            dst_sid = node_to_scc.get(dst)
            if dst_sid is None or src_sid == dst_sid:
                continue
            scc_out[src_sid].add(dst_sid)
            scc_in[dst_sid].add(src_sid)

    # Longest path depth over SCC DAG (forward direction); this equals reverse-chain depth.
    indeg: dict[int, int] = {sid: len(scc_in[sid]) for sid in scc_in}
    queue: list[int] = [sid for sid, d in indeg.items() if d == 0]
    topo: list[int] = []
    while queue:
        sid = queue.pop()
        topo.append(sid)
        for nxt in scc_out[sid]:
            indeg[nxt] -= 1
            if indeg[nxt] == 0:
                queue.append(nxt)

    scc_depth: dict[int, int] = {sid: 0 for sid in range(len(sccs))}
    for sid in topo:
        for nxt in scc_out[sid]:
            scc_depth[nxt] = max(scc_depth[nxt], scc_depth[sid] + 1)

    # Reachability masses per SCC (cached BFS on condensation graph).
    reverse_reach_cache: dict[int, int] = {}
    descendant_mass_cache: dict[int, int] = {}

    def reachable_mass(start_sid: int, graph: dict[int, set[int]]) -> int:
        seen: set[int] = set()
        stack2: list[int] = list(graph[start_sid])
        while stack2:
            cur = stack2.pop()
            if cur in seen:
                continue
            seen.add(cur)
            for nxt in graph[cur]:
                if nxt not in seen:
                    stack2.append(nxt)
        return sum(scc_sizes[sid] for sid in seen)

    profiles: dict[str, StructuralProfile] = {}
    for name in decls:
        sid = node_to_scc.get(name)
        if sid is None:
            profiles[name] = StructuralProfile()
            continue

        if sid not in reverse_reach_cache:
            reverse_reach_cache[sid] = reachable_mass(sid, scc_in)
        if sid not in descendant_mass_cache:
            descendant_mass_cache[sid] = reachable_mass(sid, scc_out)

        scc_size = scc_sizes[sid]
        if scc_size == 1:
            role = "self-cycle" if name in self_loop_nodes else "acyclic"
        else:
            indegree = len(scc_in[sid])
            outdegree = len(scc_out[sid])
            if indegree == 0 and outdegree == 0:
                role = "cycle-island"
            elif indegree == 0:
                role = "cycle-source"
            elif outdegree == 0:
                role = "cycle-sink"
            else:
                role = "cycle-core"

        profiles[name] = StructuralProfile(
            depth=scc_depth[sid],
            transitive_reverse_reach=reverse_reach_cache[sid],
            descendant_mass=descendant_mass_cache[sid],
            scc_size=scc_size,
            scc_role=role,
        )

    return profiles


def build_proof_shape(
    name: str,
    forward: dict[str, list[tuple[str, str]]],
    decls: dict[str, DeclInfo],
) -> ProofShapeInfo:
    fwd = forward.get(name, [])
    value_targets = [dst for dst, kind in fwd if kind == "value"]
    # Filter to only theorem targets (forwarding to a theorem)
    theorem_targets = [t for t in value_targets if t in decls and decls[t].kind == "theorem"]
    return ProofShapeInfo(
        forward_value_targets=value_targets,
        forward_theorem_targets=theorem_targets,
        n_forward_value=len(value_targets),
        n_forward_theorem=len(theorem_targets),
    )


def relative_path(abspath: str | None, root: Path) -> str | None:
    if abspath is None:
        return None
    try:
        return str(Path(abspath).relative_to(root))
    except ValueError:
        return abspath


def score_all(
    decls: dict[str, DeclInfo],
    forward: dict[str, list[tuple[str, str]]],
    reverse: dict[str, list[tuple[str, str]]],
    bridge_hints: list[str],
    strict_paths: list[str],
    root: Path,
) -> list[ScoredDecl]:
    results: list[ScoredDecl] = []
    reverse_use_profiles = build_reverse_use_profiles(reverse)
    structural_profiles = build_structural_profiles(decls, forward, reverse)

    for name, info in sorted(decls.items()):
        # Only score theorems
        if info.kind != "theorem":
            continue
        graph = build_graph_stats(
            name,
            forward,
            reverse,
            reverse_use=reverse_use_profiles.get(name),
            structural=structural_profiles.get(name),
        )
        proof = build_proof_shape(name, forward, decls)
        rel_file = relative_path(info.file, root)
        tags = classify_tags(info, graph, proof)
        exempt_attrs = sorted({attr for attr in info.attrs if attr in EXEMPT_ATTRS})
        if exempt_attrs:
            tags = sorted(set(tags + ["role-exempt"] + [f"attr:{attr}" for attr in exempt_attrs]))
        # Auto-generated theorems (eliminators, injection lemmas, etc.)
        # are tagged but exempt from violations — they are not authored proofs.
        if _is_generated(name):
            tags = sorted(set(tags + ["auto-generated"]))
            violations = []
        elif exempt_attrs:
            violations = []
        else:
            violations = compute_violations(info, tags, rel_file, bridge_hints, strict_paths)

        suspicion_score, suspicion_confidence, suspicion_factors = compute_vacuity_suspicion(
            info,
            graph,
            proof,
            tags,
            rel_file,
            bridge_hints,
            strict_paths,
        )

        results.append(ScoredDecl(
            name=name,
            kind=info.kind,
            file=rel_file,
            module=info.module,
            attrs=info.attrs,
            graph=graph,
            proof=proof,
            tags=tags,
            violations=violations,
            vacuity_suspicion_score=suspicion_score,
            vacuity_suspicion_confidence=suspicion_confidence,
            vacuity_suspicion_factors=suspicion_factors,
        ))
    return results


# ─── report generation ────────────────────────────────────────

def generate_json_report(scored: list[ScoredDecl]) -> list[dict]:
    return [s.to_dict() for s in scored]


def generate_md_report(scored: list[ScoredDecl]) -> str:
    lines: list[str] = []
    lines.append("# Theorem Vacuity Triage Report\n")

    # Summary stats
    total = len(scored)
    n_violations = sum(1 for s in scored if s.violations)
    n_errors = sum(1 for s in scored if any(v[0] == "error" for v in s.violations))
    n_warnings = sum(1 for s in scored if any(v[0] == "warning" for v in s.violations) and not any(v[0] == "error" for v in s.violations))
    n_clean = total - n_violations

    lines.append(f"**Theorems scored:** {total}  ")
    lines.append(f"**With violations:** {n_violations} ({n_errors} error, {n_warnings} warning-only)  ")
    lines.append(f"**Clean:** {n_clean}  \n")

    # Tag distribution
    tag_counts: Counter[str] = Counter()
    for s in scored:
        for t in s.tags:
            tag_counts[t] += 1
    lines.append("## Tag Distribution\n")
    lines.append("| Tag | Count |")
    lines.append("|-----|-------|")
    for tag, count in tag_counts.most_common():
        lines.append(f"| `{tag}` | {count} |")
    lines.append("")

    # Violation distribution
    viol_counts: Counter[str] = Counter()
    for s in scored:
        for _, code in s.violations:
            viol_counts[code] += 1
    lines.append("## Violation Distribution\n")
    lines.append("| Violation | Count |")
    lines.append("|-----------|-------|")
    for code, count in viol_counts.most_common():
        lines.append(f"| `{code}` | {count} |")
    lines.append("")

    # Derived ranking from structural + proof-shape evidence.
    lines.append("## Top Vacuity Suspicion (derived ranking)\n")
    lines.append("| Rank | Theorem | Suspicion | Confidence | Key Factors |")
    lines.append("|------|---------|----------:|-----------:|-------------|")
    ranked_suspicion = sorted(
        scored,
        key=lambda s: (
            -s.vacuity_suspicion_score,
            -s.vacuity_suspicion_confidence,
            s.name,
        ),
    )
    for idx, s in enumerate(ranked_suspicion[:20], start=1):
        top_factors = [
            str(factor["signal"])
            for factor in s.vacuity_suspicion_factors
            if float(factor["contribution"]) > 0
        ][:3]
        key_factors = ", ".join(f"`{signal}`" for signal in top_factors) if top_factors else "(none)"
        lines.append(
            f"| {idx} | `{s.name}` | {s.vacuity_suspicion_score:.4f} | "
            f"{s.vacuity_suspicion_confidence:.4f} | {key_factors} |"
        )
    lines.append("")

    # Structural metrics snapshot
    lines.append("## Structural Metrics (top 20 by transitive reverse reach)\n")
    lines.append("| Theorem | Reverse Reach | Descendant Mass | Depth | SCC Role | Public Fan-In | Proof-Only Reuse |")
    lines.append("|---------|--------------:|----------------:|------:|----------|---------------:|-----------------:|")
    ranked_structural = sorted(
        scored,
        key=lambda s: (
            -s.graph.transitive_reverse_reach,
            -s.graph.descendant_mass,
            -s.graph.depth,
            s.name,
        ),
    )
    for s in ranked_structural[:20]:
        lines.append(
            "| "
            f"`{s.name}` | "
            f"{s.graph.transitive_reverse_reach} | "
            f"{s.graph.descendant_mass} | "
            f"{s.graph.depth} | "
            f"`{s.graph.scc_role}` | "
            f"{s.graph.reverse_public_fan_in} | "
            f"{s.graph.reverse_proof_only_reuse} |"
        )
    lines.append("")

    # Errors (bridge/canonical files)
    errors = [s for s in scored if any(v[0] == "error" for v in s.violations)]
    if errors:
        lines.append("## Errors (require action)\n")
        # Group by file
        by_file: dict[str, list[ScoredDecl]] = defaultdict(list)
        for s in errors:
            by_file[s.file or "(unknown)"].append(s)
        for fpath in sorted(by_file):
            lines.append(f"### `{fpath}`\n")
            for s in by_file[fpath]:
                vcodes = ", ".join(f"`{v[1]}`" for v in s.violations if v[0] == "error")
                lines.append(f"- **`{s.name}`** — {vcodes}")
                if s.proof.exact_forward_target is not None:
                    lines.append(f"  - Forwards to: `{s.proof.exact_forward_target}`")
                lines.append(f"  - Tags: {', '.join(f'`{t}`' for t in s.tags)}")
            lines.append("")

    # Per-file summary (top 20 most-affected files)
    file_violation_count: Counter[str] = Counter()
    for s in scored:
        if s.violations and s.file:
            file_violation_count[s.file] += 1
    if file_violation_count:
        lines.append("## Most-Affected Files (top 20)\n")
        lines.append("| File | Violations |")
        lines.append("|------|------------|")
        for fpath, count in file_violation_count.most_common(20):
            lines.append(f"| `{fpath}` | {count} |")
        lines.append("")

    return "\n".join(lines)


# ─── main ─────────────────────────────────────────────────────

def main() -> None:
    root = repo_root()
    parser = argparse.ArgumentParser(description="Heuristic theorem vacuity triage")
    parser.add_argument("--decls", type=Path, default=root / "artifacts" / "dag" / "index" / "decls.jsonl")
    parser.add_argument("--edges", type=Path, default=root / "artifacts" / "dag" / "index" / "edges.jsonl")
    parser.add_argument("--out", type=Path, default=root / "reports" / "theorem-significance.json")
    parser.add_argument("--md", type=Path, default=root / "reports" / "theorem-significance.md")
    parser.add_argument("--strict-paths", nargs="*", default=STRICT_PATHS_DEFAULT)
    parser.add_argument("--bridge-hints", nargs="*", default=BRIDGE_HINTS_DEFAULT)
    args = parser.parse_args()

    print(f"Loading declarations from {args.decls} ...")
    decls = load_decls(args.decls)
    print(f"  {len(decls)} declarations loaded")

    print(f"Loading edges from {args.edges} ...")
    forward, reverse = load_edges(args.edges)
    n_edges = sum(len(v) for v in forward.values())
    print(f"  {n_edges} edges loaded")

    print("Scoring theorems ...")
    scored = score_all(decls, forward, reverse, args.bridge_hints, args.strict_paths, root)
    print(f"  {len(scored)} theorems scored")

    n_violations = sum(1 for s in scored if s.violations)
    n_errors = sum(1 for s in scored if any(v[0] == "error" for v in s.violations))
    print(f"  {n_violations} with violations ({n_errors} errors)")

    # Write JSON
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(generate_json_report(scored), f, indent=2)
    print(f"JSON report → {args.out}")

    # Write Markdown
    args.md.parent.mkdir(parents=True, exist_ok=True)
    with open(args.md, "w") as f:
        f.write(generate_md_report(scored))
    print(f"Markdown report → {args.md}")


if __name__ == "__main__":
    main()
