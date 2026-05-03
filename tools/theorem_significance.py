#!/usr/bin/env python3
"""
⚖️ THE PAULI SIGNIFICANCE AUDITOR (Authority-Grounded)
Truth lives in Lean; structure lives in the graph.

This script replaces legacy lexical heuristics with formal topological evidence.
A theorem is considered significant if it possesses 'Causal Mass'—defined by
transitive downstream support and depth in the formal dependency DAG.
"""

from __future__ import annotations

import json
import os
import sys
from collections import Counter, defaultdict, deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    # Insert repository root so `tools.*` imports resolve when executed as a script.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from tools.infra.decl_graph_support import load_decl_graph
    from tools.pathing import repo_root
else:
    from tools.infra.decl_graph_support import load_decl_graph
    from tools.pathing import repo_root


BRIDGE_HINTS_DEFAULT = ("bridge", "Bridge")
STRICT_PATHS_DEFAULT = ("lean/InfoGeometry",)


@dataclass(frozen=True)
class DeclInfo:
    name: str
    kind: str
    file: str
    module: str | None = None
    line: int = 0
    attrs: list[str] = field(default_factory=list)


@dataclass(frozen=True)
class ProofShape:
    is_exact_forward: bool
    exact_forward_target: str | None


@dataclass(frozen=True)
class GraphSignals:
    transitive_reverse_reach: int = 0
    reverse_public_fan_in: int = 0
    reverse_proof_only_reuse: int = 0
    depth: int = 0
    descendant_mass: int = 0
    scc_size: int = 1
    scc_role: str = "acyclic"


@dataclass(frozen=True)
class BridgeEvidence:
    semantic_expr_count: int = 0
    fingerprint_match_count: int = 0
    provenance_counts: Counter[str] = field(default_factory=Counter)


@dataclass
class ScoreEntry:
    name: str
    kind: str
    file: str
    tags: list[str]
    violations: list[tuple[str, str]]
    graph: GraphSignals
    vacuity_suspicion_score: float = 0.0
    vacuity_suspicion_confidence: float = 0.0
    vacuity_suspicion_factors: list[dict[str, Any]] = field(default_factory=list)
    bridge_semantic_evidence_count: int = 0
    bridge_fingerprint_match_count: int = 0


def build_proof_shape(
    name: str,
    forward: dict[str, list[tuple[str, str]]],
    decls: dict[str, DeclInfo],
) -> ProofShape:
    value_edges = [(dst, kind) for dst, kind in forward.get(name, []) if kind == "value"]
    if len(value_edges) != 1:
        return ProofShape(False, None)
    dst = value_edges[0][0]
    if dst not in decls:
        return ProofShape(False, None)
    if len(forward.get(name, [])) != 1:
        return ProofShape(False, None)
    return ProofShape(True, dst)


def _is_generated(name: str) -> bool:
    return any(token in name for token in (".rec", ".recOn", ".casesOn", ".match_", ".proof_", "._"))


def _is_role_exempt(decl: DeclInfo) -> bool:
    return bool({"terminal", "role_exempt", "role-exempt"} & set(decl.attrs))


def _in_strict_path(file: str, strict_paths: tuple[str, ...] | list[str]) -> bool:
    return any(file.startswith(prefix) for prefix in strict_paths)


def _is_bridge_file(file: str, bridge_hints: tuple[str, ...] | list[str]) -> bool:
    stem = Path(file).stem
    return any(hint.lower() in stem.lower() for hint in bridge_hints)


def _is_certified_surface(name: str) -> bool:
    leaf = name.rsplit(".", 1)[-1]
    return leaf.startswith("certified") or ".certified" in name or ".Certified" in name or name.startswith("Certified")


def _uncertified_twin_name(name: str) -> str | None:
    leaf = name.rsplit(".", 1)[-1]
    prefix = name[: -len(leaf)]
    if leaf.startswith("certified") and len(leaf) > len("certified"):
        tail = leaf[len("certified") :]
        return prefix + tail[:1].lower() + tail[1:]
    return None


def _reachable(start: str, adjacency: dict[str, list[tuple[str, str]]]) -> set[str]:
    seen: set[str] = set()
    queue = deque([start])
    while queue:
        cur = queue.popleft()
        for nxt, _kind in adjacency.get(cur, []):
            if nxt in seen:
                continue
            seen.add(nxt)
            queue.append(nxt)
    seen.discard(start)
    return seen


def _longest_reverse_depth(name: str, reverse: dict[str, list[tuple[str, str]]]) -> int:
    def go(cur: str, active: set[str]) -> int:
        best = 0
        for nxt, _kind in reverse.get(cur, []):
            if nxt in active:
                continue
            best = max(best, 1 + go(nxt, active | {nxt}))
        return best

    return go(name, {name})


def _scc_sizes(names: set[str], forward: dict[str, list[tuple[str, str]]]) -> dict[str, int]:
    graph = {n: [dst for dst, _kind in forward.get(n, []) if dst in names] for n in names}
    rev: dict[str, list[str]] = {n: [] for n in names}
    for src, dsts in graph.items():
        for dst in dsts:
            rev.setdefault(dst, []).append(src)

    order: list[str] = []
    seen: set[str] = set()

    def dfs(n: str) -> None:
        seen.add(n)
        for m in graph.get(n, []):
            if m not in seen:
                dfs(m)
        order.append(n)

    for n in names:
        if n not in seen:
            dfs(n)

    sizes: dict[str, int] = {}

    def rdfs(n: str, comp: list[str]) -> None:
        seen.add(n)
        comp.append(n)
        for m in rev.get(n, []):
            if m not in seen:
                rdfs(m, comp)

    seen.clear()
    for n in reversed(order):
        if n in seen:
            continue
        comp: list[str] = []
        rdfs(n, comp)
        for item in comp:
            sizes[item] = len(comp)
    return sizes


def _graph_signals(
    name: str,
    decls: dict[str, DeclInfo],
    forward: dict[str, list[tuple[str, str]]],
    reverse: dict[str, list[tuple[str, str]]],
    scc_sizes: dict[str, int],
) -> GraphSignals:
    rev_edges = reverse.get(name, [])
    reverse_public_fan_in = sum(1 for _src, kind in rev_edges if kind == "type")
    reverse_proof_only_reuse = sum(1 for _src, kind in rev_edges if kind == "value")
    scc_size = scc_sizes.get(name, 1)
    return GraphSignals(
        transitive_reverse_reach=len(_reachable(name, reverse)),
        reverse_public_fan_in=reverse_public_fan_in,
        reverse_proof_only_reuse=reverse_proof_only_reuse,
        depth=_longest_reverse_depth(name, reverse),
        descendant_mass=len(_reachable(name, forward)),
        scc_size=scc_size,
        scc_role="cycle-island" if scc_size > 1 else "acyclic",
    )


def _vacuity_score(
    *,
    decl: DeclInfo,
    shape: ProofShape,
    graph: GraphSignals,
    tags: list[str],
    bridge_evidence: BridgeEvidence | None,
) -> tuple[float, float, list[dict[str, Any]]]:
    factors: list[dict[str, Any]] = []
    score = 0.0
    if "auto-generated" in tags:
        factors.append({"signal": "policy.auto-generated-exempt", "weight": -1.0})
        return 0.0, 1.0, factors
    if "role-exempt" in tags:
        factors.append({"signal": "policy.role-exempt", "weight": -1.0})
        return 0.0, 1.0, factors
    if shape.is_exact_forward:
        score += 3.0
        factors.append({"signal": "shape.exact-forward", "weight": 3.0})
    if graph.reverse_public_fan_in == 0:
        score += 0.5
        factors.append({"signal": "graph.no-public-reuse", "weight": 0.5})
    if graph.depth <= 1:
        score += 0.5
        factors.append({"signal": "graph.shallow", "weight": 0.5})
    if bridge_evidence and bridge_evidence.semantic_expr_count:
        boost = min(2.0, float(bridge_evidence.semantic_expr_count))
        score += boost
        factors.append({"signal": "bridge.semantic-expr-evidence", "weight": boost})
    confidence = min(1.0, score / 5.0) if score > 0 else 0.0
    return score, confidence, factors


def score_all(
    decls: dict[str, DeclInfo],
    forward: dict[str, list[tuple[str, str]]],
    reverse: dict[str, list[tuple[str, str]]],
    bridge_hints: tuple[str, ...] | list[str],
    strict_paths: tuple[str, ...] | list[str],
    root: Path,
    *,
    bridge_evidence_by_file: dict[str, BridgeEvidence] | None = None,
    bridge_evidence_by_decl: dict[str, BridgeEvidence] | None = None,
) -> list[ScoreEntry]:
    bridge_evidence_by_file = bridge_evidence_by_file or {}
    bridge_evidence_by_decl = bridge_evidence_by_decl or {}
    scc_sizes = _scc_sizes(set(decls), forward)
    scored: list[ScoreEntry] = []

    for name, decl in decls.items():
        tags: list[str] = []
        violations: list[tuple[str, str]] = []
        graph = _graph_signals(name, decls, forward, reverse, scc_sizes)
        shape = build_proof_shape(name, forward, decls)

        if _is_generated(name):
            tags.append("auto-generated")
        if _is_role_exempt(decl):
            tags.append("role-exempt")

        if shape.is_exact_forward:
            tags.append("wrapper-candidate")
            severity = "error" if _is_bridge_file(decl.file, bridge_hints) else "warning"
            violations.append((severity, "V1/public-wrapper-inflation"))
            if severity == "error":
                violations.append(("warning", "V4/bridge-infrastructure-promoted"))

        if (
            decl.kind == "theorem"
            and not reverse.get(name)
            and not forward.get(name)
            and _in_strict_path(decl.file, strict_paths)
            and "auto-generated" not in tags
            and "role-exempt" not in tags
        ):
            tags.append("dead-candidate")
            violations.append(("error", "V2/dead-public-theorem"))

        if _is_certified_surface(name):
            tags.append("certified-surface")
            twin = _uncertified_twin_name(name)
            forward_targets = {dst for dst, kind in forward.get(name, []) if kind == "value"}
            targets_all_certified = bool(forward_targets) and all(_is_certified_surface(dst) for dst in forward_targets)
            alias_to_uncertified = twin in forward_targets if twin else False
            public_reused = bool(reverse.get(name))
            if alias_to_uncertified or (public_reused and not targets_all_certified):
                if name.endswith("_eq_" + (twin or "\0")) or alias_to_uncertified or public_reused:
                    tags.append("certification-transport")
                tags.append("certification-wash-candidate")
                violations.append(("error", "V5/certification-wash"))

        if "auto-generated" in tags or "role-exempt" in tags:
            violations = []

        evidence = bridge_evidence_by_decl.get(name) or bridge_evidence_by_file.get(decl.file) or BridgeEvidence()
        vac_score, vac_conf, vac_factors = _vacuity_score(
            decl=decl,
            shape=shape,
            graph=graph,
            tags=tags,
            bridge_evidence=evidence,
        )
        scored.append(
            ScoreEntry(
                name=name,
                kind=decl.kind,
                file=decl.file,
                tags=tags,
                violations=violations,
                graph=graph,
                vacuity_suspicion_score=vac_score,
                vacuity_suspicion_confidence=vac_conf,
                vacuity_suspicion_factors=vac_factors,
                bridge_semantic_evidence_count=evidence.semantic_expr_count,
                bridge_fingerprint_match_count=evidence.fingerprint_match_count,
            )
        )
    return scored


def _count_bridge_evidence(payload: dict[str, Any]) -> BridgeEvidence:
    semantic = 0
    fingerprint = 0
    provenance: Counter[str] = Counter()

    def visit(obj: Any) -> None:
        nonlocal semantic, fingerprint
        if isinstance(obj, dict):
            source = obj.get("fingerprintSource")
            if source == "exprSemantic":
                semantic += 1
            if obj.get("fingerprintV1"):
                fingerprint += 1
            prov = obj.get("classificationProvenance")
            if isinstance(prov, str) and prov:
                provenance[prov] += 1
            for value in obj.values():
                visit(value)
        elif isinstance(obj, list):
            for value in obj:
                visit(value)

    visit(payload)
    return BridgeEvidence(semantic, fingerprint, provenance)


def _payload_file(payload: dict[str, Any]) -> str | None:
    request = payload.get("request", {}) if isinstance(payload.get("request"), dict) else {}
    file_value = request.get("file") or payload.get("file")
    if isinstance(file_value, str) and file_value:
        return file_value
    meta = payload.get("responseMeta", {}) if isinstance(payload.get("responseMeta"), dict) else {}
    session = meta.get("sessionId", {})
    if isinstance(session, dict) and isinstance(session.get("value"), str):
        return session["value"]
    return None


def _repo_relative_file(file_value: str, root: Path) -> str:
    if file_value.startswith("file://"):
        path = Path(file_value.removeprefix("file://"))
    else:
        path = Path(file_value)
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except Exception:
        return file_value


def load_bridge_evidence_index(
    paths: list[Path],
    root: Path,
    decls: dict[str, DeclInfo],
) -> tuple[dict[str, BridgeEvidence], dict[str, BridgeEvidence]]:
    by_decl: dict[str, BridgeEvidence] = {}
    by_file: dict[str, BridgeEvidence] = {}
    decls_by_file: dict[str, list[DeclInfo]] = defaultdict(list)
    for decl in decls.values():
        decls_by_file[decl.file].append(decl)
    for rows in decls_by_file.values():
        rows.sort(key=lambda d: d.line)

    for path in paths:
        payload = json.loads(path.read_text(encoding="utf-8"))
        evidence = _count_bridge_evidence(payload)
        file_value = _payload_file(payload)
        if not file_value:
            continue
        rel_file = _repo_relative_file(file_value, root)
        by_file[rel_file] = evidence

        request = payload.get("request", {}) if isinstance(payload.get("request"), dict) else {}
        line = request.get("line")
        if isinstance(line, int):
            candidates = [d for d in decls_by_file.get(rel_file, []) if d.line <= line]
            if candidates:
                by_decl[candidates[-1].name] = evidence

    return by_decl, by_file

def main() -> int:
    root = repo_root()
    
    # 1. Load the ground truth from Pauli Authority (ArangoDB or local artifacts)
    print("[pauli-audit] Loading truthful graph mass from Pauli Authority...")
    decl_key_to_full, profiles = load_decl_graph(root)
    
    if not profiles:
        print("[pauli-audit] ERROR: Pauli Authority is unreachable or graph is empty.")
        return 1

    print(f"[pauli-audit] Analysing {len(profiles)} declarations for formal significance...")

    significant: list[dict] = []
    vacuous: list[dict] = []
    deep_identifications: list[dict] = []

    for name, p in profiles.items():
        # Heuristic exclusion: noise labels (match_, proof_, etc)
        if any(x in name for x in [".match_", ".proof_", "._"]):
            continue

        # SIGNANCE METRIC 1: Causal Mass (Transitive Downstream Support)
        mass = p.descendant_mass
        
        # SIGNANCE METRIC 2: Linkage Depth
        depth = p.depth

        # JUDGMENT: Deep Identification
        if p.structural_role in ("supported_theorem", "load_bearing") and depth > 5:
            deep_identifications.append({
                "name": name,
                "mass": mass,
                "depth": depth,
                "role": p.structural_role
            })

        # JUDGMENT: Actual Vacuity
        if mass == 0 and p.reverse_value_users == 0 and p.structural_role == "isolated_theorem":
            vacuous.append({
                "name": name,
                "file": p.file,
                "line": p.line
            })
        elif mass > 10 or p.reverse_public_fan_in > 5:
            significant.append({
                "name": name,
                "mass": mass,
                "depth": depth,
                "fan_in": p.reverse_public_fan_in
            })

    # 2. Render the Truthful Verdict
    md_lines = [
        "# ⚖️ Pauli Authority Audit: Truthful Significance Index",
        "",
        "> **Protocol:** Truth lives in Lean; structure lives in the graph.",
        f"> **Snapshot:** {len(profiles)} declarations analysed via Pauli Authority.",
        "",
        "## 💎 High Causal Mass (The Spire's Pillars)",
        "| Declaration | Causal Mass | Depth | Fan-In |",
        "| :--- | :---: | :---: | :---: |"
    ]
    
    significant.sort(key=lambda x: x["mass"], reverse=True)
    for s in significant[:50]:
        md_lines.append(f"| `{s['name']}` | {s['mass']} | {s['depth']} | {s['fan_in']} |")

    md_lines.extend([
        "",
        "## 🧬 Deep Identifications (Algebraic Unifications)",
        "| Milestone | Mass | Depth |",
        "| :--- | :---: | :---: |"
    ])
    
    deep_identifications.sort(key=lambda x: x["depth"], reverse=True)
    for d in deep_identifications[:20]:
        md_lines.append(f"| `{d['name']}` | {d['mass']} | {d['depth']} |")

    md_lines.extend([
        "",
        "## 🗑️ Confirmed Vacuity (Pruning Candidates)",
        "| Vacuous Declaration | Location |",
        "| :--- | :--- |"
    ])
    
    for v in vacuous[:30]:
        md_lines.append(f"| `{v['name']}` | `{v['file']}:{v['line']}` |")

    report_path = root / "reports" / "theorem-significance.md"
    report_path.write_text("\n".join(md_lines), encoding="utf-8")

    json_path = root / "reports" / "theorem-significance.json"
    json_payload: list[dict[str, Any]] = []
    for name, p in profiles.items():
        json_payload.append(
            {
                "name": name,
                "kind": p.kind,
                "file": p.file,
                "line": p.line,
                "structural_role": p.structural_role,
                "reverse_public_fan_in": p.reverse_public_fan_in,
                "reverse_theorem_users": p.reverse_theorem_users,
                "reverse_value_users": p.reverse_value_users,
                "reverse_type_users": p.reverse_type_users,
                "descendant_mass": p.descendant_mass,
                "transitive_reverse_reach": p.transitive_reverse_reach,
                "depth": p.depth,
                "scc_size": p.scc_size,
                "is_sink": p.is_sink,
                "classification_basis": "graph-topology",
                "graph_grounded_signal": True,
                "heuristic_signal": False,
                "hard_verdict_allowed": True,
            }
        )
    json_path.write_text(json.dumps(json_payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    print(f"[pauli-audit] Formal audit complete. Wrote {report_path.relative_to(root)}")
    print(f"[pauli-audit] Machine report: {json_path.relative_to(root)}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
