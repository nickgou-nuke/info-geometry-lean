#!/usr/bin/env python3
"""Apply externally produced Gibbs edge attention to a refactoring-map snapshot.

The program validates provenance and scores an already observed dependency
graph. It does not train a model or assign semantic labels. Sparse support is
explicit because a strictly positive softmax on every edge preserves SCCs.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

_REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(_REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPOSITORY_ROOT))

from tools.infra.graph_components import tarjan_scc


DEPENDENCY_KINDS = {"lean_source_import", "python_import", "test_import"}


def edge_reference(edge: dict[str, Any]) -> str:
    """Content-address one exact typed dependency witness from the map."""
    payload = json.dumps(edge, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _validate_map_and_scores(
    refactoring_map: dict[str, Any], score_packet: dict[str, Any]
) -> tuple[list[str], list[str], list[tuple[str, dict[str, Any], float]]]:
    if refactoring_map.get("schema") != "info_geometry.refactoring_map.v1":
        raise ValueError("unsupported refactoring-map schema")
    snapshot = refactoring_map.get("sourceSnapshot", {})
    if snapshot.get("worktreeConsistentDuringScan") is not True:
        raise ValueError("refactoring map is not a consistent worktree snapshot")
    snapshot_hash = snapshot.get("pathContentManifestSha256")
    if not isinstance(snapshot_hash, str) or not snapshot_hash:
        raise ValueError("refactoring map has no source snapshot hash")
    if score_packet.get("schema") != "info_geometry.edge_attention_logits.v1":
        raise ValueError("unsupported edge-attention score schema")
    if score_packet.get("sourceSnapshotSha256") != snapshot_hash:
        raise ValueError("edge-attention scores belong to a different source snapshot")
    if not score_packet.get("modelVersion") or not score_packet.get("featureVersion"):
        raise ValueError("edge-attention packet must identify model and feature versions")
    beta = score_packet.get("inverseTemperature")
    if isinstance(beta, bool) or not isinstance(beta, (int, float)) or not math.isfinite(beta) or beta <= 0:
        raise ValueError("inverseTemperature must be a finite positive number")

    edge_kinds = score_packet.get("edgeKinds", sorted(DEPENDENCY_KINDS))
    if (not isinstance(edge_kinds, list) or not edge_kinds
            or any(not isinstance(kind, str) or kind not in DEPENDENCY_KINDS
                   for kind in edge_kinds)
            or edge_kinds != sorted(set(edge_kinds))):
        raise ValueError("edgeKinds must be a non-empty sorted unique dependency-kind list")
    edge_kind_set = set(edge_kinds)

    vertices = sorted(
        str(row["path"]) for row in refactoring_map.get("files", []) if row.get("path")
    )
    vertex_set = set(vertices)
    witnessed: dict[str, dict[str, Any]] = {}
    for edge in refactoring_map.get("dependencyEdges", []):
        if (edge.get("kind") not in edge_kind_set
                or edge.get("from") not in vertex_set or edge.get("to") not in vertex_set):
            continue
        ref = edge_reference(edge)
        if ref in witnessed and witnessed[ref] != edge:
            raise ValueError("dependency edge reference collision")
        witnessed[ref] = edge

    logits: dict[str, float] = {}
    score_rows = score_packet.get("edges")
    if not isinstance(score_rows, list):
        raise ValueError("edge-attention packet must contain an edges list")
    for row in score_rows:
        if not isinstance(row, dict):
            raise ValueError("edge-attention edge entries must be objects")
        ref, logit = row.get("edgeRef"), row.get("logit")
        if not isinstance(ref, str) or ref not in witnessed:
            raise ValueError("edge-attention packet references an unknown dependency witness")
        if ref in logits:
            raise ValueError("duplicate edgeRef in edge-attention packet")
        if isinstance(logit, bool) or not isinstance(logit, (int, float)) or not math.isfinite(logit):
            raise ValueError("edge-attention logits must be finite numbers")
        for field in ("sourceDnaFingerprint", "targetDnaFingerprint"):
            value = row.get(field)
            if value is not None and (not isinstance(value, str) or len(value) != 64
                                      or any(char not in "0123456789abcdef" for char in value)):
                raise ValueError(f"{field} must be a lowercase SHA-256 digest")
        logits[ref] = float(logit)
    if set(logits) != set(witnessed):
        missing = len(set(witnessed) - set(logits))
        raise ValueError(
            f"edge-attention packet must score every scoped local dependency edge; {missing} missing"
        )
    return (vertices, edge_kinds,
            [(ref, edge, logits[ref]) for ref, edge in sorted(witnessed.items())])


def build_attention_scc_overlay(
    refactoring_map: dict[str, Any],
    score_packet: dict[str, Any],
    support_rule: dict[str, Any],
) -> dict[str, Any]:
    """Normalize per-source logits, sparsify by a declared rule, then condense."""
    vertices, edge_kinds, scored_edges = _validate_map_and_scores(refactoring_map, score_packet)
    beta = float(score_packet["inverseTemperature"])
    grouped: dict[str, list[tuple[str, dict[str, Any], float]]] = defaultdict(list)
    for row in scored_edges:
        grouped[str(row[1]["from"])].append(row)

    normalized: list[dict[str, Any]] = []
    normalized_by_source: dict[str, list[dict[str, Any]]] = defaultdict(list)
    score_rows_by_ref = {row["edgeRef"]: row for row in score_packet["edges"]}
    for source, rows in sorted(grouped.items()):
        # Center in logit space before multiplying by beta.  Multiplying raw
        # finite logits first can overflow to +inf, making ``inf - inf`` feed
        # NaN into the partition function.  Since beta is positive, this is
        # algebraically the same softmax shift.  Negative overflow/underflow
        # maps to zero mass, while at least one centered logit is exactly 0,
        # so the partition remains finite and nonzero.
        maximum_logit = max(logit for _, _, logit in rows)
        centered_scaled = [beta * (logit - maximum_logit)
                           for _, _, logit in rows]
        masses = [math.exp(value) for value in centered_scaled]
        partition = sum(masses)
        for (ref, edge, logit), mass in zip(rows, masses):
            factor = {
                "edgeRef": ref,
                "from": edge["from"],
                "to": edge["to"],
                "kind": edge["kind"],
                "logit": logit,
                "probability": mass / partition,
                "selected": False,
            }
            score_row = score_rows_by_ref[ref]
            for field in ("sourceDnaFingerprint", "targetDnaFingerprint"):
                if field in score_row:
                    factor[field] = score_row[field]
            for field in ("scoreComponents", "factorWeights"):
                if field in score_row:
                    factor[field] = score_row[field]
            normalized.append(factor)
            normalized_by_source[source].append(factor)

    # Each source's outgoing edge factors form a finite softmax state, just as
    # in the repo's AttentionKMSState owner.  Export state diagnostics before
    # support pruning: SCC sparsification is a separate navigation operation
    # and must not alter the underlying Gibbs distribution.
    source_attention_states: list[dict[str, Any]] = []
    for source in vertices:
        factors = normalized_by_source.get(source, [])
        if not factors:
            source_attention_states.append({
                "source": source,
                "status": "no_outgoing_edges",
                "outDegree": 0,
            })
            continue
        probabilities = [row["probability"] for row in factors]
        entropy = -math.fsum(
            probability * math.log(probability)
            for probability in probabilities if probability > 0.0
        )
        collision_probability = math.fsum(p * p for p in probabilities)
        source_attention_states.append({
            "source": source,
            "status": "normalized_finite_gibbs_state",
            "outDegree": len(factors),
            "normalizationSum": math.fsum(probabilities),
            "shannonEntropyNats": entropy,
            "normalizedEntropy": (
                min(1.0, max(0.0, entropy / math.log(len(factors))))
                if len(factors) > 1 else 0.0
            ),
            "perplexity": math.exp(entropy),
            "inverseSimpsonEffectiveSupport": 1.0 / collision_probability,
            "maxProbability": max(probabilities),
            # Floating point underflow can encode a mathematically positive
            # Gibbs mass as zero. Keep this distinct from graph support.
            "positiveFloatingSupportCount": sum(p > 0.0 for p in probabilities),
        })

    rule_kind = support_rule.get("kind")
    selected_refs: set[str] = set()
    if rule_kind == "top_k":
        k = support_rule.get("k")
        if isinstance(k, bool) or not isinstance(k, int) or k <= 0:
            raise ValueError("top_k support requires a positive integer k")
        for rows in normalized_by_source.values():
            # With one positive inverse temperature per source, Gibbs
            # probability is strictly increasing in the input logit. Rank in
            # logit space so distinct low-mass edges that underflow to the
            # same float probability do not get ordered by their hashes.
            ranked = sorted(rows, key=lambda row: (-row["logit"], row["edgeRef"]))
            selected_refs.update(row["edgeRef"] for row in ranked[:k])
    elif rule_kind == "minimum_probability":
        threshold = support_rule.get("threshold")
        if (isinstance(threshold, bool) or not isinstance(threshold, (int, float))
                or not math.isfinite(threshold) or not 0 < threshold <= 1):
            raise ValueError("minimum_probability support requires threshold in (0, 1]")
        selected_refs.update(
            row["edgeRef"] for row in normalized if row["probability"] >= threshold
        )
    else:
        raise ValueError("support kind must be top_k or minimum_probability")
    for row in normalized:
        row["selected"] = row["edgeRef"] in selected_refs

    raw_adjacency: dict[str, list[str]] = defaultdict(list)
    attention_adjacency: dict[str, list[str]] = defaultdict(list)
    by_ref = {row["edgeRef"]: row for row in normalized}
    for ref, edge, _ in scored_edges:
        raw_adjacency[edge["from"]].append(edge["to"])
        if ref in selected_refs:
            attention_adjacency[edge["from"]].append(edge["to"])
    raw_components = tarjan_scc(vertices, raw_adjacency)
    components = tarjan_scc(vertices, attention_adjacency)
    component_ids = [_component_id(component) for component in components]
    component_by_member = {
        member: component_id
        for component, component_id in zip(components, component_ids)
        for member in component
    }
    component_rows = [
        {"id": component_id, "members": component, "memberCount": len(component)}
        for component, component_id in zip(components, component_ids)
    ]
    quotient: dict[tuple[str, str], dict[str, Any]] = {}
    for row in normalized:
        if not row["selected"]:
            continue
        source_component = component_by_member[row["from"]]
        target_component = component_by_member[row["to"]]
        if source_component == target_component:
            continue
        key = (source_component, target_component)
        aggregate = quotient.setdefault(key, {
            "fromComponent": source_component,
            "toComponent": target_component,
            "edgeCount": 0,
            "probabilityMass": 0.0,
            "edgeRefs": [],
        })
        aggregate["edgeCount"] += 1
        aggregate["probabilityMass"] += row["probability"]
        aggregate["edgeRefs"].append(row["edgeRef"])

    return {
        "schema": "info_geometry.attention_scc_overlay.v1",
        "status": "model_derived_navigation_candidate",
        "sourceSnapshotSha256": refactoring_map["sourceSnapshot"]["pathContentManifestSha256"],
        "modelVersion": score_packet["modelVersion"],
        "featureVersion": score_packet["featureVersion"],
        "scorePacketProvenance": {
            key: score_packet[key] for key in (
                "encoderPacketSha256", "generationId", "generationManifestSha256",
                "scoreMethod", "trainingStatus", "authority", "factorWeights",
            ) if key in score_packet
        },
        "edgeKinds": edge_kinds,
        "inverseTemperature": beta,
        "supportRule": support_rule,
        "nodeCount": len(vertices),
        "observedDependencyEdgeCount": len(scored_edges),
        "selectedEdgeCount": len(selected_refs),
        "rawSccCount": len(raw_components),
        "attentionSccCount": len(components),
        "components": component_rows,
        "allEdgeFactors": normalized,
        "sourceAttentionStates": source_attention_states,
        "quotientEdges": [quotient[key] for key in sorted(quotient)],
        "authority": "source dependency witnesses plus supplied model logits; not semantic classification or proof evidence",
    }


def _component_id(members: list[str]) -> str:
    payload = json.dumps(members, ensure_ascii=False, separators=(",", ":"))
    return "scc_" + hashlib.sha256(payload.encode("utf-8")).hexdigest()[:20]


def _read_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return value


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("edge_logits", type=Path)
    parser.add_argument("--support", choices=("top-k", "minimum-probability"), required=True)
    parser.add_argument("--k", type=int)
    parser.add_argument("--threshold", type=float)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.support == "top-k":
        rule = {"kind": "top_k", "k": args.k}
    else:
        rule = {"kind": "minimum_probability", "threshold": args.threshold}
    result = build_attention_scc_overlay(
        _read_json(args.refactoring_map), _read_json(args.edge_logits), rule
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if args.out.suffix == ".gz":
        with gzip.open(args.out, "wt", encoding="utf-8") as stream:
            stream.write(encoded)
    else:
        args.out.write_text(encoded, encoding="utf-8")
    print(json.dumps({key: result[key] for key in (
        "schema", "nodeCount", "observedDependencyEdgeCount", "selectedEdgeCount",
        "rawSccCount", "attentionSccCount", "sourceSnapshotSha256",
    )}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
