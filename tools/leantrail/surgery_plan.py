#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
import sys
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

try:
    import networkx as nx
except Exception as exc:  # pragma: no cover
    raise SystemExit("surgery_plan.py requires networkx. Install it in the repo Python environment.") from exc

from leantrail.backend.models import GraphSnapshot
from tools.leantrail.adapters import load_snapshot

ROLE_PRIORITY = [
    "contaminated",
    "protected",
    "exported",
    "unknown",
    "gate",
    "orphan_genuine",
    "closure_debt",
    "translator",
    "pure_conductor",
    "fake_transport",
    "dead_socket",
]

VACUUM_ROLES_FOR_CONTRACTION = {"fake_transport", "pure_conductor"}
META_EDGE_KINDS = {"contains"}
DEPENDENCY_EDGE_KINDS = {"depends_type", "depends_value", "type", "value"}


def _sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    if not path.exists():
        return ""
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return "sha256:" + h.hexdigest()


def _iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            s = raw.strip()
            if not s:
                continue
            obj = json.loads(s)
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")


def _get_nested(obj: dict[str, Any], path: str, default: Any = None) -> Any:
    cur: Any = obj
    for part in path.split("."):
        if not isinstance(cur, dict) or part not in cur:
            return default
        cur = cur[part]
    return cur


def _as_bool(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() in {"1", "true", "yes"}
    return bool(value)


def _stable_packet_id(prefix: str, *parts: str) -> str:
    seed = "|".join(parts)
    return f"{prefix}_{hashlib.sha1(seed.encode('utf-8')).hexdigest()[:24]}"


def build_dependency_graph(snapshot: GraphSnapshot) -> nx.DiGraph:
    g = nx.DiGraph()
    for node in snapshot.nodes:
        if node.kind == "Declaration":
            g.add_node(node.id)
    for edge in snapshot.edges:
        if edge.kind in META_EDGE_KINDS:
            continue
        if edge.kind not in DEPENDENCY_EDGE_KINDS:
            continue
        if edge.src in g and edge.dst in g:
            g.add_edge(edge.src, edge.dst, kind=edge.kind)
    return g


def scc_maps(g: nx.DiGraph) -> tuple[dict[str, int], dict[int, set[str]], nx.DiGraph, dict[int, int], dict[int, int]]:
    comps = list(nx.strongly_connected_components(g))
    scc_of: dict[str, int] = {}
    members: dict[int, set[str]] = {}
    for idx, comp in enumerate(comps):
        members[idx] = set(comp)
        for n in comp:
            scc_of[n] = idx
    dag = nx.condensation(g, scc=comps)
    topo = list(nx.topological_sort(dag)) if nx.is_directed_acyclic_graph(dag) else list(dag.nodes)
    topo_rank = {node: i for i, node in enumerate(topo)}
    reverse_rank = {node: len(topo) - i - 1 for i, node in enumerate(topo)}
    return scc_of, members, dag, topo_rank, reverse_rank


def lift_scc_role(member_nodes: list[dict[str, Any]]) -> str:
    roles: set[str] = set()
    for member in member_nodes:
        if _as_bool(member.get("is_protected")) or _as_bool(_get_nested(member, "attrs.surgery.protected", False)):
            roles.add("protected")
            continue
        if _as_bool(member.get("is_exported")) or _as_bool(_get_nested(member, "attrs.surgery.exported", False)):
            roles.add("exported")
            continue
        role = str(_get_nested(member, "attrs.vacuity.role", "unknown") or "unknown")
        contam = str(_get_nested(member, "attrs.contamination.state", "clean") or "clean")
        if contam == "honest_sorry":
            roles.add("closure_debt")
        elif contam != "clean":
            roles.add("contaminated")
        else:
            roles.add(role)
    for role in ROLE_PRIORITY:
        if role in roles:
            return role
    return "unknown"


def protected_by_surgery_lock(target: str, locks: list[dict[str, Any]]) -> bool:
    for row in locks:
        state = str(row.get("state", "")).strip()
        scope = str(row.get("scope", "decl")).strip()
        if scope in {"decl", "node"} and str(row.get("target", "")).strip() == target:
            if state in {"protected", "quarantine", "manual_refactor_required", "rejected"}:
                return True
    return False


def source_patch_ok(attrs: dict[str, Any]) -> bool:
    sp = attrs.get("source_patch", {}) if isinstance(attrs.get("source_patch", {}), dict) else {}
    return (
        sp.get("decl_span_kind") == "top_level_decl"
        and sp.get("patch_span_kind") == "decl_body"
        and sp.get("source_info_kind") == "original"
    )


def replacement_for(node_attrs: dict[str, Any]) -> str:
    for path in (
        "surgery.replacement",
        "surgery.replacement_candidate",
        "vacuity.replacement",
        "vacuity.replacement_candidate",
        "source_patch.replacement",
    ):
        value = str(_get_nested(node_attrs, f"attrs.{path}", "") or "") if "attrs" in node_attrs else ""
        if value:
            return value
    # Called with attrs usually, not full node dict.
    for path in (
        "surgery.replacement",
        "surgery.replacement_candidate",
        "vacuity.replacement",
        "vacuity.replacement_candidate",
        "source_patch.replacement",
    ):
        value = str(_get_nested(node_attrs, path, "") or "")
        if value:
            return value
    return ""


def build_packet_envelope(
    *,
    stream: str,
    action_phase: str,
    state: str,
    target: str,
    node: Any,
    attrs: dict[str, Any],
    scc_id: int,
    scc_size: int,
    topo_rank: int,
    reverse_topo_rank: int,
    snapshot_hash: str,
    audit_hash: str,
    priority: float,
    payload: dict[str, Any],
) -> dict[str, Any]:
    sp = attrs.get("source_patch", {}) if isinstance(attrs.get("source_patch", {}), dict) else {}
    cert_ref = str(_get_nested(attrs, "vacuity_ingest.certificate_ref", "") or _get_nested(attrs, "vacuity.certificate_ref", ""))
    sig = str(_get_nested(attrs, "alignment.signature_class", "") or _get_nested(attrs, "vacuity.signature_class", ""))
    return {
        "packet_id": _stable_packet_id(stream[0] + "p", stream, action_phase, target, snapshot_hash),
        "packet_stream": stream,
        "action_phase": action_phase,
        "state": state,
        "target": target,
        "module": node.module,
        "file": node.file,
        "scc_id": f"scc_{scc_id}",
        "scc_size": scc_size,
        "signature_class": sig,
        "priority_score": float(priority),
        "certificate_ref": cert_ref,
        "snapshot_hash": snapshot_hash,
        "audit_hash": audit_hash or str(_get_nested(attrs, "vacuity_ingest.audit_hash", "")),
        "toolchain": node.toolchain,
        "commit_sha": node.commit_sha,
        "decl_span_kind": sp.get("decl_span_kind", "unknown"),
        "patch_span_kind": sp.get("patch_span_kind", "unsupported"),
        "source_info_kind": sp.get("source_info_kind", "synthetic/none"),
        "topo_rank": int(topo_rank),
        "reverse_topo_rank": int(reverse_topo_rank),
        "protected": bool(_get_nested(attrs, "surgery.protected", False)),
        "certificate_stale": bool(_get_nested(attrs, "vacuity_ingest.certificate_stale", False)),
        "payload": payload,
    }


def plan(snapshot_path: Path, locks_path: Path | None = None) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    snapshot = load_snapshot(snapshot_path)
    snapshot_hash = _sha256_file(snapshot_path)
    locks = _iter_jsonl(locks_path) if locks_path else []
    g = build_dependency_graph(snapshot)
    scc_of, members, _dag, topo_rank_by_scc, reverse_rank_by_scc = scc_maps(g)
    node_by_id = {n.id: n for n in snapshot.nodes if n.kind == "Declaration"}

    scc_role: dict[int, str] = {}
    for sid, names in members.items():
        raw = [node_by_id[n].to_dict() for n in names if n in node_by_id]
        scc_role[sid] = lift_scc_role(raw)

    vacuum: list[dict[str, Any]] = []
    bridge: list[dict[str, Any]] = []
    alignment: list[dict[str, Any]] = []
    proof_holes: list[dict[str, Any]] = []
    role_counts: Counter[str] = Counter()
    contamination_counts: Counter[str] = Counter()
    source_patch_counts: Counter[str] = Counter()
    vacuity_evidence_nodes = 0

    for node in snapshot.nodes:
        if node.kind != "Declaration":
            continue
        attrs = node.attrs if isinstance(node.attrs, dict) else {}
        role = str(_get_nested(attrs, "vacuity.role", "unknown") or "unknown")
        contamination = str(_get_nested(attrs, "contamination.state", "clean") or "clean")
        if isinstance(attrs.get("vacuity"), dict):
            vacuity_evidence_nodes += 1
        role_counts[role] += 1
        contamination_counts[contamination] += 1
        sp_for_count = attrs.get("source_patch", {}) if isinstance(attrs.get("source_patch", {}), dict) else {}
        source_patch_counts[
            "|".join([
                str(sp_for_count.get("decl_span_kind", "unknown")),
                str(sp_for_count.get("patch_span_kind", "unknown")),
                str(sp_for_count.get("source_info_kind", "unknown")),
            ])
        ] += 1
        is_prop = bool(_get_nested(attrs, "vacuity.is_prop", False))
        sid = scc_of.get(node.id, -1)
        scc_size = len(members.get(sid, {node.id})) if sid >= 0 else 1
        tr = topo_rank_by_scc.get(sid, 0)
        rr = reverse_rank_by_scc.get(sid, 0)
        priority = float(_get_nested(attrs, "vacuity.priority_score", 0.0) or 0.0)
        if priority == 0.0:
            priority = float(_get_nested(attrs, "vacuity.term_node_count", 0) or 0)

        if protected_by_surgery_lock(node.id, locks):
            continue
        if role == "closure_debt" or contamination == "honest_sorry":
            proof_holes.append(build_packet_envelope(
                stream="proof_hole",
                action_phase="quarantine",
                state="proposed",
                target=node.id,
                node=node,
                attrs=attrs,
                scc_id=sid,
                scc_size=scc_size,
                topo_rank=tr,
                reverse_topo_rank=rr,
                snapshot_hash=snapshot_hash,
                audit_hash=str(_get_nested(attrs, "vacuity_ingest.audit_hash", "")),
                priority=priority,
                payload={
                    "hole_kind": "explicit_sorry",
                    "honest": True,
                    "target_cluster_root": node.id,
                    "suggested_action": "prove_or_route_honest_sorry",
                    "release_blocking": True,
                    "dev_allowed": True,
                    "delete_old_surface": False,
                    "contamination": contamination,
                    "allowed_next_actions": [
                        "prove the declaration without sorry",
                        "replace with approved theorem",
                        "keep as explicit closure debt",
                        "open bridge obligation",
                    ],
                },
            ))
            continue

        if scc_role.get(sid) in {"contaminated", "protected", "exported", "unknown"}:
            if contamination != "clean":
                bridge.append(build_packet_envelope(
                    stream="bridge",
                    action_phase="bridge",
                    state="proposed",
                    target=node.id,
                    node=node,
                    attrs=attrs,
                    scc_id=sid,
                    scc_size=scc_size,
                    topo_rank=tr,
                    reverse_topo_rank=rr,
                    snapshot_hash=snapshot_hash,
                    audit_hash=str(_get_nested(attrs, "vacuity_ingest.audit_hash", "")),
                    priority=priority,
                    payload={
                        "bridge_kind": "axiom_bridge",
                        "target_cluster_root": node.id,
                        "suggested_action": "open_bridge_obligation",
                        "delete_old_surface": False,
                        "contamination": contamination,
                    },
                ))
            continue

        if role == "orphan_genuine":
            bridge.append(build_packet_envelope(
                stream="bridge",
                action_phase="bridge",
                state="proposed",
                target=node.id,
                node=node,
                attrs=attrs,
                scc_id=sid,
                scc_size=scc_size,
                topo_rank=tr,
                reverse_topo_rank=rr,
                snapshot_hash=snapshot_hash,
                audit_hash=str(_get_nested(attrs, "vacuity_ingest.audit_hash", "")),
                priority=priority,
                payload={
                    "bridge_kind": "orphan_genuine_reconnect",
                    "target_cluster_root": node.id,
                    "suggested_action": "expose_in_public_api",
                    "delete_old_surface": False,
                },
            ))
            continue

        if role in VACUUM_ROLES_FOR_CONTRACTION:
            replacement = replacement_for(attrs)
            if not replacement:
                continue
            if not is_prop:
                continue
            if contamination != "clean":
                continue
            if scc_size != 1:
                continue
            state = "certified" if source_patch_ok(attrs) else "manual_refactor_required"
            reason = "" if state == "certified" else "source_patch_not_safe"
            sp = attrs.get("source_patch", {}) if isinstance(attrs.get("source_patch", {}), dict) else {}
            vacuum.append(build_packet_envelope(
                stream="vacuum",
                action_phase="contract",
                state=state,
                target=node.id,
                node=node,
                attrs=attrs,
                scc_id=sid,
                scc_size=scc_size,
                topo_rank=tr,
                reverse_topo_rank=rr,
                snapshot_hash=snapshot_hash,
                audit_hash=str(_get_nested(attrs, "vacuity_ingest.audit_hash", "")),
                priority=priority,
                payload={
                    "role": role,
                    "replacement": replacement,
                    "rewrite_mode": "replace_decl_body",
                    "replacement_body": str(sp.get("replacement_text", "") or f"by exact {replacement}"),
                    "destructive": False,
                    "reason": reason,
                    "source_patch": sp,
                },
            ))
            continue

        # Alignment lane: emit candidates only when another pipeline has attached overlap candidates.
        hodge = attrs.get("hodge", {}) if isinstance(attrs.get("hodge", {}), dict) else {}
        for cand in hodge.get("forest_overlap_candidates", []) if isinstance(hodge.get("forest_overlap_candidates", []), list) else []:
            target = str(cand.get("target", "")).strip()
            if not target:
                continue
            alignment.append(build_packet_envelope(
                stream="alignment",
                action_phase="align",
                state="proposed",
                target=node.id,
                node=node,
                attrs=attrs,
                scc_id=sid,
                scc_size=scc_size,
                topo_rank=tr,
                reverse_topo_rank=rr,
                snapshot_hash=snapshot_hash,
                audit_hash=str(_get_nested(attrs, "vacuity_ingest.audit_hash", "")),
                priority=float(cand.get("overlap_score", 0.0)),
                payload={
                    "packet_type": "isomorphic_alignment",
                    "source_decl": node.id,
                    "target_decl": target,
                    "signature_level": "hodge_forest_overlap",
                    "source_signature_hash": str(hodge.get("dependency_forest_hash", "")),
                    "target_signature_hash": str(cand.get("target_forest_hash", "")),
                    "suggested_action": "deprecate_and_route",
                    "kernel_obligation": {"mode": "temporary_theorem", "must_typecheck": True, "proof_template": ""},
                },
            ))

    return vacuum, bridge, alignment, proof_holes, {
        "snapshot": str(snapshot_path),
        "snapshot_hash": snapshot_hash,
        "nodes": len(snapshot.nodes),
        "edges": len(snapshot.edges),
        "vacuity_evidence_nodes": vacuity_evidence_nodes,
        "role_counts": dict(sorted(role_counts.items())),
        "contamination_counts": dict(sorted(contamination_counts.items())),
        "source_patch_counts": dict(source_patch_counts.most_common(20)),
        "vacuum_packets": len(vacuum),
        "bridge_packets": len(bridge),
        "alignment_packets": len(alignment),
        "proof_hole_packets": len(proof_holes),
    }


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Generate LeanTrail v1.3 surgery packet streams from a vacuity-enriched snapshot, including honest-sorry proof-hole packets.")
    p.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.vacuity.json")
    p.add_argument("--surgery-locks", default="artifacts/leantrail/surgery_locks.jsonl")
    p.add_argument("--vacuum-out", default="artifacts/leantrail/vacuum_packets.jsonl")
    p.add_argument("--bridge-out", default="artifacts/leantrail/bridge_packets.jsonl")
    p.add_argument("--alignment-out", default="artifacts/leantrail/alignment_packets.jsonl")
    p.add_argument("--proof-hole-out", default="artifacts/leantrail/proof_hole_packets.jsonl")
    p.add_argument("--json-out", default="artifacts/leantrail/surgery_plan_report.json")
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    locks = Path(args.surgery_locks).resolve()
    vacuum, bridge, alignment, proof_holes, report = plan(Path(args.snapshot).resolve(), locks if locks.exists() else None)
    _write_jsonl(Path(args.vacuum_out).resolve(), vacuum)
    _write_jsonl(Path(args.bridge_out).resolve(), bridge)
    _write_jsonl(Path(args.alignment_out).resolve(), alignment)
    _write_jsonl(Path(args.proof_hole_out).resolve(), proof_holes)
    report_path = Path(args.json_out).resolve()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, ensure_ascii=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
