#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

try:
    import networkx as nx
except Exception as exc:  # pragma: no cover
    raise SystemExit(
        "shadow_ledger.py requires networkx. Install it in the repo Python environment."
    ) from exc

from leantrail.backend.models import GraphSnapshot, NodeRecord
from tools.leantrail.adapters import load_snapshot


SCHEMA = "leantrail.shadow_ledger.v1"
DEPENDENCY_EDGE_KINDS = {"depends_type", "depends_value", "type", "value"}
VALUE_EDGE_KINDS = {"depends_value", "value"}
META_EDGE_KINDS = {"contains"}

SAFE_TARGET_ROLES = {"fake_transport", "pure_conductor"}
UNSAFE_REPLACEMENT_ROLES = {
    "contaminated",
    "closure_debt",
    "deferred_interface",
    "unknown",
}
CRITIC_BLOCKING_SEVERITIES = {"high", "critical", "blocker"}
MATHLIB_OWNER_PREFIX = "Mathlib"


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    if not path.exists():
        return ""
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return "sha256:" + h.hexdigest()


def iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for line_no, raw in enumerate(handle, start=1):
            s = raw.strip()
            if not s:
                continue
            try:
                obj = json.loads(s)
            except Exception as exc:
                raise ValueError(f"Invalid JSON at {path}:{line_no}: {exc}") from exc
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )


def get_nested(obj: Any, dotted: str, default: Any = None) -> Any:
    cur = obj
    for part in dotted.split("."):
        if not isinstance(cur, dict):
            return default
        cur = cur.get(part)
        if cur is None:
            return default
    return cur


def as_bool(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() in {"1", "true", "yes", "y"}
    return bool(value)


def severity_blocks(value: Any) -> bool:
    if isinstance(value, (int, float)):
        return float(value) >= 3.0
    if isinstance(value, str):
        return value.strip().lower() in CRITIC_BLOCKING_SEVERITIES
    return False


def node_attrs(node: NodeRecord | None) -> dict[str, Any]:
    if node is None:
        return {}
    return node.attrs if isinstance(node.attrs, dict) else {}


def node_role(node: NodeRecord | None) -> str:
    attrs = node_attrs(node)
    return str(get_nested(attrs, "vacuity.role", "unknown") or "unknown")


def contamination_state(node: NodeRecord | None) -> str:
    attrs = node_attrs(node)
    return str(get_nested(attrs, "contamination.state", "clean") or "clean")


def hole_state(node: NodeRecord | None) -> str:
    attrs = node_attrs(node)
    return str(get_nested(attrs, "hole.state", "none") or "none")


def is_protected_node(node: NodeRecord | None) -> bool:
    if node is None:
        return False
    attrs = node_attrs(node)
    return (
        as_bool(getattr(node, "is_protected", False))
        or as_bool(get_nested(attrs, "surgery.protected", False))
        or str(get_nested(attrs, "surgery.state", "")).strip()
        in {
            "protected",
            "quarantine",
            "manual_refactor_required",
            "rejected",
        }
    )


def source_patch_ok(packet: dict[str, Any]) -> bool:
    return (
        packet.get("decl_span_kind") == "top_level_decl"
        and packet.get("patch_span_kind") == "decl_body"
        and packet.get("source_info_kind") == "original"
    )


def is_mathlib_owner_module(module: str) -> bool:
    module = str(module).strip()
    return module == MATHLIB_OWNER_PREFIX or module.startswith(f"{MATHLIB_OWNER_PREFIX}.")


def packet_replacement(packet: dict[str, Any]) -> str:
    payload = packet.get("payload", {}) if isinstance(packet.get("payload", {}), dict) else {}
    return str(payload.get("replacement") or packet.get("replacement") or "").strip()


def packet_replacement_module(packet: dict[str, Any]) -> str:
    payload = packet.get("payload", {}) if isinstance(packet.get("payload", {}), dict) else {}
    replacement_module = payload.get("replacement_module") or packet.get("replacement_module") or ""
    return str(replacement_module).strip()


def packet_source_patch(packet: dict[str, Any]) -> dict[str, Any]:
    payload = packet.get("payload", {}) if isinstance(packet.get("payload", {}), dict) else {}
    source_patch = payload.get("source_patch", {})
    return source_patch if isinstance(source_patch, dict) else {}


def packet_span_key(packet: dict[str, Any]) -> tuple[str, int, int] | None:
    source_patch = packet_source_patch(packet)
    file_raw = packet.get("file") or source_patch.get("file")
    start = source_patch.get("startByte", source_patch.get("start_byte"))
    end = source_patch.get("endByte", source_patch.get("end_byte"))
    if not file_raw or not isinstance(start, int) or not isinstance(end, int):
        return None
    return (str(file_raw), int(start), int(end))


def spans_overlap(a: tuple[int, int], b: tuple[int, int]) -> bool:
    return max(a[0], b[0]) < min(a[1], b[1])


def build_dependency_graph(snapshot: GraphSnapshot) -> nx.DiGraph:
    """
    Graph orientation:
      declaration -> dependency

    That is, an edge B -> A means B depends on A.
    """
    graph = nx.DiGraph()
    decl_ids = {node.id for node in snapshot.nodes if node.kind == "Declaration"}

    for node_id in decl_ids:
        graph.add_node(node_id)

    for edge in snapshot.edges:
        if edge.kind in META_EDGE_KINDS:
            continue
        if edge.kind not in DEPENDENCY_EDGE_KINDS:
            continue
        if edge.src in decl_ids and edge.dst in decl_ids:
            graph.add_edge(edge.src, edge.dst, kind=edge.kind)

    return graph


@dataclass
class SccInfo:
    scc_of: dict[str, int]
    members: dict[int, set[str]]
    condensation: nx.DiGraph
    topo_rank: dict[int, int]
    reverse_topo_rank: dict[int, int]


def compute_scc_info(graph: nx.DiGraph) -> SccInfo:
    comps = list(nx.strongly_connected_components(graph))
    scc_of: dict[str, int] = {}
    members: dict[int, set[str]] = {}

    for idx, comp in enumerate(comps):
        members[idx] = set(comp)
        for node in comp:
            scc_of[node] = idx

    condensation = nx.condensation(graph, scc=comps)
    if nx.is_directed_acyclic_graph(condensation):
        topo = list(nx.topological_sort(condensation))
    else:
        topo = list(condensation.nodes)

    topo_rank = {sid: i for i, sid in enumerate(topo)}
    reverse_topo_rank = {sid: len(topo) - i - 1 for i, sid in enumerate(topo)}

    return SccInfo(
        scc_of=scc_of,
        members=members,
        condensation=condensation,
        topo_rank=topo_rank,
        reverse_topo_rank=reverse_topo_rank,
    )


def packet_sort_key(packet: dict[str, Any], scc_info: SccInfo) -> tuple[int, float, str]:
    target = str(packet.get("target", ""))
    sid = scc_info.scc_of.get(target, -1)
    fallback = int(packet.get("reverse_topo_rank", 10**9) or 10**9)
    reverse_rank = scc_info.reverse_topo_rank.get(sid, fallback)
    priority = float(packet.get("priority_score", 0.0) or 0.0)
    return (reverse_rank, -priority, target)


def immediate_blast_radius(
    graph: nx.DiGraph,
    target: str,
    replacement: str | None = None,
) -> set[str]:
    """
    Use local blast radius for v1 contractions.

    Direction:
      predecessors = consumers
      successors   = dependencies
    """
    out = {target}
    if target in graph:
        out.update(graph.predecessors(target))
        out.update(graph.successors(target))
    if replacement and replacement in graph:
        out.add(replacement)
        out.update(graph.predecessors(replacement))
        out.update(graph.successors(replacement))
    return out


def full_blast_radius(
    graph: nx.DiGraph,
    target: str,
    replacement: str | None = None,
) -> set[str]:
    out = {target}
    if target in graph:
        out.update(nx.ancestors(graph, target))
        out.update(nx.descendants(graph, target))
    if replacement and replacement in graph:
        out.add(replacement)
        out.update(nx.ancestors(graph, replacement))
        out.update(nx.descendants(graph, replacement))
    return out


def critic_blocks(node: NodeRecord | None, packet: dict[str, Any]) -> bool:
    payload = packet.get("payload", {}) if isinstance(packet.get("payload", {}), dict) else {}
    if as_bool(packet.get("allow_high_severity_critic", False)):
        return False
    if as_bool(payload.get("allow_high_severity_critic", False)):
        return False

    attrs = node_attrs(node)
    critic = attrs.get("critic", {}) if isinstance(attrs.get("critic", {}), dict) else {}

    if as_bool(critic.get("block_surgery", False)):
        return True

    if severity_blocks(critic.get("severity")):
        return True

    if severity_blocks(get_nested(attrs, "critic.top_issue.severity", None)):
        return True

    return False


def defer_packet(
    packet: dict[str, Any],
    reason: str,
    epoch: str,
    extra: dict[str, Any] | None = None,
) -> dict[str, Any]:
    out = dict(packet)
    out["state"] = "shadow_deferred"
    out["shadow_epoch"] = epoch
    out["shadow_state"] = "deferred"
    out["shadow_reason"] = reason
    reasons = list(out.get("shadow_reasons", [])) if isinstance(out.get("shadow_reasons", []), list) else []
    reasons.append(reason)
    out["shadow_reasons"] = reasons
    if extra:
        out["shadow_details"] = extra
    return out


def approve_packet(packet: dict[str, Any], epoch: str, checks: dict[str, Any]) -> dict[str, Any]:
    out = dict(packet)
    out["state"] = "shadow_approved"
    out["shadow_epoch"] = epoch
    out["shadow_state"] = "approved"
    out["shadow_approved_at"] = utc_now()
    out["shadow_checks"] = checks
    return out


def replacement_safe(node: NodeRecord | None) -> tuple[bool, str]:
    if node is None:
        return False, "replacement_node_missing"

    role = node_role(node)
    contamination = contamination_state(node)
    hole = hole_state(node)

    if contamination not in {"clean", ""}:
        return False, f"replacement_contaminated:{contamination}"

    if hole not in {"", "none"}:
        return False, f"replacement_has_hole:{hole}"

    if role in UNSAFE_REPLACEMENT_ROLES:
        return False, f"replacement_role_unsafe:{role}"

    return True, "ok"


def validate_packet_static(
    packet: dict[str, Any],
    *,
    node_by_id: dict[str, NodeRecord],
    scc_info: SccInfo,
    epoch: str,
) -> tuple[bool, str, dict[str, Any]]:
    del epoch
    target = str(packet.get("target", "")).strip()
    replacement = packet_replacement(packet)

    if packet.get("packet_stream") != "vacuum":
        return False, "not_vacuum_stream", {}

    if packet.get("action_phase") != "contract":
        return False, "not_contract_phase", {}

    if packet.get("state") != "certified":
        return False, f"state_not_certified:{packet.get('state')}", {}

    payload = packet.get("payload", {}) if isinstance(packet.get("payload", {}), dict) else {}
    if as_bool(payload.get("destructive", False)):
        return False, "destructive_packet_rejected_v1", {}

    if not target:
        return False, "missing_target", {}

    if not replacement:
        return False, "missing_replacement", {}

    target_node = node_by_id.get(target)
    replacement_node = node_by_id.get(replacement)

    if target_node is None:
        return False, "target_node_missing", {}

    if replacement_node is None:
        return False, "replacement_node_missing", {}

    if target == replacement:
        return False, "replacement_same_as_target", {}

    if is_protected_node(target_node):
        return False, "target_protected_or_quarantined", {}

    if critic_blocks(target_node, packet):
        return False, "high_severity_critic_block", {}

    role = str(payload.get("role") or node_role(target_node))
    if role not in SAFE_TARGET_ROLES:
        return False, f"target_role_not_contractible:{role}", {}

    if contamination_state(target_node) not in {"clean", ""}:
        return False, f"target_contaminated:{contamination_state(target_node)}", {}

    if hole_state(target_node) not in {"", "none"}:
        return False, f"target_has_hole:{hole_state(target_node)}", {}

    target_scc = scc_info.scc_of.get(target, -1)
    replacement_scc = scc_info.scc_of.get(replacement, -1)
    target_scc_size = len(scc_info.members.get(target_scc, {target}))
    replacement_scc_size = len(scc_info.members.get(replacement_scc, {replacement}))

    if target_scc_size != 1:
        return False, "target_scc_not_singleton", {
            "target_scc": target_scc,
            "target_scc_size": target_scc_size,
        }

    safe, reason = replacement_safe(replacement_node)
    if not safe:
        return False, reason, {
            "replacement_scc": replacement_scc,
            "replacement_scc_size": replacement_scc_size,
        }

    replacement_module = packet_replacement_module(packet)
    if replacement_module:
        if not is_mathlib_owner_module(replacement_module):
            return False, f"replacement_not_mathlib_owner:{replacement_module}", {
                "replacement_module": replacement_module,
            }
    elif replacement_node is not None:
        if not is_mathlib_owner_module(str(getattr(replacement_node, "module", "") or "")):
            return False, f"replacement_not_mathlib_owner:{getattr(replacement_node, 'module', '')}", {
                "replacement_module": str(getattr(replacement_node, "module", "") or ""),
            }

    if not source_patch_ok(packet):
        return False, "source_patch_provenance_not_safe", {
            "decl_span_kind": packet.get("decl_span_kind"),
            "patch_span_kind": packet.get("patch_span_kind"),
            "source_info_kind": packet.get("source_info_kind"),
        }

    source_patch = packet_source_patch(packet)
    if not isinstance(source_patch.get("startByte", source_patch.get("start_byte")), int):
        return False, "source_patch_missing_startByte", {}
    if not isinstance(source_patch.get("endByte", source_patch.get("end_byte")), int):
        return False, "source_patch_missing_endByte", {}
    if not (source_patch.get("fileHash") or source_patch.get("file_hash") or packet.get("file_hash")):
        return False, "source_patch_missing_fileHash", {}

    return True, "ok", {
        "target": target,
        "replacement": replacement,
        "target_scc": target_scc,
        "replacement_scc": replacement_scc,
        "target_scc_size": target_scc_size,
        "replacement_scc_size": replacement_scc_size,
    }


def simulate_contract_value_edge(graph: nx.DiGraph, target: str, replacement: str) -> None:
    """
    Simulate body contraction while preserving the declaration node.

    A source edit changes the proof/body of `target`, so the target declaration
    remains present. We conservatively replace outgoing value-dependency edges
    of target with a single value-dependency edge to replacement. Type edges
    remain untouched.
    """
    if target not in graph or replacement not in graph:
        return

    remove_edges: list[tuple[str, str]] = []
    for _, dst, data in graph.out_edges(target, data=True):
        if data.get("kind") in VALUE_EDGE_KINDS:
            remove_edges.append((target, dst))

    for edge in remove_edges:
        graph.remove_edge(*edge)

    if target != replacement:
        graph.add_edge(target, replacement, kind="depends_value", shadow_contract=True)


def would_create_bad_dependency_cycle(graph: nx.DiGraph, target: str, replacement: str) -> bool:
    """
    If replacement currently depends on target, replacing target's body with
    replacement would make the target depend on something that depends on target.
    Defer this in v1.
    """
    if target not in graph or replacement not in graph:
        return True
    try:
        return nx.has_path(graph, replacement, target)
    except nx.NetworkXError:
        return True


def select_and_simulate(
    *,
    snapshot: GraphSnapshot,
    packets: list[dict[str, Any]],
    epoch: str,
    max_batch_size: int,
    full_blast_radius_mode: bool,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    node_by_id = {n.id: n for n in snapshot.nodes if n.kind == "Declaration"}
    graph = build_dependency_graph(snapshot)
    scc_info = compute_scc_info(graph)
    shadow_graph = graph.copy()

    certified_contracts = [
        p
        for p in packets
        if p.get("packet_stream") == "vacuum"
        and p.get("action_phase") == "contract"
        and p.get("state") == "certified"
    ]
    non_candidates = [
        p
        for p in packets
        if not (
            p.get("packet_stream") == "vacuum"
            and p.get("action_phase") == "contract"
            and p.get("state") == "certified"
        )
    ]

    approved: list[dict[str, Any]] = []
    deferred: list[dict[str, Any]] = []

    for packet in non_candidates:
        reason = (
            f"not_certified_vacuum_contract:{packet.get('packet_stream')}:"
            f"{packet.get('action_phase')}:{packet.get('state')}"
        )
        deferred.append(defer_packet(packet, reason, epoch))

    locked_sccs: set[str] = set()
    locked_signature_classes: set[str] = set()
    locked_replacements: set[str] = set()
    locked_nodes: set[str] = set()
    locked_spans_by_file: dict[str, list[tuple[int, int, str]]] = defaultdict(list)

    sorted_packets = sorted(certified_contracts, key=lambda p: packet_sort_key(p, scc_info))

    for packet in sorted_packets:
        if len(approved) >= max_batch_size:
            deferred.append(defer_packet(packet, "batch_size_limit", epoch))
            continue

        ok, reason, details = validate_packet_static(
            packet,
            node_by_id=node_by_id,
            scc_info=scc_info,
            epoch=epoch,
        )
        if not ok:
            deferred.append(defer_packet(packet, reason, epoch, details))
            continue

        target = details["target"]
        replacement = details["replacement"]

        if target not in shadow_graph:
            deferred.append(defer_packet(packet, "shadow_target_missing_or_removed", epoch))
            continue

        if replacement not in shadow_graph:
            deferred.append(defer_packet(packet, "shadow_replacement_missing_or_removed", epoch))
            continue

        if would_create_bad_dependency_cycle(shadow_graph, target, replacement):
            deferred.append(defer_packet(packet, "replacement_depends_on_target_cycle_risk", epoch))
            continue

        scc_id = str(packet.get("scc_id") or f"scc_{details['target_scc']}")
        signature_class = str(packet.get("signature_class") or "")

        if scc_id in locked_sccs:
            deferred.append(defer_packet(packet, "scc_locked_by_prior_packet", epoch))
            continue

        if signature_class and signature_class in locked_signature_classes:
            deferred.append(defer_packet(packet, "signature_class_locked_by_prior_packet", epoch))
            continue

        if replacement in locked_replacements:
            deferred.append(defer_packet(packet, "replacement_locked_by_prior_packet", epoch))
            continue

        if full_blast_radius_mode:
            radius = full_blast_radius(shadow_graph, target, replacement)
        else:
            radius = immediate_blast_radius(shadow_graph, target, replacement)

        if not radius.isdisjoint(locked_nodes):
            deferred.append(defer_packet(packet, "blast_radius_intersects_prior_packet", epoch, {
                "intersection": sorted(radius & locked_nodes)[:25],
            }))
            continue

        span = packet_span_key(packet)
        if span is None:
            deferred.append(defer_packet(packet, "source_patch_span_missing", epoch))
            continue

        file_path, start, end = span
        if start < 0 or end < start:
            deferred.append(defer_packet(packet, "source_patch_span_invalid", epoch, {
                "file": file_path,
                "startByte": start,
                "endByte": end,
            }))
            continue

        overlap_found = False
        for old_start, old_end, old_packet in locked_spans_by_file[file_path]:
            if spans_overlap((start, end), (old_start, old_end)):
                deferred.append(defer_packet(packet, "source_patch_span_overlaps_prior_packet", epoch, {
                    "file": file_path,
                    "overlaps_packet_id": old_packet,
                }))
                overlap_found = True
                break
        if overlap_found:
            continue

        simulate_contract_value_edge(shadow_graph, target, replacement)

        checks = {
            "schema": SCHEMA,
            "target": target,
            "replacement": replacement,
            "target_scc": details["target_scc"],
            "replacement_scc": details["replacement_scc"],
            "source_patch_span": {
                "file": file_path,
                "startByte": start,
                "endByte": end,
            },
            "blast_radius_mode": "full" if full_blast_radius_mode else "immediate",
            "blast_radius_size": len(radius),
            "state_transition": "certified -> shadow_approved",
            "semantic_authority": (
                "shadow_approved only means worth trying in worktree; "
                "Lean kernel remains authority"
            ),
        }
        approved_packet = approve_packet(packet, epoch, checks)
        approved.append(approved_packet)

        locked_sccs.add(scc_id)
        if signature_class:
            locked_signature_classes.add(signature_class)
        locked_replacements.add(replacement)
        locked_nodes.update(radius)
        locked_spans_by_file[file_path].append((start, end, str(packet.get("packet_id", ""))))

    reason_counts = Counter(p.get("shadow_reason", "") for p in deferred)
    manifest = {
        "schema": SCHEMA,
        "created_at": utc_now(),
        "shadow_epoch": epoch,
        "dependency_orientation": "declaration -> dependency",
        "action_phase": "contract",
        "source_edit_policy": "no source edits in shadow ledger",
        "kernel_authority": "Lean kernel / lake build remains final authority",
        "counts": {
            "input_packets": len(packets),
            "certified_contract_candidates": len(certified_contracts),
            "approved": len(approved),
            "deferred": len(deferred),
            "snapshot_nodes": len(snapshot.nodes),
            "snapshot_edges": len(snapshot.edges),
            "dependency_nodes": graph.number_of_nodes(),
            "dependency_edges": graph.number_of_edges(),
            "shadow_dependency_edges": shadow_graph.number_of_edges(),
        },
        "approved_packet_ids": [str(p.get("packet_id", "")) for p in approved],
        "deferred_by_reason": dict(sorted(reason_counts.items())),
        "approved_targets": [
            {
                "packet_id": p.get("packet_id"),
                "target": p.get("target"),
                "replacement": packet_replacement(p),
                "file": p.get("file"),
            }
            for p in approved
        ],
    }

    return approved, deferred, manifest


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "LeanTrail Shadow Ledger control plane: promote certified contraction "
            "packets to shadow_approved or shadow_deferred."
        )
    )
    parser.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.vacuity.json")
    parser.add_argument("--vacuum-packets", default="artifacts/leantrail/vacuum_packets.jsonl")
    parser.add_argument("--approved-out", default="artifacts/leantrail/shadow_approved_packets.jsonl")
    parser.add_argument("--deferred-out", default="artifacts/leantrail/shadow_deferred_packets.jsonl")
    parser.add_argument("--manifest-out", default="artifacts/leantrail/surgery_manifest.json")
    parser.add_argument("--json-out", default="artifacts/leantrail/shadow_ledger_report.json")
    parser.add_argument("--epoch", default="")
    parser.add_argument("--max-batch-size", type=int, default=20)
    parser.add_argument(
        "--full-blast-radius",
        action="store_true",
        help="Use full transitive blast radius instead of immediate-neighborhood locking.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    snapshot_path = Path(args.snapshot).resolve()
    packets_path = Path(args.vacuum_packets).resolve()
    epoch = str(args.epoch).strip()
    if not epoch:
        epoch = f"shadow-{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}"

    snapshot = load_snapshot(snapshot_path)
    packets = iter_jsonl(packets_path)

    approved, deferred, manifest = select_and_simulate(
        snapshot=snapshot,
        packets=packets,
        epoch=epoch,
        max_batch_size=max(0, int(args.max_batch_size)),
        full_blast_radius_mode=bool(args.full_blast_radius),
    )

    approved_out = Path(args.approved_out).resolve()
    deferred_out = Path(args.deferred_out).resolve()
    manifest_out = Path(args.manifest_out).resolve()
    report_out = Path(args.json_out).resolve()

    write_jsonl(approved_out, approved)
    write_jsonl(deferred_out, deferred)
    write_json(manifest_out, manifest)

    report = dict(manifest)
    report["input"] = {
        "snapshot": str(snapshot_path),
        "snapshot_hash": sha256_file(snapshot_path),
        "vacuum_packets": str(packets_path),
        "vacuum_packets_hash": sha256_file(packets_path),
    }
    report["outputs"] = {
        "approved_out": str(approved_out),
        "deferred_out": str(deferred_out),
        "manifest_out": str(manifest_out),
    }
    write_json(report_out, report)

    print(json.dumps(report, indent=2, ensure_ascii=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
