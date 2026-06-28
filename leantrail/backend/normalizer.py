from __future__ import annotations

import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

from .models import EdgeRecord, GraphSnapshot, NodeRecord


EDGE_KIND_MAP = {
    "type": "depends_type",
    "value": "depends_value",
}

TYPED_SEMANTIC_KIND_MAP = {
    "translator": "translator_of",
    "coherence": "coheres_with",
    "obstruction": "obstructs",
    "quotientWitness": "quotient_witness",
}

_FAILED_KINDS = {"obstructs", "violates_depth"}
_META_KINDS = {"contains"}
_LOCKABLE_STATES = {"bound", "locked"}


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _iter_jsonl(path: Path, max_rows: int | None = None) -> Iterable[dict[str, Any]]:
    with path.open(encoding="utf-8") as handle:
        for idx, line in enumerate(handle):
            if max_rows is not None and idx >= max_rows:
                break
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)


def _edge_key(src: str, dst: str, kind: str) -> tuple[str, str, str]:
    return (src, dst, kind)


def _load_failed_transition_index(path: Path) -> dict[tuple[str, str, str], dict[str, Any]]:
    out: dict[tuple[str, str, str], dict[str, Any]] = {}
    if not path.exists():
        return out

    for row in _iter_jsonl(path):
        src = str(row.get("src", "")).strip()
        dst = str(row.get("dst", "")).strip()
        kind = str(row.get("kind", "depends_value")).strip() or "depends_value"
        if not src or not dst:
            continue
        count_raw = row.get("count")
        count = int(count_raw) if isinstance(count_raw, int) and count_raw > 0 else 1
        error_kind = str(row.get("error_kind", "")).strip() or "unknown"
        key = _edge_key(src, dst, kind)
        rec = out.get(key)
        if rec is None:
            out[key] = {"count": count, "kinds": {error_kind}}
        else:
            rec["count"] = int(rec.get("count", 0)) + count
            kinds = rec.get("kinds")
            if isinstance(kinds, set):
                kinds.add(error_kind)
            else:
                rec["kinds"] = {error_kind}
    return out


def _load_path_lock_index(path: Path) -> set[tuple[str, str, str]]:
    locked: set[tuple[str, str, str]] = set()
    if not path.exists():
        return locked

    for row in _iter_jsonl(path):
        state = str(row.get("state", "locked")).strip().lower()
        if state != "locked":
            continue

        edges = row.get("edges")
        if isinstance(edges, list):
            for edge in edges:
                if not isinstance(edge, dict):
                    continue
                src = str(edge.get("src", "")).strip()
                dst = str(edge.get("dst", "")).strip()
                kind = str(edge.get("kind", "")).strip()
                if src and dst and kind:
                    locked.add(_edge_key(src, dst, kind))
            continue

        src = str(row.get("src", "")).strip()
        dst = str(row.get("dst", "")).strip()
        kind = str(row.get("kind", "")).strip()
        if src and dst and kind:
            locked.add(_edge_key(src, dst, kind))
    return locked


def _default_path_state(kind: str) -> str:
    if kind in _FAILED_KINDS:
        return "failed"
    if kind in _META_KINDS:
        return "meta"
    return "bound"


def _annotate_edge_path_states(
    edges: list[EdgeRecord],
    *,
    failed_index: dict[tuple[str, str, str], dict[str, Any]],
    locked_index: set[tuple[str, str, str]],
) -> None:
    for edge in edges:
        key = _edge_key(edge.src, edge.dst, edge.kind)
        attrs = edge.attrs if isinstance(edge.attrs, dict) else {}
        attrs = dict(attrs)

        if key in locked_index:
            state = "locked"
        elif key in failed_index:
            state = "failed"
        else:
            state = _default_path_state(edge.kind)
        attrs["path_state"] = state

        failure_row = failed_index.get(key)
        if failure_row:
            attrs["failure_count"] = int(failure_row.get("count", 0))
            kinds = failure_row.get("kinds")
            if isinstance(kinds, set):
                attrs["failure_kinds"] = sorted(str(k) for k in kinds if str(k))
        edge.attrs = attrs


def _dedupe_edges(edges: list[EdgeRecord]) -> tuple[list[EdgeRecord], int]:
    """Merge redundant graph wires with the same semantic edge identity.

    The LeanTrail graph treats `(src, dst, kind)` as the traversal edge key.
    Multiple producers can report the same wire, especially depth-violation
    overlays derived from both type and value dependency rows.  Keep one edge
    and preserve provenance in `attrs.evidence_refs`.
    """
    by_key: dict[tuple[str, str, str], EdgeRecord] = {}
    removed = 0
    for edge in edges:
        key = _edge_key(edge.src, edge.dst, edge.kind)
        prior = by_key.get(key)
        if prior is None:
            attrs = dict(edge.attrs) if isinstance(edge.attrs, dict) else {}
            refs = attrs.get("evidence_refs")
            if isinstance(refs, list):
                evidence_refs = {str(ref) for ref in refs if str(ref)}
            else:
                evidence_refs = set()
            if edge.evidence_ref:
                evidence_refs.add(edge.evidence_ref)
            if evidence_refs:
                attrs["evidence_refs"] = sorted(evidence_refs)
            edge.attrs = attrs
            by_key[key] = edge
            continue

        removed += 1
        if edge.weight > prior.weight:
            prior.weight = edge.weight
        attrs = dict(prior.attrs) if isinstance(prior.attrs, dict) else {}
        other_attrs = edge.attrs if isinstance(edge.attrs, dict) else {}
        for attr_key, attr_value in other_attrs.items():
            attrs.setdefault(attr_key, attr_value)
        evidence_refs = set()
        refs = attrs.get("evidence_refs")
        if isinstance(refs, list):
            evidence_refs.update(str(ref) for ref in refs if str(ref))
        if prior.evidence_ref:
            evidence_refs.add(prior.evidence_ref)
        if edge.evidence_ref:
            evidence_refs.add(edge.evidence_ref)
        if evidence_refs:
            attrs["evidence_refs"] = sorted(evidence_refs)
            prior.evidence_ref = sorted(evidence_refs)[0]
        prior.attrs = attrs
    return list(by_key.values()), removed


def _annotate_node_endpoints(nodes: list[NodeRecord], edges: list[EdgeRecord]) -> dict[str, int]:
    decl_ids = {node.id for node in nodes if node.kind == "Declaration"}
    indeg: dict[str, int] = {nid: 0 for nid in decl_ids}
    outdeg: dict[str, int] = {nid: 0 for nid in decl_ids}

    for edge in edges:
        if edge.kind in _META_KINDS:
            continue
        attrs = edge.attrs if isinstance(edge.attrs, dict) else {}
        state = str(attrs.get("path_state", "")).strip().lower()
        if state not in _LOCKABLE_STATES:
            continue
        if edge.src in decl_ids:
            outdeg[edge.src] = outdeg.get(edge.src, 0) + 1
        if edge.dst in decl_ids:
            indeg[edge.dst] = indeg.get(edge.dst, 0) + 1

    summary = {"source": 0, "sink": 0, "internal": 0, "isolated": 0}
    for node in nodes:
        if node.kind != "Declaration":
            continue
        attrs = node.attrs if isinstance(node.attrs, dict) else {}
        attrs = dict(attrs)
        inn = int(indeg.get(node.id, 0))
        out = int(outdeg.get(node.id, 0))
        if inn == 0 and out == 0:
            endpoint = "isolated"
        elif inn == 0:
            endpoint = "source"
        elif out == 0:
            endpoint = "sink"
        else:
            endpoint = "internal"
        summary[endpoint] += 1
        attrs["path_endpoint"] = endpoint
        attrs["path_in_degree"] = inn
        attrs["path_out_degree"] = out
        node.attrs = attrs
    return summary


def _annotate_node_process_geometry(
    nodes: list[NodeRecord],
    *,
    lawful_cones_by_name: dict[str, dict[str, Any]],
    typed_paths_by_src: dict[str, list[dict[str, Any]]],
) -> dict[str, int]:
    summary = {"cones": 0, "path_owners": 0, "paths": 0}
    for node in nodes:
        if node.kind != "Declaration":
            continue

        attrs = node.attrs if isinstance(node.attrs, dict) else {}
        attrs = dict(attrs)

        cone_row = lawful_cones_by_name.get(node.id)
        if isinstance(cone_row, dict):
            base = cone_row.get("base")
            base = base if isinstance(base, dict) else {}
            legs = base.get("legs")
            shared = base.get("sharedComparisons")
            defects = cone_row.get("defects")
            leg_rows = legs if isinstance(legs, list) else []
            shared_rows = shared if isinstance(shared, list) else []
            defect_rows = defects if isinstance(defects, list) else []
            leg_kinds = sorted(
                {
                    str(leg.get("kind", "")).strip()
                    for leg in leg_rows
                    if isinstance(leg, dict) and str(leg.get("kind", "")).strip()
                }
            )
            total_defect_cost = cone_row.get("totalDefectCost")
            total_cost = int(total_defect_cost) if isinstance(total_defect_cost, int) else 0
            attrs["lawful_cone"] = {
                "leg_count": len(leg_rows),
                "shared_comparison_count": len(shared_rows),
                "defect_count": len(defect_rows),
                "total_defect_cost": total_cost,
                "leg_kinds": leg_kinds,
            }
            summary["cones"] += 1

        typed_paths = typed_paths_by_src.get(node.id, [])
        if typed_paths:
            costs = [
                int(row.get("totalDefectCost", 0))
                for row in typed_paths
                if isinstance(row, dict) and isinstance(row.get("totalDefectCost", 0), int)
            ]
            attrs["lawful_path_summary"] = {
                "count": len(typed_paths),
                "defectful_count": sum(1 for cost in costs if cost > 0),
                "max_defect_cost": max(costs, default=0),
            }
            summary["path_owners"] += 1
            summary["paths"] += len(typed_paths)

        node.attrs = attrs
    return summary


def _safe_git_head(repo_root: Path) -> str:
    try:
        out = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo_root, text=True)
        return out.strip()
    except Exception:
        return "unknown"


def _read_toolchain(repo_root: Path) -> str:
    toolchain = repo_root / "lean-toolchain"
    if toolchain.exists():
        return toolchain.read_text(encoding="utf-8").strip()
    return "unknown"


def _module_family(module_name: str) -> str:
    parts = module_name.split(".")
    if len(parts) <= 3:
        return module_name
    return ".".join(parts[:3])


def _infer_role(name: str, module: str, capstone: bool) -> str:
    if capstone:
        return "capstone"
    lowered = f"{name}.{module}".lower()
    if "translator" in lowered or "bridge" in lowered:
        return "translator"
    if "cohere" in lowered or "compatibility" in lowered or "equiv" in lowered:
        return "coherence"
    return "owner"


def _is_lawful_depth(
    src_depth_nat: int | None,
    dst_depth_nat: int | None,
    src_capstone: bool,
) -> bool:
    if src_capstone:
        return True
    if src_depth_nat is None or dst_depth_nat is None:
        return True
    return dst_depth_nat == src_depth_nat or dst_depth_nat == src_depth_nat - 1


class LeanTrailNormalizer:
    def __init__(self, repo_root: Path) -> None:
        self.repo_root = repo_root.resolve()
        self.dag_root = self.repo_root / "artifacts" / "dag"

    def build_snapshot(
        self,
        max_process_events: int | None = None,
        max_candidates_per_node: int = 12,
        include_modules: set[str] | None = None,
    ) -> GraphSnapshot:
        meta_file = self.dag_root / "index" / "meta.json"
        decl_file = self.dag_root / "index" / "decls.jsonl"
        edge_file = self.dag_root / "index" / "edges.jsonl"
        depth_file = self.dag_root / "representation-depth-tags.json"
        process_file = self.dag_root / "process-flow" / "process-events.jsonl"
        typed_objects_file = self.dag_root / "process-flow" / "typed-decl-objects.jsonl"
        typed_semantic_morphisms_file = self.dag_root / "process-flow" / "typed-semantic-morphisms.jsonl"
        lawful_typed_paths_file = self.dag_root / "process-flow" / "lawful-typed-composite-paths.jsonl"
        lawful_cones_file = self.dag_root / "process-flow" / "lawful-cones.jsonl"
        holonomy_file = self.dag_root / "process-flow" / "holonomy-events.jsonl"
        failed_transitions_file = self.repo_root / "artifacts" / "leantrail" / "failed_transitions.jsonl"
        path_locks_file = self.repo_root / "artifacts" / "leantrail" / "path_locks.jsonl"

        dag_meta = _read_json(meta_file)
        depth_payload = _read_json(depth_file)

        depth_records = depth_payload.get("declarations", [])
        depth_by_name: dict[str, dict[str, Any]] = {}
        for row in depth_records:
            name = str(row.get("name", "")).strip()
            if name:
                depth_by_name[name] = row

        holonomy_by_name: dict[str, dict[str, Any]] = {}
        if holonomy_file.exists():
            for row in _iter_jsonl(holonomy_file):
                name = str(row.get("node", "")).strip()
                if name:
                    holonomy_by_name[name] = row

        process_by_name: dict[str, dict[str, Any]] = {}
        typed_objects_by_name: dict[str, dict[str, Any]] = {}
        lawful_cones_by_name: dict[str, dict[str, Any]] = {}
        typed_paths_by_src: dict[str, list[dict[str, Any]]] = {}
        extra_edges: list[EdgeRecord] = []
        failed_index = _load_failed_transition_index(failed_transitions_file)
        locked_index = _load_path_lock_index(path_locks_file)
        if typed_objects_file.exists():
            for row in _iter_jsonl(typed_objects_file, max_rows=max_process_events):
                name = str(row.get("decl", "")).strip()
                if name:
                    typed_objects_by_name[name] = row
        if lawful_cones_file.exists():
            for row in _iter_jsonl(lawful_cones_file, max_rows=max_process_events):
                base = row.get("base")
                base = base if isinstance(base, dict) else {}
                apex = base.get("apex")
                apex = apex if isinstance(apex, dict) else {}
                name = str(apex.get("decl", "")).strip()
                if name:
                    lawful_cones_by_name[name] = row
        if lawful_typed_paths_file.exists():
            for row in _iter_jsonl(lawful_typed_paths_file, max_rows=max_process_events):
                base = row.get("base")
                base = base if isinstance(base, dict) else {}
                src = str(base.get("src", "")).strip()
                if src:
                    typed_paths_by_src.setdefault(src, []).append(row)
        if process_file.exists():
            for row in _iter_jsonl(process_file, max_rows=max_process_events):
                name = str(row.get("node", "")).strip()
                if not name:
                    continue
                process_by_name[name] = {
                    "role": row.get("role"),
                    "boundaryClass": row.get("boundaryClass"),
                    "novelty": row.get("novelty"),
                }
        if typed_semantic_morphisms_file.exists():
            for row in _iter_jsonl(typed_semantic_morphisms_file):
                src = str(row.get("src", "")).strip()
                dst = str(row.get("dst", "")).strip()
                kind_raw = str(row.get("kind", "")).strip()
                if not src or not dst or not kind_raw:
                    continue
                kind = TYPED_SEMANTIC_KIND_MAP.get(kind_raw)
                if not kind:
                    continue
                extra_edges.append(
                    EdgeRecord(
                        src=src,
                        dst=dst,
                        kind=kind,
                        weight=0.6,
                        evidence_ref="artifacts/dag/process-flow/typed-semantic-morphisms.jsonl",
                    )
                )
        elif process_file.exists():
            for row in _iter_jsonl(process_file, max_rows=max_process_events):
                name = str(row.get("node", "")).strip()
                if not name:
                    continue
                for field, kind in (
                    ("supportCandidates", "translator_of"),
                    ("comparisonCandidates", "coheres_with"),
                    ("closureDeps", "obstructs"),
                ):
                    values = row.get(field) or []
                    if not isinstance(values, list):
                        continue
                    for dst in values[:max_candidates_per_node]:
                        dst_name = str(dst).strip()
                        if not dst_name:
                            continue
                        extra_edges.append(
                            EdgeRecord(
                                src=name,
                                dst=dst_name,
                                kind=kind,
                                weight=0.6,
                                evidence_ref=f"artifacts/dag/process-flow/process-events.jsonl:{field}",
                            )
                        )

        module_filter = {m for m in include_modules or set() if m}
        commit_sha = _safe_git_head(self.repo_root)
        toolchain = _read_toolchain(self.repo_root)
        artifact_version = int(dag_meta.get("schemaVersion", 0))

        nodes: list[NodeRecord] = []
        edges: list[EdgeRecord] = []
        include_decl_ids: set[str] | None = set() if module_filter else None

        module_seen: set[str] = set()
        for decl in _iter_jsonl(decl_file):
            name = str(decl.get("name", "")).strip()
            module = str(decl.get("module", "")).strip()
            if not name or not module:
                continue
            if module_filter and module not in module_filter:
                continue
            if include_decl_ids is not None:
                include_decl_ids.add(name)

            depth_row = depth_by_name.get(name, {})
            process_row = process_by_name.get(name, {})
            typed_object_row = typed_objects_by_name.get(name, {})
            capstone = bool(depth_row.get("capstone", False))

            role_raw = str(typed_object_row.get("role", "")).strip() or str(process_row.get("role", "")).strip() or None
            if role_raw in {"owner", "translator", "coherence", "capstone", "infrastructure"}:
                role = role_raw
            else:
                role = _infer_role(name, module, capstone)

            attrs = {
                "decl_kind": decl.get("kind"),
                "doc": decl.get("doc", ""),
                "boundary_class": typed_object_row.get("boundary") or process_row.get("boundaryClass"),
                "novelty": process_row.get("novelty"),
                "attrs": decl.get("attrs", []),
            }
            holonomy_row = holonomy_by_name.get(name)
            if holonomy_row:
                attrs["holonomy"] = holonomy_row
            if role_raw and role_raw != role:
                attrs["process_role"] = role_raw

            nodes.append(
                NodeRecord(
                    id=name,
                    name=name,
                    kind="Declaration",
                    module=module,
                    file=decl.get("file"),
                    line=decl.get("line"),
                    rep_depth=depth_row.get("depth"),
                    role=role,
                    module_family=_module_family(module),
                    commit_sha=commit_sha,
                    toolchain=toolchain,
                    artifact_version=artifact_version,
                    attrs=attrs,
                )
            )

            if module not in module_seen:
                module_seen.add(module)
                nodes.append(
                    NodeRecord(
                        id=f"module:{module}",
                        name=module,
                        kind="Module",
                        module=module,
                        file=None,
                        line=None,
                        rep_depth=None,
                        role="owner",
                        module_family=_module_family(module),
                        commit_sha=commit_sha,
                        toolchain=toolchain,
                        artifact_version=artifact_version,
                        attrs={},
                    )
                )

            edges.append(
                EdgeRecord(
                    src=f"module:{module}",
                    dst=name,
                    kind="contains",
                    weight=1.0,
                    evidence_ref="artifacts/dag/index/decls.jsonl",
                )
            )

        depth_nat_by_name: dict[str, int] = {
            n: int(row["depthNat"])
            for n, row in depth_by_name.items()
            if isinstance(row.get("depthNat"), int)
        }
        capstone_by_name: dict[str, bool] = {
            n: bool(row.get("capstone", False))
            for n, row in depth_by_name.items()
        }

        for dep in _iter_jsonl(edge_file):
            src = str(dep.get("src", "")).strip()
            dst = str(dep.get("dst", "")).strip()
            raw_kind = str(dep.get("kind", "value")).strip()
            if not src or not dst:
                continue
            if include_decl_ids is not None and src not in include_decl_ids and dst not in include_decl_ids:
                continue

            kind = EDGE_KIND_MAP.get(raw_kind, "depends_value")
            edges.append(
                EdgeRecord(
                    src=src,
                    dst=dst,
                    kind=kind,
                    weight=1.0 if kind == "depends_type" else 1.1,
                    evidence_ref="artifacts/dag/index/edges.jsonl",
                )
            )

            if not _is_lawful_depth(
                src_depth_nat=depth_nat_by_name.get(src),
                dst_depth_nat=depth_nat_by_name.get(dst),
                src_capstone=capstone_by_name.get(src, False),
            ):
                edges.append(
                    EdgeRecord(
                        src=src,
                        dst=dst,
                        kind="violates_depth",
                        weight=3.0,
                        evidence_ref="artifacts/dag/index/edges.jsonl+artifacts/dag/representation-depth-tags.json",
                    )
                )

        if include_decl_ids is None:
            edges.extend(extra_edges)
        else:
            for edge in extra_edges:
                if edge.src in include_decl_ids or edge.dst in include_decl_ids:
                    edges.append(edge)

        edges, duplicate_edges_removed = _dedupe_edges(edges)
        _annotate_edge_path_states(
            edges,
            failed_index=failed_index,
            locked_index=locked_index,
        )
        endpoint_summary = _annotate_node_endpoints(nodes, edges)
        process_geometry_summary = _annotate_node_process_geometry(
            nodes,
            lawful_cones_by_name=lawful_cones_by_name,
            typed_paths_by_src=typed_paths_by_src,
        )

        snapshot_meta = {
            "created_at": _utc_now(),
            "source": "leantrail.normalizer",
            "commit_sha": commit_sha,
            "toolchain": toolchain,
            "artifact_version": artifact_version,
            "scope": "partial" if module_filter else "full",
            "include_modules": sorted(module_filter) if module_filter else [],
            "dag_meta": dag_meta,
            "counts": {
                "nodes": len(nodes),
                "edges": len(edges),
                "depth_rows": len(depth_records),
                "path_endpoints": endpoint_summary,
                "process_geometry": process_geometry_summary,
                "failed_transition_edges": len(failed_index),
                "locked_edges": len(locked_index),
                "duplicate_edges_removed": duplicate_edges_removed,
            },
            "path_state_sources": {
                "failed_transitions_file": str(failed_transitions_file),
                "path_locks_file": str(path_locks_file),
            },
        }

        return GraphSnapshot(metadata=snapshot_meta, nodes=nodes, edges=edges)
