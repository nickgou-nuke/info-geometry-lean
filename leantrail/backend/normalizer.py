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
    ) -> GraphSnapshot:
        meta_file = self.dag_root / "index" / "meta.json"
        decl_file = self.dag_root / "index" / "decls.jsonl"
        edge_file = self.dag_root / "index" / "edges.jsonl"
        depth_file = self.dag_root / "representation-depth-tags.json"
        process_file = self.dag_root / "process-flow" / "process-events.jsonl"

        dag_meta = _read_json(meta_file)
        depth_payload = _read_json(depth_file)

        depth_records = depth_payload.get("declarations", [])
        depth_by_name: dict[str, dict[str, Any]] = {}
        for row in depth_records:
            name = str(row.get("name", "")).strip()
            if name:
                depth_by_name[name] = row

        process_by_name: dict[str, dict[str, Any]] = {}
        extra_edges: list[EdgeRecord] = []
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

        commit_sha = _safe_git_head(self.repo_root)
        toolchain = _read_toolchain(self.repo_root)
        artifact_version = int(dag_meta.get("schemaVersion", 0))

        nodes: list[NodeRecord] = []
        edges: list[EdgeRecord] = []

        module_seen: set[str] = set()
        for decl in _iter_jsonl(decl_file):
            name = str(decl.get("name", "")).strip()
            module = str(decl.get("module", "")).strip()
            if not name or not module:
                continue

            depth_row = depth_by_name.get(name, {})
            process_row = process_by_name.get(name, {})
            capstone = bool(depth_row.get("capstone", False))

            role_raw = str(process_row.get("role", "")).strip() or None
            if role_raw in {"owner", "translator", "coherence", "capstone"}:
                role = role_raw
            else:
                role = _infer_role(name, module, capstone)

            attrs = {
                "decl_kind": decl.get("kind"),
                "doc": decl.get("doc", ""),
                "boundary_class": process_row.get("boundaryClass"),
                "novelty": process_row.get("novelty"),
                "attrs": decl.get("attrs", []),
            }
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

        edges.extend(extra_edges)

        snapshot_meta = {
            "created_at": _utc_now(),
            "source": "leantrail.normalizer",
            "commit_sha": commit_sha,
            "toolchain": toolchain,
            "artifact_version": artifact_version,
            "dag_meta": dag_meta,
            "counts": {
                "nodes": len(nodes),
                "edges": len(edges),
                "depth_rows": len(depth_records),
            },
        }

        return GraphSnapshot(metadata=snapshot_meta, nodes=nodes, edges=edges)
