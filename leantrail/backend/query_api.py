from __future__ import annotations

import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import jsonschema

from tools.infra.candidate_bridge_packet import validate_packet

from .indexer import build_snapshot
from .models import GraphSnapshot
from .rpc_adapter import LeanRPCAdapter
from .store import GraphStore


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _slug(text: str) -> str:
    out = re.sub(r"[^a-zA-Z0-9]+", "-", text.strip().lower()).strip("-")
    return out[:64] or "bridge"


def _safe_git_head(repo_root: Path) -> str:
    try:
        out = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo_root, text=True)
    except Exception:
        return "unknown"
    return out.strip() or "unknown"


def _read_json_if_exists(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    return payload if isinstance(payload, dict) else {}


def _iter_jsonl_if_exists(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    try:
        with path.open(encoding="utf-8") as handle:
            for line in handle:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                if isinstance(row, dict):
                    rows.append(row)
    except Exception:
        return []
    return rows


def _snapshot_is_stale(repo_root: Path, snapshot_path: Path) -> bool:
    if not snapshot_path.exists():
        return True

    snapshot_payload = _read_json_if_exists(snapshot_path)
    snapshot_meta = snapshot_payload.get("metadata")
    if not isinstance(snapshot_meta, dict):
        return True

    snapshot_commit = str(snapshot_meta.get("commit_sha", "")).strip()
    current_commit = _safe_git_head(repo_root)
    if snapshot_commit and current_commit != "unknown" and snapshot_commit != current_commit:
        return True

    dag_meta_path = repo_root / "artifacts" / "dag" / "index" / "meta.json"
    dag_meta = _read_json_if_exists(dag_meta_path)
    if not dag_meta:
        return False

    snapshot_dag_meta = snapshot_meta.get("dag_meta")
    if not isinstance(snapshot_dag_meta, dict):
        return True

    for key in ("timestamp", "sourceHash", "oleanHash", "nodeCount", "edgeCount", "morphismCount"):
        if snapshot_dag_meta.get(key) != dag_meta.get(key):
            return True

    return False


class LeanTrailQueryAPI:
    def __init__(
        self,
        repo_root: Path,
        snapshot_path: Path,
        bridge_dir: Path,
        bridge_schema_path: Path,
    ) -> None:
        self.repo_root = repo_root
        self.snapshot_path = snapshot_path
        self.bridge_dir = bridge_dir
        self.bridge_schema_path = bridge_schema_path
        self.rpc = LeanRPCAdapter(repo_root)
        self.store: GraphStore | None = None
        self._lawful_cones_by_name: dict[str, dict[str, Any]] | None = None
        self._typed_paths_by_src: dict[str, list[dict[str, Any]]] | None = None

    def _ensure_process_geometry_loaded(self) -> None:
        if self._lawful_cones_by_name is not None and self._typed_paths_by_src is not None:
            return

        process_flow_dir = self.repo_root / "artifacts" / "dag" / "process-flow"
        lawful_cones_file = process_flow_dir / "lawful-cones.jsonl"
        lawful_typed_paths_file = process_flow_dir / "lawful-typed-composite-paths.jsonl"

        lawful_cones_by_name: dict[str, dict[str, Any]] = {}
        for row in _iter_jsonl_if_exists(lawful_cones_file):
            base = row.get("base")
            base = base if isinstance(base, dict) else {}
            apex = base.get("apex")
            apex = apex if isinstance(apex, dict) else {}
            name = str(apex.get("decl", "")).strip()
            if name:
                lawful_cones_by_name[name] = row

        typed_paths_by_src: dict[str, list[dict[str, Any]]] = {}
        for row in _iter_jsonl_if_exists(lawful_typed_paths_file):
            base = row.get("base")
            base = base if isinstance(base, dict) else {}
            src = str(base.get("src", "")).strip()
            if src:
                typed_paths_by_src.setdefault(src, []).append(row)

        self._lawful_cones_by_name = lawful_cones_by_name
        self._typed_paths_by_src = typed_paths_by_src

    def ensure_loaded(self) -> None:
        if self.store is not None:
            return
        if _snapshot_is_stale(self.repo_root, self.snapshot_path):
            self.snapshot_path.parent.mkdir(parents=True, exist_ok=True)
            build_snapshot(self.repo_root, self.snapshot_path)

        payload = json.loads(self.snapshot_path.read_text(encoding="utf-8"))
        snapshot = GraphSnapshot.from_dict(payload)
        self.store = GraphStore(snapshot)

    def search(self, q: str, limit: int = 50) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        return {"query": q, "results": self.store.search(q, limit=limit)}

    def dedup_candidates(self, status: str = "active", limit: int = 50) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        return self.store.dedup_candidates(status=status, limit=limit)

    def decl(self, name: str) -> dict[str, Any]:
        self.ensure_loaded()
        self._ensure_process_geometry_loaded()
        assert self.store is not None
        row = self.store.get_decl(name)
        if row is None:
            return {"found": False, "name": name}
        assert self._lawful_cones_by_name is not None
        assert self._typed_paths_by_src is not None
        return {
            "found": True,
            "name": name,
            "lawful_cone": self._lawful_cones_by_name.get(name),
            "lawful_typed_paths": self._typed_paths_by_src.get(name, []),
            **row,
        }

    def neighborhood(self, name: str, radius: int = 2) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        data = self.store.neighborhood(name, radius=radius)
        return {"name": name, "radius": radius, **data}

    def path(
        self,
        src: str,
        dst: str,
        lawful_only: bool = True,
        state_policy: str = "any",
    ) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        return {
            "from": src,
            "to": dst,
            "lawful_only": lawful_only,
            "state_policy": state_policy,
            **self.store.shortest_path_with_state_policy(
                src,
                dst,
                lawful_only=lawful_only,
                state_policy=state_policy,
            ),
        }

    def proofstate(self, file: str, line: int, col: int) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None

        rpc_payload = self.rpc.proof_state(file=file, line=line, col=col)

        nearby: list[dict[str, Any]] = []
        for node in self.store.snapshot.nodes:
            if node.kind != "Declaration":
                continue
            if node.file != file:
                continue
            if node.line is None:
                continue
            nearby.append(
                {
                    "name": node.name,
                    "line": node.line,
                    "distance": abs(node.line - line),
                    "module": node.module,
                }
            )
        nearby.sort(key=lambda row: row["distance"])
        return {
            "rpc": rpc_payload,
            "nearby_declarations": nearby[:12],
        }

    def coherence_hotspots(self, limit: int = 25) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        return {"hotspots": self.store.coherence_hotspots(limit=limit)}

    def cone_hotspots(
        self,
        limit: int = 25,
        alpha: float = 1.0,
        beta: float = 1.5,
        gamma: float = 3.0,
        min_score: float = 0.0,
    ) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        return {
            "weights": {"alpha": alpha, "beta": beta, "gamma": gamma},
            "min_score": min_score,
            "hotspots": self.store.cone_hotspots(
                limit=limit,
                alpha=alpha,
                beta=beta,
                gamma=gamma,
                min_score=min_score,
            ),
        }

    def holonomy_hotspots(
        self,
        limit: int = 25,
        alpha: float = 1.5,
        beta: float = 2.0,
        gamma: float = 3.0,
        min_score: float = 0.0,
    ) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        return {
            "weights": {"alpha": alpha, "beta": beta, "gamma": gamma},
            "min_score": min_score,
            "hotspots": self.store.holonomy_hotspots(
                limit=limit,
                alpha=alpha,
                beta=beta,
                gamma=gamma,
                min_score=min_score,
            ),
        }

    def create_bridge_candidate(self, payload: dict[str, Any]) -> dict[str, Any]:
        self.ensure_loaded()

        schema = json.loads(self.bridge_schema_path.read_text(encoding="utf-8"))
        jsonschema.validate(instance=payload, schema=schema)

        packet_id = str(payload.get("packet_id", "")).strip()
        if not packet_id:
            ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
            packet_id = f"cbp-{ts}-{_slug(payload.get('claimed_invariant', 'bridge'))}"

        packet: dict[str, Any] = {
            "packet_id": packet_id,
            "created_at": _utc_now(),
            "source_owner_surfaces": payload["source_owner_surfaces"],
            "target_owner_surfaces": payload["target_owner_surfaces"],
            "claimed_invariant": payload["claimed_invariant"],
            "proposed_map": {
                "map_kind": payload["map_kind"],
                "map_expression": payload["map_expression"],
            },
            "outcome_class": payload["outcome_class"],
            "evidence_refs": payload.get("evidence_refs", []),
            "unresolved_assumptions": payload.get("unresolved_assumptions", []),
            "status": payload.get("status", "draft"),
        }

        if payload.get("forbidden_moves"):
            packet["forbidden_moves"] = payload["forbidden_moves"]

        if payload["outcome_class"] in {"equivalence", "obstruction"}:
            packet["theorem_target"] = payload["theorem_target"]

        if payload["outcome_class"] == "obstruction":
            packet["mismatch_object"] = payload["mismatch_object"]

        if payload["outcome_class"] == "discard":
            packet["discard_reason"] = payload["discard_reason"]

        errors = validate_packet(packet)
        if errors:
            raise ValueError("; ".join(errors))

        self.bridge_dir.mkdir(parents=True, exist_ok=True)
        out_file = self.bridge_dir / f"{packet_id}.json"
        out_file.write_text(json.dumps(packet, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
        try:
            out_path = str(out_file.relative_to(self.repo_root))
        except ValueError:
            out_path = str(out_file)

        return {
            "ok": True,
            "packet_id": packet_id,
            "path": out_path,
            "packet": packet,
        }
