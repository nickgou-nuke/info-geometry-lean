from __future__ import annotations

import json
import re
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

    def ensure_loaded(self) -> None:
        if self.store is not None:
            return
        if not self.snapshot_path.exists():
            self.snapshot_path.parent.mkdir(parents=True, exist_ok=True)
            build_snapshot(self.repo_root, self.snapshot_path)

        payload = json.loads(self.snapshot_path.read_text(encoding="utf-8"))
        snapshot = GraphSnapshot.from_dict(payload)
        self.store = GraphStore(snapshot)

    def search(self, q: str, limit: int = 50) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        return {"query": q, "results": self.store.search(q, limit=limit)}

    def decl(self, name: str) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        row = self.store.get_decl(name)
        if row is None:
            return {"found": False, "name": name}
        return {"found": True, "name": name, **row}

    def neighborhood(self, name: str, radius: int = 2) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        data = self.store.neighborhood(name, radius=radius)
        return {"name": name, "radius": radius, **data}

    def path(self, src: str, dst: str, lawful_only: bool = True) -> dict[str, Any]:
        self.ensure_loaded()
        assert self.store is not None
        return {
            "from": src,
            "to": dst,
            "lawful_only": lawful_only,
            **self.store.shortest_path(src, dst, lawful_only=lawful_only),
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
