#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

SEVERITY_RANK = {"high": 3, "medium": 2, "low": 1, "info": 0, "unknown": 0}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            raw = line.strip()
            if not raw:
                continue
            try:
                obj = json.loads(raw)
            except Exception:
                continue
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def as_dict(value: Any) -> dict[str, Any]:
    return value if isinstance(value, dict) else {}


def build_dedup_index(payload: dict[str, Any]) -> dict[str, list[dict[str, Any]]]:
    by_target: dict[str, list[dict[str, Any]]] = {}
    for row in payload.get("dedup_families", []):
        if not isinstance(row, dict):
            continue
        members = row.get("member_sinks", [])
        if not isinstance(members, list):
            continue
        for member in members:
            target = str(member)
            if target:
                by_target.setdefault(target, []).append(row)
    return by_target


def merge_node_critic(node: dict[str, Any], packets: list[dict[str, Any]]) -> bool:
    if not packets:
        return False
    attrs = as_dict(node.get("attrs"))
    attrs = dict(attrs)
    existing = as_dict(attrs.get("critic"))

    packet_refs = list(existing.get("critic_packet_refs", [])) if isinstance(existing.get("critic_packet_refs"), list) else []
    for p in packets:
        pid = str(p.get("packet_id", ""))
        if pid and pid not in packet_refs:
            packet_refs.append(pid)

    top = sorted(
        packets,
        key=lambda p: (
            -SEVERITY_RANK.get(str(p.get("severity", "unknown")), 0),
            -float(p.get("confidence", 0.0)),
            str(p.get("critic_kind", "")),
        ),
    )[0]

    counts_by_kind: dict[str, int] = {}
    max_severity = "unknown"
    for p in packets:
        kind = str(p.get("critic_kind", "unknown"))
        counts_by_kind[kind] = counts_by_kind.get(kind, 0) + 1
        sev = str(p.get("severity", "unknown"))
        if SEVERITY_RANK.get(sev, 0) > SEVERITY_RANK.get(max_severity, 0):
            max_severity = sev

    attrs["critic"] = {
        **existing,
        "status": "review_requested",
        "updated_at": utc_now(),
        "top_issue": top.get("critic_kind"),
        "severity": max_severity,
        "confidence": float(top.get("confidence", 0.0)),
        "critic_packet_refs": packet_refs,
        "counts_by_kind": counts_by_kind,
        "source_modification_allowed": False,
    }
    node["attrs"] = attrs
    return True


def merge_node_structural_dedup(node: dict[str, Any], families: list[dict[str, Any]]) -> bool:
    if not families:
        return False
    attrs = as_dict(node.get("attrs"))
    attrs = dict(attrs)
    existing = as_dict(attrs.get("structural_dedup"))
    top = sorted(
        families,
        key=lambda row: (
            0 if str(row.get("relation_subtype", "")) == "compatibility_alias_candidate" else 1,
            -float(row.get("family_score", 0.0) or 0.0),
            str(row.get("family_id", "")),
        ),
    )[0]
    family_ids = list(existing.get("family_ids", [])) if isinstance(existing.get("family_ids"), list) else []
    for row in families:
        fid = str(row.get("family_id", ""))
        if fid and fid not in family_ids:
            family_ids.append(fid)
    attrs["structural_dedup"] = {
        **existing,
        "status": "classified",
        "updated_at": utc_now(),
        "family_id": str(top.get("family_id", "")),
        "family_ids": family_ids,
        "relation_type": str(top.get("relation_type", "true_dedup_candidate")),
        "relation_subtype": str(top.get("relation_subtype", "true_dedup_candidate")),
        "recommended_action": str(top.get("recommended_action", "review_for_contraction")),
        "candidate_canonical_endpoint": str(top.get("candidate_canonical_endpoint", "")),
        "shared_name_stem": str(top.get("shared_name_stem", "")),
        "member_count": int(top.get("member_count", len(top.get("member_sinks", [])) if isinstance(top.get("member_sinks"), list) else 0) or 0),
        "source_modification_allowed": False,
    }
    node["attrs"] = attrs
    return True


def run(*, snapshot_path: Path, critic_packets_path: Path, out_path: Path, json_out: Path, structural_dedup_path: Path | None = None) -> dict[str, Any]:
    snapshot = load_json(snapshot_path)
    packets = list(iter_jsonl(critic_packets_path))
    by_target: dict[str, list[dict[str, Any]]] = {}
    for p in packets:
        target = str(p.get("target", ""))
        if target:
            by_target.setdefault(target, []).append(p)
    structural_dedup = load_json(structural_dedup_path) if structural_dedup_path and structural_dedup_path.exists() else {}
    dedup_by_target = build_dedup_index(structural_dedup)

    updated = 0
    dedup_updated = 0
    for node in snapshot.get("nodes", []):
        if not isinstance(node, dict):
            continue
        targets = [str(node.get("id", "")), str(node.get("name", ""))]
        node_packets: list[dict[str, Any]] = []
        seen: set[str] = set()
        node_families: list[dict[str, Any]] = []
        seen_families: set[str] = set()
        for t in targets:
            for p in by_target.get(t, []):
                pid = str(p.get("packet_id", ""))
                if pid in seen:
                    continue
                seen.add(pid)
                node_packets.append(p)
            for row in dedup_by_target.get(t, []):
                fid = str(row.get("family_id", ""))
                if fid in seen_families:
                    continue
                seen_families.add(fid)
                node_families.append(row)
        if merge_node_critic(node, node_packets):
            updated += 1
        if merge_node_structural_dedup(node, node_families):
            dedup_updated += 1

    metadata = as_dict(snapshot.get("metadata"))
    metadata = dict(metadata)
    metadata["critic_ingest"] = {
        "created_at": utc_now(),
        "critic_packets": str(critic_packets_path),
        "packet_count": len(packets),
        "updated_nodes": updated,
        "structural_dedup": str(structural_dedup_path) if structural_dedup_path else "",
        "dedup_family_count": len(structural_dedup.get("dedup_families", [])) if isinstance(structural_dedup.get("dedup_families", []), list) else 0,
        "dedup_updated_nodes": dedup_updated,
        "source_modification_allowed": False,
    }
    snapshot["metadata"] = metadata

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(snapshot, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")

    report = {
        "created_at": utc_now(),
        "snapshot": str(snapshot_path),
        "critic_packets": str(critic_packets_path),
        "structural_dedup": str(structural_dedup_path) if structural_dedup_path else "",
        "output_snapshot": str(out_path),
        "packet_count": len(packets),
        "updated_nodes": updated,
        "dedup_family_count": len(structural_dedup.get("dedup_families", [])) if isinstance(structural_dedup.get("dedup_families", []), list) else 0,
        "dedup_updated_nodes": dedup_updated,
        "source_modification_allowed": False,
    }
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Merge LeanTrail critic packets into graph snapshot attrs.critic.")
    parser.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.vacuity.json")
    parser.add_argument("--critic-packets", default="artifacts/leantrail/critic_packets.jsonl")
    parser.add_argument("--structural-dedup", default="")
    parser.add_argument("--out", default="artifacts/leantrail/graph_snapshot.critic.json")
    parser.add_argument("--json-out", default="artifacts/leantrail/critic_ingest_report.json")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    snapshot_path = Path(args.snapshot).resolve()
    packets_path = Path(args.critic_packets).resolve()
    if not snapshot_path.exists():
        raise FileNotFoundError(f"Snapshot not found: {snapshot_path}")
    if not packets_path.exists():
        raise FileNotFoundError(f"Critic packets not found: {packets_path}")
    report = run(
        snapshot_path=snapshot_path,
        critic_packets_path=packets_path,
        out_path=Path(args.out).resolve(),
        json_out=Path(args.json_out).resolve(),
        structural_dedup_path=Path(args.structural_dedup).resolve() if args.structural_dedup else None,
    )
    print(f"Critic attrs merged: {report['output_snapshot']} (updated_nodes={report['updated_nodes']})")
    print(f"Operation report written: {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
