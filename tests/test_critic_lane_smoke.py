#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        packets = tmp / "critic_packets.jsonl"
        report = tmp / "critic_report.json"
        md = tmp / "critic_report.md"
        prompts = tmp / "critic_prompts.jsonl"
        prompt_report = tmp / "critic_prompt_report.json"
        ingested = tmp / "graph_snapshot.critic.json"
        ingest_report = tmp / "critic_ingest_report.json"
        structural_dedup = tmp / "structural-dedup.json"

        snapshot = ROOT / "tests" / "fixtures" / "sample_graph_snapshot.vacuity.json"
        holes = ROOT / "tests" / "fixtures" / "sample_proof_hole_packets.jsonl"
        structural_dedup.write_text(json.dumps({
            "dedup_families": [{
                "family_id": "family:smoke1",
                "relation_type": "true_dedup_candidate",
                "relation_subtype": "compatibility_alias_candidate",
                "recommended_action": "review_as_alias_family",
                "shared_name_stem": "InfoGeometry.Canonical.",
                "candidate_canonical_endpoint": "InfoGeometry.Canonical.GrandBridge",
                "member_sinks": ["InfoGeometry.Canonical.GrandBridge"],
            }]
        }), encoding="utf-8")

        subprocess.check_call([
            sys.executable,
            str(ROOT / "tools" / "leantrail" / "critic_packets.py"),
            "--snapshot", str(snapshot),
            "--proof-holes", str(holes),
            "--bridge-packets", "",
            "--alignment-packets", "",
            "--out", str(packets),
            "--json-out", str(report),
            "--md-out", str(md),
        ])

        rows = [json.loads(line) for line in packets.read_text(encoding="utf-8").splitlines() if line.strip()]
        assert rows, "expected critic packets"
        kinds = {r["critic_kind"] for r in rows}
        assert "proof_shape_name_mismatch" in kinds
        assert "honest_sorry_triage" in kinds
        assert "orphan_genuine_review" in kinds

        subprocess.check_call([
            sys.executable,
            str(ROOT / "tools" / "leantrail" / "critic_prompt_builder.py"),
            "--packets", str(packets),
            "--out", str(prompts),
            "--md-out", "",
            "--json-out", str(prompt_report),
        ])
        assert prompts.exists() and prompts.stat().st_size > 0

        subprocess.check_call([
            sys.executable,
            str(ROOT / "tools" / "leantrail" / "critic_ingest.py"),
            "--snapshot", str(snapshot),
            "--critic-packets", str(packets),
            "--structural-dedup", str(structural_dedup),
            "--out", str(ingested),
            "--json-out", str(ingest_report),
        ])
        payload = json.loads(ingested.read_text(encoding="utf-8"))
        updated = [n for n in payload["nodes"] if n.get("attrs", {}).get("critic")]
        assert len(updated) >= 3
        grand = next(n for n in payload["nodes"] if n["name"] == "InfoGeometry.Canonical.GrandBridge")
        assert grand.get("attrs", {}).get("structural_dedup", {}).get("relation_subtype") == "compatibility_alias_candidate"

    print("critic lane smoke test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
