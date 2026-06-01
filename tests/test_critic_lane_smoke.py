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

        snapshot = ROOT / "tests" / "fixtures" / "sample_graph_snapshot.vacuity.json"
        holes = ROOT / "tests" / "fixtures" / "sample_proof_hole_packets.jsonl"

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
            "--out", str(ingested),
            "--json-out", str(ingest_report),
        ])
        payload = json.loads(ingested.read_text(encoding="utf-8"))
        updated = [n for n in payload["nodes"] if n.get("attrs", {}).get("critic")]
        assert len(updated) >= 3

    print("critic lane smoke test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
