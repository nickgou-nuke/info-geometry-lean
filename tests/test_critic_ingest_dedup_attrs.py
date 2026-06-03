from __future__ import annotations

import json
from pathlib import Path

from tools.leantrail.critic_ingest import run


ROOT = Path(__file__).resolve().parents[1]


def test_run_merges_structural_dedup_classification_into_node_attrs(tmp_path: Path) -> None:
    snapshot = ROOT / "tests" / "fixtures" / "sample_graph_snapshot.vacuity.json"
    critic_packets = tmp_path / "critic_packets.jsonl"
    critic_packets.write_text("", encoding="utf-8")

    dedup_report = tmp_path / "structural-dedup.json"
    dedup_report.write_text(
        json.dumps(
            {
                "dedup_families": [
                    {
                        "relation_type": "true_dedup_candidate",
                        "relation_subtype": "compatibility_alias_candidate",
                        "recommended_action": "review_as_alias_family",
                        "shared_name_stem": "InfoGeometry.Canonical.",
                        "candidate_canonical_endpoint": "InfoGeometry.Canonical.GrandBridge",
                        "member_sinks": [
                            "InfoGeometry.Canonical.GrandBridge",
                            "InfoGeometry.Experimental.OpenLemma",
                        ],
                        "family_id": "family:test123",
                    }
                ]
            }
        ),
        encoding="utf-8",
    )

    out = tmp_path / "graph_snapshot.critic.json"
    report = tmp_path / "critic_ingest_report.json"
    run(
        snapshot_path=snapshot,
        critic_packets_path=critic_packets,
        out_path=out,
        json_out=report,
        structural_dedup_path=dedup_report,
    )

    payload = json.loads(out.read_text(encoding="utf-8"))
    grand = next(node for node in payload["nodes"] if node["name"] == "InfoGeometry.Canonical.GrandBridge")
    open_lemma = next(node for node in payload["nodes"] if node["name"] == "InfoGeometry.Experimental.OpenLemma")
    dense = next(node for node in payload["nodes"] if node["name"] == "InfoGeometry.Standalone.DenseTheory")

    for node in (grand, open_lemma):
        dedup = node["attrs"].get("structural_dedup")
        assert dedup is not None
        assert dedup["family_id"] == "family:test123"
        assert dedup["relation_subtype"] == "compatibility_alias_candidate"
        assert dedup["recommended_action"] == "review_as_alias_family"
        assert dedup["candidate_canonical_endpoint"] == "InfoGeometry.Canonical.GrandBridge"
        assert dedup["shared_name_stem"] == "InfoGeometry.Canonical."

    assert "structural_dedup" not in dense.get("attrs", {})

    ingest_report = json.loads(report.read_text(encoding="utf-8"))
    assert ingest_report["dedup_family_count"] == 1
    assert ingest_report["dedup_updated_nodes"] == 2
