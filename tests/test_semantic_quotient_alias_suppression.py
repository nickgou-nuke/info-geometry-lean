from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_semantic_quotient_suppresses_compatibility_alias_dedup_by_default(tmp_path: Path) -> None:
    hotspots = tmp_path / "hotspots.json"
    fibers = tmp_path / "fibers.json"
    dedup = tmp_path / "structural-dedup.json"
    surface = tmp_path / "surface.json"
    json_out = tmp_path / "semantic-quotient.json"
    md_out = tmp_path / "semantic-quotient.md"

    hotspots.write_text(
        json.dumps(
            {
                "rows": [
                    {"module": "InfoGeometry.Canonical.BohmMadelungOperatorialBridge", "selector_score": 100.0},
                    {"module": "InfoGeometry.LLM.SinkhornDefectFlow", "selector_score": 80.0},
                ]
            }
        ),
        encoding="utf-8",
    )
    fibers.write_text(json.dumps({"packet_fibers": []}), encoding="utf-8")
    dedup.write_text(
        json.dumps(
            {
                "dedup_families": [
                    {
                        "relation_subtype": "compatibility_alias_candidate",
                        "recommended_action": "review_as_alias_family",
                        "family_score": 20.0,
                        "shared_sink_family": ["InfoGeometry.Canonical.BohmMadelungOperatorialBridge"],
                    },
                    {
                        "relation_subtype": "true_dedup_candidate",
                        "recommended_action": "review_for_contraction",
                        "family_score": 38.0,
                        "shared_sink_family": ["InfoGeometry.LLM.SinkhornDefectFlow"],
                    },
                ]
            }
        ),
        encoding="utf-8",
    )
    surface.write_text(json.dumps({"rows": []}), encoding="utf-8")

    subprocess.check_call(
        [
            sys.executable,
            str(ROOT / "tools" / "infra" / "generate_semantic_quotient.py"),
            "--hotspots",
            str(hotspots),
            "--fibers",
            str(fibers),
            "--dedup",
            str(dedup),
            "--surface",
            str(surface),
            "--json-out",
            str(json_out),
            "--md-out",
            str(md_out),
            "--top",
            "10",
        ]
    )

    payload = json.loads(json_out.read_text(encoding="utf-8"))
    rows = {row["module"]: row for row in payload["hotspot_rows"]}

    bohm = rows["InfoGeometry.Canonical.BohmMadelungOperatorialBridge"]
    sinkhorn = rows["InfoGeometry.LLM.SinkhornDefectFlow"]

    assert bohm["dedup_family_count"] == 0
    assert bohm["dedup_family_score"] == 0.0
    assert bohm["suppressed_alias_dedup_family_count"] == 1
    assert bohm["suppressed_alias_dedup_family_score"] == 20.0

    assert sinkhorn["dedup_family_count"] == 1
    assert sinkhorn["dedup_family_score"] == 38.0
    assert sinkhorn["suppressed_alias_dedup_family_count"] == 0

    summary = payload["summary"]
    assert summary["suppressed_alias_dedup_family_count"] == 1
