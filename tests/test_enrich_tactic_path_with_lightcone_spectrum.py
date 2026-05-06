import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools" / "infra"))

from enrich_tactic_path_with_lightcone_spectrum import enrich_rows, iter_jsonl, load_spectral_report


def test_enrich_rows_adds_context_and_candidate_weights(tmp_path: Path) -> None:
    report = {
        "schema": "info_geometry.local_lightcone_spectral_filter.v1",
        "drazin": {"nonzero_schur_dim": 2, "index": 1},
        "hodge": {"harmonic_dim": 1},
        "nodes": [
            {"name": "Thm", "drazin_core_weight": 2.0, "nilpotent_residue_weight": 0.5, "hodge_harmonic_weight": 1.0},
            {"name": "Other", "drazin_core_weight": 1.0, "nilpotent_residue_weight": 2.0, "hodge_harmonic_weight": 0.0},
        ],
    }
    rows = [
        {
            "id": "row1",
            "theorem": "Thm",
            "candidates": [
                {"edge_id": "e1", "tactic": "exact h", "sampling_priority": 1.0, "trace_source": "hive"},
                {"edge_id": "e2", "tactic": "simp", "sampling_priority": 0.5, "declaration": "Other", "trace_source": "hive"},
            ],
        }
    ]

    enriched, stats = enrich_rows(rows, report, source_report=tmp_path / "spectrum.json", apex="Thm", alpha=0.1, beta=0.05, gamma=0.1)

    assert stats["rows"] == 1
    assert stats["candidate_count"] == 2
    assert enriched[0]["lightcone_operator_context"]["schema"] == "info_geometry.tactic_lightcone_operator_context.v1"
    assert enriched[0]["lightcone_operator_context"]["diagnostic_only"] is True
    candidates = enriched[0]["candidates"]
    assert candidates[0]["operator_enrichment"]["schema"] == "info_geometry.tactic_lightcone_operator_enrichment.v1"
    assert "hodge_harmonic_weight" in candidates[0]["operator_enrichment"]
    assert "hodge_boundary_penalty" not in candidates[0]["operator_enrichment"]
    assert candidates[0]["final_operator_sampling_weight"] > 1.0
    assert candidates[1]["operator_enrichment"]["nilpotent_penalty"] == 1.0


def test_load_spectral_report_rejects_wrong_schema(tmp_path: Path) -> None:
    path = tmp_path / "bad.json"
    path.write_text(json.dumps({"schema": "wrong"}), encoding="utf-8")
    try:
        load_spectral_report(path)
    except SystemExit as exc:
        assert "unexpected spectral report schema" in str(exc)
    else:
        raise AssertionError("expected SystemExit")


def test_iter_jsonl_missing_input_fails(tmp_path: Path) -> None:
    missing = tmp_path / "missing.jsonl"
    try:
        list(iter_jsonl(missing))
    except SystemExit as exc:
        assert "input JSONL does not exist" in str(exc)
    else:
        raise AssertionError("expected SystemExit")
