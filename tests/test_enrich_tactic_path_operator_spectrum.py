from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools" / "infra"))

from enrich_tactic_path_operator_spectrum import (  # noqa: E402
    ROW_SCHEMA,
    STATS_SCHEMA,
    compute_operator_spectrum,
    enrich_row,
    iter_jsonl,
    run,
)


def _candidate(tactic: str, *, label: int, score: float, stall_type: str = "none") -> dict:
    return {
        "edge_id": f"edge:{tactic}",
        "goal_hash_before": "goal:before",
        "goal_hash_after": f"goal:after:{tactic}",
        "tactic": tactic,
        "edge_type": "terminal" if label == 1 else "failure",
        "operator_score": score,
        "balanced_operator_score": score,
        "sampling_priority": score + 0.1,
        "is_positive": label == 1,
        "label": label,
        "stall_type": stall_type,
        "authority_stage": "lean_checked" if label == 1 else "diagnostic_failure",
    }


def _row(candidates: list[dict]) -> dict:
    return {
        "schema": "info_geometry.tactic_path_ranking.v1",
        "decision_id": "decision:mixed",
        "theorem": "Example.theorem",
        "context": {
            "goal_state": "⊢ True",
            "goal_hash": "goal:before",
        },
        "graph_features": {
            "hodge_harmonic_signal": 0.25,
            "candidate_count": len(candidates),
            "positive_count": sum(1 for c in candidates if c.get("is_positive")),
            "negative_count": sum(1 for c in candidates if not c.get("is_positive")),
            "stall_count": sum(1 for c in candidates if c.get("stall_type") != "none"),
        },
        "provenance": {
            "trace_source": "test",
            "authority_stage": "lean_checked",
            "split": "train",
        },
        "candidates": candidates,
        "authority": {
            "lean_labels_are_authority": True,
            "operator_features_are_diagnostic": True,
        },
    }


def test_compute_operator_spectrum_mixed_decision_point() -> None:
    row = _row(
        [
            _candidate("exact h", label=1, score=0.90),
            _candidate("simp", label=-1, score=0.20, stall_type="harmonic_stall"),
            _candidate("rw [h]", label=0, score=0.35),
        ]
    )

    spectrum = compute_operator_spectrum(row)

    assert spectrum["schema"] == ROW_SCHEMA
    assert spectrum["operator_scope"] == "local_decision_point"
    assert spectrum["diagnostic_only"] is True
    assert spectrum["authority"]["lean_remains_proof_authority"] is True
    assert spectrum["drazin_proxy"]["core_mass"] > 0
    assert spectrum["drazin_proxy"]["nilpotent_stall_mass"] > 0
    assert spectrum["drazin_proxy"]["transient_mass"] > 0
    assert spectrum["hodge_proxy"]["harmonic_residual"] > 0
    assert 0 <= spectrum["dirac_proxy"]["chiral_balance"] <= 1


def test_enrich_row_adds_candidate_operator_weights() -> None:
    row = _row(
        [
            _candidate("exact h", label=1, score=0.85),
            _candidate("simp", label=-1, score=0.30, stall_type="harmonic_stall"),
        ]
    )

    enriched = enrich_row(row, alpha=0.10, beta=0.05, gamma=0.10)

    assert enriched["operator_spectrum"]["schema"] == ROW_SCHEMA
    assert enriched["operator_spectrum"]["diagnostic_only"] is True
    for candidate in enriched["candidates"]:
        op = candidate["operator_enrichment"]
        assert op["schema"] == "info_geometry.tactic_operator_spectrum_candidate.v1"
        assert op["diagnostic_only"] is True
        assert op["authority"]["not_a_proof"] is True
        assert candidate["final_operator_sampling_weight"] >= 0


def test_repeated_stall_family_has_cycle_pressure() -> None:
    row = _row(
        [
            _candidate("simp", label=-1, score=0.15, stall_type="harmonic_stall"),
            _candidate("simp [h]", label=-1, score=0.10, stall_type="harmonic_stall"),
            _candidate("simp only [h]", label=-1, score=0.12, stall_type="harmonic_stall"),
        ]
    )

    spectrum = compute_operator_spectrum(row)

    assert spectrum["drazin_proxy"]["core_mass"] == 0
    assert spectrum["drazin_proxy"]["nilpotent_stall_mass"] > 0
    assert spectrum["hodge_proxy"]["cycle_pressure"] > 0


def test_iter_jsonl_missing_input_fails(tmp_path: Path) -> None:
    missing = tmp_path / "missing.jsonl"

    with pytest.raises(SystemExit):
        list(iter_jsonl(missing))


def test_run_writes_enriched_rows_and_stats(tmp_path: Path) -> None:
    input_path = tmp_path / "ranking.jsonl"
    output_path = tmp_path / "operator_enriched.jsonl"
    stats_path = tmp_path / "stats.json"
    input_row = _row(
        [
            _candidate("exact h", label=1, score=0.95),
            _candidate("simp", label=-1, score=0.10, stall_type="harmonic_stall"),
        ]
    )
    input_path.write_text(json.dumps(input_row) + "\n", encoding="utf-8")

    stats = run(input_path=input_path, out_path=output_path, stats_path=stats_path)

    rows = [json.loads(line) for line in output_path.read_text(encoding="utf-8").splitlines()]
    persisted_stats = json.loads(stats_path.read_text(encoding="utf-8"))
    assert stats == persisted_stats
    assert stats["schema"] == STATS_SCHEMA
    assert stats["rows"] == 1
    assert stats["candidate_count"] == 2
    assert rows[0]["operator_spectrum"]["authority"]["diagnostic_prior_only"] is True


def test_run_groups_rows_by_decision_point_before_enrichment(tmp_path: Path) -> None:
    input_path = tmp_path / "ranking.jsonl"
    output_path = tmp_path / "operator_enriched.jsonl"
    stats_path = tmp_path / "stats.json"
    row_success = _row([_candidate("exact h", label=1, score=0.90)])
    row_stall = _row([_candidate("simp", label=-1, score=0.10, stall_type="harmonic_stall")])
    row_success["decision_id"] = "fragment:success"
    row_stall["decision_id"] = "fragment:stall"
    row_success["context"]["goal_hash"] = "shared-goal"
    row_stall["context"]["goal_hash"] = "shared-goal"
    input_path.write_text(
        json.dumps(row_success) + "\n" + json.dumps(row_stall) + "\n",
        encoding="utf-8",
    )

    stats = run(input_path=input_path, out_path=output_path, stats_path=stats_path)

    rows = [json.loads(line) for line in output_path.read_text(encoding="utf-8").splitlines()]
    assert stats["rows"] == 2
    assert stats["decision_point_count"] == 1
    for row in rows:
        spectrum = row["operator_spectrum"]
        assert spectrum["decision_point_key"] == "shared-goal"
        assert spectrum["decision_point_row_count"] == 2
        assert spectrum["transition_proxy"]["candidate_count"] == 2
        assert spectrum["drazin_proxy"]["core_mass"] > 0
        assert spectrum["drazin_proxy"]["nilpotent_stall_mass"] > 0
