from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools" / "infra"))

from lean_auto_trace_bridge import SCHEMA, STATS_SCHEMA, iter_records, normalize_row, run  # noqa: E402


def test_normalize_trusted_smt_trace_is_not_authority(tmp_path: Path) -> None:
    source = tmp_path / "trace.json"
    row = {
        "theorem": "Example.bad",
        "goal": "⊢ False",
        "solver": "z3",
        "solved": True,
        "trusted": True,
        "proof": "autoSMTSorry False",
        "unsat_core": [0, 2],
        "local_lemmas": ["h1", "h2", "h3"],
        "premise_selection": True,
    }

    normalized = normalize_row(source, row)

    assert normalized["schema"] == SCHEMA
    assert normalized["lean_auto"]["solver"]["trusted_external_solver"] is True
    assert normalized["labels"]["authority_stage"] == "trusted_external_not_promotable"
    assert normalized["labels"]["usable_as_training_positive"] is False
    assert normalized["labels"]["usable_as_premise_selection_prior"] is True
    assert normalized["authority"]["external_solver_claim_not_authority"] is True


def test_normalize_reconstructed_native_trace_can_be_training_positive(tmp_path: Path) -> None:
    source = tmp_path / "trace.json"
    row = {
        "declaration": "Example.good",
        "solver": "native",
        "solved": True,
        "proof_reconstructed": True,
        "user_lemmas": ["h"],
        "inhabitation_facts": ["inst"],
    }

    normalized = normalize_row(source, row)

    assert normalized["lean_auto"]["solver"]["proof_status"] == "lean_reconstructed_candidate"
    assert normalized["labels"]["authority_stage"] == "lean_reconstructed_candidate"
    assert normalized["labels"]["usable_as_training_positive"] is True
    assert normalized["authority"]["not_a_certificate"] is True


def test_run_reads_jsonl_and_writes_stats(tmp_path: Path) -> None:
    input_path = tmp_path / "traces.jsonl"
    out_path = tmp_path / "out.jsonl"
    stats_path = tmp_path / "stats.json"
    input_path.write_text(
        json.dumps({"theorem": "A", "solver": "z3", "solved": False})
        + "\n"
        + json.dumps({"theorem": "B", "solver": "native", "solved": True, "proof_reconstructed": True})
        + "\n",
        encoding="utf-8",
    )

    stats = run(input_path, out_path, stats_path)

    rows = [json.loads(line) for line in out_path.read_text(encoding="utf-8").splitlines()]
    persisted = json.loads(stats_path.read_text(encoding="utf-8"))
    assert stats == persisted
    assert stats["schema"] == STATS_SCHEMA
    assert stats["rows"] == 2
    assert stats["solver_counts"] == {"native": 1, "z3": 1}
    assert rows[0]["authority"]["diagnostic_only"] is True


def test_iter_records_missing_input_fails(tmp_path: Path) -> None:
    with pytest.raises(SystemExit):
        list(iter_records(tmp_path / "missing.jsonl"))
