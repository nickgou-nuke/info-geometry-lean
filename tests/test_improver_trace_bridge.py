from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools" / "infra"))

from improver_trace_bridge import SCHEMA, STATS_SCHEMA, iter_records, normalize_row, run  # noqa: E402


def test_normalize_improved_length_rewrite_candidate(tmp_path: Path) -> None:
    source = tmp_path / "improver.json"
    row = {
        "repo": "Repo",
        "file": "A.lean",
        "decl": "theorem t : True",
        "method": "prompt_basic",
        "metric": "LENGTH",
        "og_correct": True,
        "new_correct": True,
        "og_score": 5,
        "new_score": 3,
        "og_raw": "theorem t : True := by trivial",
        "new_raw": "theorem t : True := by exact True.intro",
    }

    normalized = normalize_row(source, row)

    assert normalized["schema"] == SCHEMA
    assert normalized["metric"]["direction"] == "MIN"
    assert normalized["metric"]["improvement_label"] == "improved"
    assert normalized["labels"]["authority_stage"] == "verified_improvement_candidate"
    assert normalized["labels"]["usable_as_rewrite_positive"] is True
    assert normalized["authority"]["requires_repo_revalidation"] is True


def test_normalize_failed_rewrite_is_failure_telemetry(tmp_path: Path) -> None:
    source = tmp_path / "improver.json"
    row = {
        "decl": "theorem t : False",
        "metric": "COMPLETION",
        "correct": False,
        "errors": "error: unsolved goals",
        "score": None,
    }

    normalized = normalize_row(source, row)

    assert normalized["labels"]["authority_stage"] == "failed_or_unverified_rewrite"
    assert normalized["labels"]["usable_as_failure_telemetry"] is True
    assert normalized["correctness"]["new_error_count"] >= 1
    assert normalized["authority"]["not_a_proof"] is True


def test_run_reads_csv_and_writes_stats(tmp_path: Path) -> None:
    input_path = tmp_path / "improver.csv"
    out_path = tmp_path / "out.jsonl"
    stats_path = tmp_path / "stats.json"
    with input_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=["decl", "metric", "og_correct", "new_correct", "og_score", "new_score"])
        writer.writeheader()
        writer.writerow({"decl": "A", "metric": "LENGTH", "og_correct": "True", "new_correct": "True", "og_score": "4", "new_score": "2"})
        writer.writerow({"decl": "B", "metric": "LENGTH", "og_correct": "True", "new_correct": "False", "og_score": "4", "new_score": ""})

    stats = run(input_path, out_path, stats_path)

    rows = [json.loads(line) for line in out_path.read_text(encoding="utf-8").splitlines()]
    persisted = json.loads(stats_path.read_text(encoding="utf-8"))
    assert stats == persisted
    assert stats["schema"] == STATS_SCHEMA
    assert stats["rows"] == 2
    assert stats["metric_counts"] == {"LENGTH": 2}
    assert stats["rewrite_positive_rows"] == 1
    assert rows[0]["authority"]["diagnostic_only"] is True


def test_iter_records_missing_input_fails(tmp_path: Path) -> None:
    with pytest.raises(SystemExit):
        list(iter_records(tmp_path / "missing.csv"))
