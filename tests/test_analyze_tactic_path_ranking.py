import json
import subprocess
import sys
from pathlib import Path

from tools.infra.analyze_tactic_path_ranking import run_analysis


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "analyze_tactic_path_ranking.py"


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, ensure_ascii=True) + "\n" for row in rows), encoding="utf-8")


def _ranking_row(*, row_id: str, positive_score: float, negative_score: float, stall_type: str = "none") -> dict:
    return {
        "schema": "info_geometry.tactic_path_ranking.v1",
        "id": row_id,
        "split": "train",
        "context": {"theorem": f"Demo.{row_id}", "goal_state": "⊢ True"},
        "provenance": {"trace_sources": ["leandojo_v2", "hive"], "authority_stages": ["lean_checked"]},
        "graph_features": {"hodge_harmonic_signal": 0.6 if stall_type != "none" else 0.05},
        "candidates": [
            {
                "edge_id": f"{row_id}-pos",
                "tactic": "trivial",
                "operator_score": positive_score,
                "is_positive": 1,
                "label": 1,
                "stall_type": "none",
                "edge_type": "terminal",
                "sampling_priority": 1.0,
                "balanced_operator_score": positive_score,
            },
            {
                "edge_id": f"{row_id}-neg",
                "tactic": "simp",
                "operator_score": negative_score,
                "is_positive": 0,
                "label": 0,
                "stall_type": stall_type,
                "edge_type": "stall" if stall_type != "none" else "simplification",
                "sampling_priority": 0.5,
                "balanced_operator_score": negative_score,
            },
        ],
    }


def test_analyze_tactic_path_ranking_reports_distribution_and_baseline(tmp_path: Path) -> None:
    src = tmp_path / "ranking.jsonl"
    out = tmp_path / "analysis.json"
    _write_jsonl(
        src,
        [
            _ranking_row(row_id="good", positive_score=0.9, negative_score=0.1),
            _ranking_row(row_id="bad", positive_score=0.2, negative_score=0.8, stall_type="harmonic_stall"),
        ],
    )

    report = run_analysis(src, out, top_k=2)

    assert report["schema"] == "info_geometry.tactic_path_ranking.analysis.v1"
    assert report["rows"] == 2
    assert report["mixed_rows"] == 2
    assert report["stall_types"] == {"harmonic_stall": 1, "none": 3}
    assert report["operator_score_baseline"]["top1_progress_rate"] == 0.5
    assert report["operator_score_baseline"]["top2_progress_rate"] == 1.0
    assert report["operator_score_baseline"]["mean_first_positive_rank"] == 1.5
    assert report["sampling_priority"]["count"] == 4
    assert report["balanced_operator_score"]["mean"] == 0.5
    assert report["by_source_top1"]["hive"]["rows"] == 2
    assert out.exists()


def test_analyze_tactic_path_ranking_handles_empty_input(tmp_path: Path) -> None:
    src = tmp_path / "empty.jsonl"
    out = tmp_path / "analysis.json"
    src.write_text("", encoding="utf-8")

    report = run_analysis(src, out, top_k=3)

    assert report["rows"] == 0
    assert report["operator_score_baseline"]["top1_progress_rate"] == 0.0
    assert report["recommendations"] == ["No ranking rows found. Build reports/training/tactic_path_ranking.jsonl first."]


def test_analyze_tactic_path_ranking_cli(tmp_path: Path) -> None:
    src = tmp_path / "ranking.jsonl"
    out = tmp_path / "analysis.json"
    _write_jsonl(src, [_ranking_row(row_id="cli", positive_score=0.9, negative_score=0.1)])

    subprocess.run(
        [sys.executable, str(SCRIPT), "--input", str(src), "--out", str(out), "--top-k", "1"],
        cwd=REPO_ROOT,
        check=True,
    )

    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["rows"] == 1
    assert report["top_k"] == 1
