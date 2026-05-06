import json
import subprocess
import sys
from pathlib import Path

from tools.infra.analyze_stall_distributions import run_analysis

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "analyze_stall_distributions.py"


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, ensure_ascii=True) + "\n" for row in rows), encoding="utf-8")


def test_analyze_stalls_aggregates_distribution(tmp_path: Path) -> None:
    dataset = tmp_path / "ranking.jsonl"
    stats = tmp_path / "stats.json"
    out = tmp_path / "analysis.json"

    _write_jsonl(
        dataset,
        [
            {
                "schema": "info_geometry.tactic_path_ranking.v1",
                "split": "train",
                "context": {"theorem": "T.one"},
                "graph_features": {"cone_depth": 1},
                "candidates": [
                    {"label": 1, "stall_type": "none"},
                    {"label": 0, "stall_type": "harmonic_stall"},
                ],
            },
            {
                "schema": "info_geometry.tactic_path_ranking.v1",
                "split": "test",
                "context": {"theorem": "T.two"},
                "graph_features": {"cone_depth": 7},
                "candidates": [
                    {"label": 0, "stall_type": "type_mismatch"},
                    {"label": 0, "stall_type": "none"},
                ],
            },
        ],
    )
    stats.write_text(json.dumps({"schema": "info_geometry.tactic_path_ranking.summary.v1", "rows": 2}), encoding="utf-8")

    result = run_analysis(dataset, stats, out, top_k=5)

    assert result["totals"]["decision_points"] == 2
    assert result["totals"]["candidates"] == 4
    assert result["totals"]["stall"] == 2
    assert result["stall_types"]["harmonic_stall"] == 1
    assert result["stall_types"]["type_mismatch"] == 1
    assert result["by_split"]["train"]["stall_ratio"] == 0.5
    assert result["by_cone_depth_bucket"]["6-10"]["stall_ratio"] == 0.5
    assert result["authority_boundary"]["lean_remains_proof_authority"] is True


def test_analyze_stalls_cli(tmp_path: Path) -> None:
    dataset = tmp_path / "ranking.jsonl"
    out = tmp_path / "analysis.json"
    _write_jsonl(
        dataset,
        [
            {
                "schema": "info_geometry.tactic_path_ranking.v1",
                "split": "val",
                "context": {"theorem": "T.cli"},
                "graph_features": {"cone_depth": 0},
                "candidates": [
                    {"label": 1, "stall_type": "none"},
                    {"label": 0, "stall_type": "none"},
                ],
            }
        ],
    )

    subprocess.run(
        [sys.executable, str(SCRIPT), "--dataset", str(dataset), "--out", str(out)],
        cwd=REPO_ROOT,
        check=True,
    )

    parsed = json.loads(out.read_text(encoding="utf-8"))
    assert parsed["schema"] == "info_geometry.tactic_path_ranking.analysis.v1"
    assert parsed["totals"]["decision_points"] == 1
