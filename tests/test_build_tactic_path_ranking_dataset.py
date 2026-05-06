import json
import subprocess
import sys
from pathlib import Path

from tools.infra.build_tactic_path_ranking_dataset import run_builder


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "build_tactic_path_ranking_dataset.py"


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, ensure_ascii=True) + "\n" for row in rows), encoding="utf-8")


def test_tactic_path_ranking_groups_success_and_failure_candidates(tmp_path: Path) -> None:
    sft = tmp_path / "tactic_sft.jsonl"
    failures = tmp_path / "tactic_failures.jsonl"
    out = tmp_path / "ranking.jsonl"
    stats = tmp_path / "stats.json"
    goal = "x : Nat\nh : x = x\n⊢ x = x"
    goal_hash = "goal-1"
    _write_jsonl(
        sft,
        [
            {
                "schema": "info_geometry.tactic_sft.v1",
                "source": "leandojo_v2",
                "theorem": "Demo.same",
                "lean_file": "lean/Demo.lean",
                "theorem_statement": "theorem Demo.same (x : Nat) : x = x := by rfl",
                "goal_before": goal,
                "goal_hash": goal_hash,
                "tactic": "rfl",
                "goal_after": "no goals",
                "context": {"dependencies": ["Eq.refl"]},
                "raw_ref": {"source_file": "sft.jsonl", "source_line": 1},
            }
        ],
    )
    _write_jsonl(
        failures,
        [
            {
                "schema": "info_geometry.tactic_failure.v1",
                "source": "hive",
                "theorem": "Demo.same",
                "goal_before": goal,
                "goal_hash": goal_hash,
                "failed_tactic": "simp",
                "diagnostic": "unsolved goals",
                "failure_kind": "lean_verification_failure",
                "raw_ref": {"source_file": "failures.jsonl", "source_line": 1},
            }
        ],
    )

    summary = run_builder(sft_path=sft, failures_path=failures, out_path=out, stats_path=stats, min_candidates=2)

    rows = [json.loads(line) for line in out.read_text(encoding="utf-8").splitlines()]
    assert summary["rows"] == 1
    assert rows[0]["schema"] == "info_geometry.tactic_path_ranking.v1"
    assert rows[0]["context"]["theorem"] == "Demo.same"
    assert rows[0]["graph_features"]["goal_hash"] == goal_hash
    assert rows[0]["graph_features"]["candidate_count"] == 2
    assert rows[0]["graph_features"]["positive_count"] == 1
    assert rows[0]["graph_features"]["negative_count"] == 1
    assert rows[0]["graph_features"]["stall_count"] == 1
    assert rows[0]["graph_features"]["chiral_flow_direction"] == 0
    assert rows[0]["split"] in {"train", "val", "test"}
    assert rows[0]["provenance"]["authority_stages"] == ["lean_checked"]
    assert rows[0]["candidates"][0]["tactic"] == "rfl"
    assert rows[0]["candidates"][0]["label"] == 1
    assert rows[0]["candidates"][0]["is_positive"] == 1
    assert rows[0]["candidates"][0]["stall_type"] == "none"
    assert rows[0]["candidates"][0]["edge_id"]
    assert rows[0]["candidates"][0]["goal_hash_before"] == goal_hash
    assert rows[0]["candidates"][0]["goal_hash_after"]
    assert rows[0]["candidates"][0]["sampling_priority"] > 0
    assert rows[0]["candidates"][0]["balanced_operator_score"] > 0
    assert rows[0]["candidates"][0]["entropic_weights"]["diagnostic_prior_only"] is True
    assert rows[0]["failure_fossils"][0]["tactic"] == "simp"
    assert rows[0]["authority"]["lean_remains_proof_authority"] is True


def test_tactic_path_ranking_marks_stalls_as_negative_one(tmp_path: Path) -> None:
    sft = tmp_path / "empty_sft.jsonl"
    failures = tmp_path / "failures.jsonl"
    out = tmp_path / "ranking.jsonl"
    stats = tmp_path / "stats.json"
    sft.write_text("", encoding="utf-8")
    _write_jsonl(
        failures,
        [
            {
                "schema": "info_geometry.tactic_failure.v1",
                "source": "hive",
                "theorem": "Demo.loop",
                "goal_before": "⊢ True",
                "goal_hash": "goal-loop",
                "failed_tactic": "simp",
                "diagnostic": "repeated no progress loop",
                "failure_kind": "no_progress",
            },
            {
                "schema": "info_geometry.tactic_failure.v1",
                "source": "hive",
                "theorem": "Demo.loop",
                "goal_before": "⊢ True",
                "goal_hash": "goal-loop",
                "failed_tactic": "simp [foo]",
                "diagnostic": "repeated no progress loop",
                "failure_kind": "no_progress",
            },
        ],
    )

    run_builder(sft_path=sft, failures_path=failures, out_path=out, stats_path=stats, min_candidates=2)

    row = json.loads(out.read_text(encoding="utf-8").splitlines()[0])
    assert {candidate["label"] for candidate in row["candidates"]} == {0}
    assert {candidate["is_positive"] for candidate in row["candidates"]} == {0}
    assert {candidate["stall_type"] for candidate in row["candidates"]} == {"harmonic_stall"}
    assert row["graph_features"]["stall_count"] == 2
    assert row["graph_features"]["entropic_weights_are_diagnostic"] is True
    assert row["graph_features"]["chiral_flow_direction"] == -1
    assert row["graph_features"]["hodge_harmonic_signal"] > 0


def test_tactic_path_ranking_cli(tmp_path: Path) -> None:
    sft = tmp_path / "sft.jsonl"
    failures = tmp_path / "failures.jsonl"
    out = tmp_path / "ranking.jsonl"
    stats = tmp_path / "stats.json"
    _write_jsonl(
        sft,
        [
            {
                "schema": "info_geometry.tactic_sft.v1",
                "theorem": "Demo.cli",
                "goal_before": "⊢ True",
                "goal_hash": "goal-cli",
                "tactic": "trivial",
                "goal_after": "no goals",
                "context": {"dependencies": []},
            }
        ],
    )
    _write_jsonl(
        failures,
        [
            {
                "schema": "info_geometry.tactic_failure.v1",
                "theorem": "Demo.cli",
                "goal_before": "⊢ True",
                "goal_hash": "goal-cli",
                "failed_tactic": "exact False.elim ?h",
                "diagnostic": "unsolved goals",
                "failure_kind": "unsolved_goals",
            }
        ],
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--sft",
            str(sft),
            "--failures",
            str(failures),
            "--out",
            str(out),
            "--stats-out",
            str(stats),
        ],
        cwd=REPO_ROOT,
        check=True,
    )

    summary = json.loads(stats.read_text(encoding="utf-8"))
    assert summary["rows"] == 1
    assert summary["candidate_labels"] == {"0": 1, "1": 1}
    assert summary["sampling_priority"]["count"] == 2
