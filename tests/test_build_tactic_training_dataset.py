import argparse
import json
from pathlib import Path

from tools.infra.build_tactic_training_dataset import build_dataset, goal_hash, normalize_goal


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def _args(
    tmp_path: Path,
    *,
    leandojo: Path,
    leantrail: Path,
    hive: Path | None = None,
    real: Path | None = None,
) -> argparse.Namespace:
    return argparse.Namespace(
        leandojo_bridge=leandojo,
        leantrail_failures=leantrail,
        hive_attempts=hive,
        real_prover_traces=real,
        raw_infotree=None,
        out_sft=tmp_path / "tactic_sft.jsonl",
        out_dpo=tmp_path / "tactic_dpo.jsonl",
        out_failures=tmp_path / "tactic_failures.jsonl",
        stats_out=tmp_path / "stats.json",
        seed=1,
        train_ratio=0.8,
        val_ratio=0.1,
    )


def test_normalize_goal_hash_is_whitespace_stable() -> None:
    assert normalize_goal("x : Nat\n⊢   x = x") == "x : Nat ⊢ x = x"
    assert goal_hash("x : Nat\n⊢   x = x") == goal_hash("x : Nat ⊢ x = x")


def test_build_tactic_training_dataset_emits_sft_and_failures(tmp_path: Path) -> None:
    leandojo = tmp_path / "leandojo_v2_bridge.jsonl"
    leantrail = tmp_path / "failed_transitions.jsonl"
    _write_jsonl(
        leandojo,
        [
            {
                "source": "leandojo_v2",
                "sourceFile": "trace.jsonl",
                "sourceLine": 1,
                "theoremFullName": "Demo.good",
                "leanFile": "lean/Demo.lean",
                "theoremStatement": "theorem Demo.good : True := by trivial",
                "dependencies": ["True.intro"],
                "tactics": [
                    {"tactic": "trivial", "stateBefore": "⊢ True", "stateAfter": "no goals"},
                ],
            }
        ],
    )
    _write_jsonl(
        leantrail,
        [
            {
                "id": "ft1",
                "src": "Demo.bad",
                "dst": "Demo.dep",
                "kind": "depends_value",
                "error_kind": "type_mismatch",
            }
        ],
    )

    stats = build_dataset(_args(tmp_path, leandojo=leandojo, leantrail=leantrail))

    sft = [json.loads(line) for line in (tmp_path / "tactic_sft.jsonl").read_text().splitlines()]
    failures = [json.loads(line) for line in (tmp_path / "tactic_failures.jsonl").read_text().splitlines()]
    dpo = (tmp_path / "tactic_dpo.jsonl").read_text().splitlines()

    assert stats["rows"] == {"sft": 1, "dpo": 0, "failures": 1}
    assert sft[0]["schema"] == "info_geometry.tactic_sft.v1"
    assert sft[0]["source"] == "leandojo_v2"
    assert sft[0]["theorem"] == "Demo.good"
    assert sft[0]["tactic"] == "trivial"
    assert sft[0]["context"]["dependencies"] == ["True.intro"]
    assert sft[0]["aesop_tactic_prior"]["phase"] == "safe"
    assert failures[0]["schema"] == "info_geometry.tactic_failure.v1"
    assert failures[0]["source"] == "leantrail"
    assert failures[0]["failure_kind"] == "type_mismatch"
    assert dpo == []


def test_build_tactic_training_dataset_pairs_dpo_by_same_theorem_and_goal_hash(tmp_path: Path) -> None:
    leandojo = tmp_path / "leandojo_v2_bridge.jsonl"
    leantrail = tmp_path / "missing_failed_transitions.jsonl"
    hive_dir = tmp_path / "hive"
    goal = "x : Nat\n⊢ x = x"
    _write_jsonl(
        leandojo,
        [
            {
                "source": "leandojo_v2",
                "sourceFile": "trace.jsonl",
                "sourceLine": 1,
                "theoremFullName": "Demo.same",
                "leanFile": "lean/Demo.lean",
                "theoremStatement": "theorem Demo.same : True := by trivial",
                "dependencies": [],
                "tactics": [
                    {"tactic": "rfl", "stateBefore": goal, "stateAfter": "no goals"},
                ],
            }
        ],
    )
    hive_dir.mkdir()
    (hive_dir / "deadend.json").write_text(
        json.dumps(
            {
                "_key": "dead1",
                "schema": "info_geometry.hive_deadend.v1",
                "const_name": "Demo.same",
                "local_context_slice": goal,
                "attempted_tactic": "simp",
                "verification_output": "unsolved goals",
                "failure_kind": "lean_verification_failure",
            }
        ),
        encoding="utf-8",
    )

    stats = build_dataset(_args(tmp_path, leandojo=leandojo, leantrail=leantrail, hive=hive_dir))

    dpo = [json.loads(line) for line in (tmp_path / "tactic_dpo.jsonl").read_text().splitlines()]
    assert stats["rows"]["dpo"] == 1
    assert stats["dpo_pairing"]["same_goal_hash_pairs"] == 1
    assert dpo[0]["schema"] == "info_geometry.tactic_dpo.v1"
    assert dpo[0]["theorem"] == "Demo.same"
    assert dpo[0]["chosen"]["tactic"] == "rfl"
    assert dpo[0]["chosen"]["aesop_tactic_prior"]["phase"] == "safe"
    assert dpo[0]["rejected"]["tactic"] == "simp"
    assert dpo[0]["rejected"]["aesop_tactic_prior"]["phase"] == "normalization"
    assert dpo[0]["pairing_reason"] == "same_theorem_and_goal_hash"


def test_build_tactic_training_dataset_ingests_real_prover_traces(tmp_path: Path) -> None:
    leandojo = tmp_path / "missing_leandojo.jsonl"
    leantrail = tmp_path / "missing_failed_transitions.jsonl"
    real = tmp_path / "real_prover_trace_bridge.jsonl"
    _write_jsonl(
        real,
        [
            {
                "schema": "info_geometry.real_prover_trace.v1",
                "id": "real1",
                "formal_statement": "theorem Demo.real : True := by sorry",
                "success": True,
                "collect_results": [
                    {
                        "declaration": "Demo.real",
                        "success": True,
                        "nodes": [
                            {"id": 0, "parent": 0, "depth": 0, "tactic": "", "state": ["⊢ True"]},
                            {"id": 1, "parent": 0, "depth": 1, "tactic": "trivial", "state": []},
                        ],
                        "calls": [],
                    }
                ],
                "raw_ref": {"source_file": "real.json", "source_line": 1},
            }
        ],
    )

    stats = build_dataset(_args(tmp_path, leandojo=leandojo, leantrail=leantrail, real=real))

    sft = [json.loads(line) for line in (tmp_path / "tactic_sft.jsonl").read_text().splitlines()]
    assert stats["rows"]["sft"] == 1
    assert stats["by_source"]["real_prover"] == 1
    assert sft[0]["source"] == "real_prover"
    assert sft[0]["theorem"] == "Demo.real"
    assert sft[0]["goal_before"] == "⊢ True"
    assert sft[0]["tactic"] == "trivial"
    assert sft[0]["goal_after"] == "no goals"
