import argparse
import json
import subprocess
import sys
from pathlib import Path

from tools.infra.build_tactic_training_dataset import build_dataset
from tools.infra.ulam_trace_bridge import normalize_record, run_bridge


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "ulam_trace_bridge.py"


def _ulam_success() -> dict:
    return {
        "theorem": "Demo.true_intro",
        "state_key": "s0",
        "state_pretty": "⊢ True",
        "tactic": "trivial",
        "ok": True,
        "solved": True,
    }


def _ulam_failure() -> dict:
    return {
        "theorem": "Demo.true_intro",
        "state_key": "s0",
        "state_pretty": "⊢ True",
        "tactic": "exact False.elim ?h",
        "ok": False,
        "error": "unsolved goals",
        "error_kind": "unsolved_goals",
    }


def test_normalize_ulam_record_preserves_transition(tmp_path: Path) -> None:
    src = tmp_path / "run.jsonl"
    row = normalize_record(_ulam_success(), src, 1)

    assert row["schema"] == "info_geometry.ulam_trace.v1"
    assert row["source"] == "ulamai"
    assert row["theorem"] == "Demo.true_intro"
    assert row["goal_before"] == "⊢ True"
    assert row["tactic"] == "trivial"
    assert row["ok"] is True
    assert row["solved"] is True
    assert row["authority"]["lean_remains_proof_authority"] is True


def test_run_bridge_writes_summary(tmp_path: Path) -> None:
    src = tmp_path / "run.jsonl"
    out = tmp_path / "out"
    src.write_text(json.dumps(_ulam_success()) + "\n" + json.dumps(_ulam_failure()) + "\n", encoding="utf-8")

    summary = run_bridge(src, out)

    assert summary["records"] == 2
    assert summary["successful_steps"] == 1
    assert summary["failed_steps"] == 1
    assert summary["solved_steps"] == 1
    assert (out / "ulam_trace_bridge.jsonl").exists()


def test_ulam_trace_bridge_feeds_tactic_dataset(tmp_path: Path) -> None:
    src = tmp_path / "run.jsonl"
    bridge_out = tmp_path / "bridge"
    src.write_text(json.dumps(_ulam_success()) + "\n" + json.dumps(_ulam_failure()) + "\n", encoding="utf-8")
    run_bridge(src, bridge_out)

    args = argparse.Namespace(
        leandojo_bridge=None,
        leantrail_failures=None,
        hive_attempts=None,
        raw_infotree=None,
        real_prover_traces=None,
        jixia_tactics=None,
        ulam_traces=bridge_out / "ulam_trace_bridge.jsonl",
        out_sft=tmp_path / "sft.jsonl",
        out_dpo=tmp_path / "dpo.jsonl",
        out_failures=tmp_path / "failures.jsonl",
        stats_out=tmp_path / "stats.json",
        seed=1729,
        train_ratio=0.85,
        val_ratio=0.075,
    )

    stats = build_dataset(args)

    assert stats["rows"]["sft"] == 1
    assert stats["rows"]["failures"] == 1
    assert stats["rows"]["dpo"] == 1
    assert stats["by_source"] == {"ulamai": 2}


def test_ulam_trace_bridge_cli(tmp_path: Path) -> None:
    src = tmp_path / "run.jsonl"
    out = tmp_path / "out"
    src.write_text(json.dumps(_ulam_success()) + "\n", encoding="utf-8")

    subprocess.run(
        [sys.executable, str(SCRIPT), "--input", str(src), "--output-dir", str(out)],
        cwd=REPO_ROOT,
        check=True,
    )

    summary = json.loads((out / "ulam_trace_bridge_summary.json").read_text(encoding="utf-8"))
    assert summary["records"] == 1
