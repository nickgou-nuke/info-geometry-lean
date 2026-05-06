import json
import subprocess
import sys
from pathlib import Path

from tools.infra.run_predigestion_to_hive_demo import run_demo


REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "tools" / "infra" / "run_predigestion_to_hive_demo.py"


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("\n".join(json.dumps(row) for row in rows) + "\n", encoding="utf-8")


def test_run_demo_writes_claims_tasks_and_summary(tmp_path: Path) -> None:
    chunks = tmp_path / "chunks.jsonl"
    out = tmp_path / "demo"
    write_jsonl(
        chunks,
        [
            {"id": "c1", "text": "Claim one. Extra.", "source": "paper-a"},
            {"id": "c2", "text": "Claim two.", "source": "paper-a", "risk": "formalizable"},
        ],
    )

    summary = run_demo(
        input_path=chunks,
        source_kind="paper",
        task_kind="formalize_claim",
        output_dir=out,
        sample_limit=1,
    )

    assert summary["schema"] == "info_geometry.predigestion_to_hive_demo.v1"
    assert summary["counts"] == {"claims": 2, "tasks": 2, "sample_tasks": 1}
    assert summary["by_risk"] == {"informal": 1, "formalizable": 1}
    assert Path(summary["artifacts"]["claims"]).exists()
    assert Path(summary["artifacts"]["tasks"]).exists()
    sample = json.loads((out / "sample_hive_queue_packets.json").read_text(encoding="utf-8"))
    assert sample["tasks"][0]["authority"] == "proposal"
    assert sample["tasks"][0]["authority_boundary"]["only_lean_checked_artifacts_can_assert"] is True


def test_cli_run_demo(tmp_path: Path) -> None:
    chunks = tmp_path / "chunks.jsonl"
    out = tmp_path / "demo"
    write_jsonl(chunks, [{"id": "c1", "text": "A Black Book image suggests a split carrier."}])

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(chunks),
            "--source-kind",
            "blackbook",
            "--task-kind",
            "map_claim_to_owner_surface",
            "--output-dir",
            str(out),
            "--sample-limit",
            "2",
        ],
        cwd=REPO,
        check=False,
    )

    assert proc.returncode == 0
    summary = json.loads((out / "predigestion_to_hive_demo_summary.json").read_text(encoding="utf-8"))
    assert summary["by_risk"] == {"metaphor": 1}
    assert summary["by_task_kind"] == {"map_claim_to_owner_surface": 1}
