import json
import subprocess
import sys
from pathlib import Path

from tools.infra.pda_forml4_bridge import normalize_record, run_bridge


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "pda_forml4_bridge.py"


def test_normalize_forml4_record_with_process_label(tmp_path: Path) -> None:
    src = tmp_path / "train.json"
    raw = {
        "name": "Demo.true_intro",
        "informal_statement": "True is true.",
        "formal_statement": "theorem Demo.true_intro : True := by trivial",
        "compiler_feedback": "type mismatch at application",
    }

    row = normalize_record(raw, src, 1)

    assert row["schema"] == "info_geometry.pda_forml4_bridge.v1"
    assert row["source"] == "pda_forml4"
    assert row["theorem"] == "Demo.true_intro"
    assert row["informal_statement"] == "True is true."
    assert row["formal_statement"].startswith("theorem Demo.true_intro")
    assert row["process_label"] == "type_error"
    assert row["split"] == "train"
    assert row["authority"]["lean_remains_proof_authority"] is True


def test_run_bridge_writes_jsonl_and_summary(tmp_path: Path) -> None:
    src_dir = tmp_path / "forml4"
    out_dir = tmp_path / "out"
    src_dir.mkdir()
    (src_dir / "basic_test.json").write_text(
        json.dumps(
            [
                {
                    "declName": "Demo.ok",
                    "informal": "A simple theorem.",
                    "formal": "theorem Demo.ok : True := by trivial",
                    "status": "success",
                }
            ]
        ),
        encoding="utf-8",
    )

    summary = run_bridge(src_dir, out_dir)

    rows = (out_dir / "pda_forml4_bridge.jsonl").read_text(encoding="utf-8").splitlines()
    assert len(rows) == 1
    assert summary["records"] == 1
    assert summary["with_informal_statement"] == 1
    assert summary["with_formal_statement"] == 1
    assert summary["process_labels"] == {"valid": 1}
    assert summary["splits"] == {"test": 1}
    assert (out_dir / "pda_forml4_bridge_summary.json").exists()


def test_pda_forml4_bridge_cli(tmp_path: Path) -> None:
    src = tmp_path / "input.jsonl"
    out = tmp_path / "out"
    src.write_text(
        json.dumps({"question": "True?", "answer": "theorem demo : True := by trivial"}) + "\n",
        encoding="utf-8",
    )

    subprocess.run(
        [sys.executable, str(SCRIPT), "--input", str(src), "--output-dir", str(out)],
        cwd=REPO_ROOT,
        check=True,
    )

    summary = json.loads((out / "pda_forml4_bridge_summary.json").read_text(encoding="utf-8"))
    assert summary["records"] == 1
