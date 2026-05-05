import json
import subprocess
from pathlib import Path

from tools.infra.leandojo_v2_bridge import _pos, convert_theorem_record, run_bridge


# -------------------------
# Unit tests: low-level API
# -------------------------

def test_pos_valid_and_invalid_shapes() -> None:
    assert _pos([3, 7]) == {"line": 3, "column": 7}
    assert _pos([3]) is None
    assert _pos([3, "x"]) is None
    assert _pos("3,7") is None


def test_convert_theorem_record_handles_missing_tactics() -> None:
    out = convert_theorem_record(
        {
            "url": "https://github.com/example/repo",
            "commit": "abc",
            "file_path": "lean/Foo.lean",
            "full_name": "Foo.no_tactics",
            "theorem_statement": None,
            "start": [1, 1],
            "end": [1, 10],
        },
        source_file="val.json",
        line_no=9,
    )

    assert out["theoremFullName"] == "Foo.no_tactics"
    assert out["proofStepCount"] == 0
    assert out["firstGoalState"] is None
    assert out["lastGoalState"] is None
    assert out["tactics"] == []


def test_convert_theorem_record_normalizes_tactics() -> None:
    out = convert_theorem_record(
        {
            "url": "https://github.com/example/repo",
            "commit": "abc",
            "file_path": "lean/Foo.lean",
            "full_name": "Foo.tactics",
            "theorem_statement": "theorem Foo.tactics : True := by trivial",
            "start": [10, 2],
            "end": [12, 5],
            "traced_tactics": [
                {"tactic": "intro h", "state_before": "⊢ True", "state_after": "h : True ⊢ True"},
                {"tactic": "exact h", "state_before": "h : True ⊢ True", "state_after": "no goals"},
            ],
        },
        source_file="train.json",
        line_no=2,
    )

    assert out["proofStepCount"] == 2
    assert out["firstGoalState"] == "⊢ True"
    assert out["lastGoalState"] == "no goals"
    assert out["positions"]["start"] == {"line": 10, "column": 2}
    assert out["positions"]["end"] == {"line": 12, "column": 5}
    assert out["tactics"][0]["stateBefore"] == "⊢ True"
    assert out["tactics"][1]["stateAfter"] == "no goals"


# --------------------------------
# Integration tests: file pipeline
# --------------------------------

def test_run_bridge_multiple_files_and_rows(tmp_path: Path) -> None:
    input_dir = tmp_path / "in"
    output_dir = tmp_path / "out"
    input_dir.mkdir()

    (input_dir / "train.json").write_text(
        json.dumps(
            [
                {
                    "url": "https://github.com/a/repo",
                    "commit": "c1",
                    "file_path": "lean/A.lean",
                    "full_name": "A.t1",
                    "theorem_statement": "theorem A.t1 : True := by trivial",
                    "start": [1, 1],
                    "end": [1, 20],
                    "traced_tactics": [{"tactic": "trivial", "state_before": "⊢ True", "state_after": "no goals"}],
                },
                {
                    "url": "https://github.com/a/repo",
                    "commit": "c1",
                    "file_path": "lean/A.lean",
                    "full_name": "A.t2",
                    "theorem_statement": "theorem A.t2 : True := by trivial",
                    "start": [2, 1],
                    "end": [2, 20],
                    "traced_tactics": [],
                },
            ]
        ),
        encoding="utf-8",
    )

    (input_dir / "test.json").write_text(
        json.dumps(
            [
                {
                    "url": "https://github.com/b/repo",
                    "commit": "c2",
                    "file_path": "lean/B.lean",
                    "full_name": "B.t1",
                    "theorem_statement": "theorem B.t1 : True := by trivial",
                    "start": [3, 1],
                    "end": [3, 20],
                    "traced_tactics": [{"tactic": "trivial", "state_before": "⊢ True", "state_after": "no goals"}],
                }
            ]
        ),
        encoding="utf-8",
    )

    summary = run_bridge(input_dir=input_dir, output_dir=output_dir)

    assert summary["files"] == 2
    assert summary["rows"] == 3

    jsonl_path = output_dir / "leandojo_v2_bridge.jsonl"
    lines = [json.loads(line) for line in jsonl_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    assert len(lines) == 3
    assert {row["theoremFullName"] for row in lines} == {"A.t1", "A.t2", "B.t1"}

    summary_path = output_dir / "leandojo_v2_bridge_summary.json"
    summary_payload = json.loads(summary_path.read_text(encoding="utf-8"))
    assert summary_payload["rows"] == 3


def test_run_bridge_ignores_non_json_files(tmp_path: Path) -> None:
    input_dir = tmp_path / "in"
    output_dir = tmp_path / "out"
    input_dir.mkdir()

    (input_dir / "README.txt").write_text("not json", encoding="utf-8")
    summary = run_bridge(input_dir=input_dir, output_dir=output_dir)

    assert summary["files"] == 0
    assert summary["rows"] == 0
    assert (output_dir / "leandojo_v2_bridge.jsonl").exists()


# ----------------------
# CLI + contract testing
# ----------------------

def test_bridge_cli_end_to_end(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    script = repo_root / "tools/infra/leandojo_v2_bridge.py"

    input_dir = tmp_path / "in"
    output_dir = tmp_path / "out"
    input_dir.mkdir()

    (input_dir / "train.json").write_text(
        json.dumps(
            [
                {
                    "url": "https://github.com/example/repo",
                    "commit": "abc",
                    "file_path": "lean/Foo.lean",
                    "full_name": "Foo.cli",
                    "theorem_statement": "theorem Foo.cli : True := by trivial",
                    "start": [1, 1],
                    "end": [1, 10],
                    "traced_tactics": [{"tactic": "trivial", "state_before": "⊢ True", "state_after": "no goals"}],
                }
            ]
        ),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            "python3",
            str(script),
            "--input-dir",
            str(input_dir),
            "--output-dir",
            str(output_dir),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    stdout_payload = json.loads(proc.stdout)
    assert stdout_payload["rows"] == 1
    assert (output_dir / "leandojo_v2_bridge.jsonl").exists()


def test_l0_architecture_contract_surface() -> None:
    repo_root = Path(__file__).resolve().parents[1]
    architecture = repo_root / "lean/InfoGeometry/Meta/Architecture.lean"
    basic = repo_root / "lean/InfoGeometry/Basic.lean"
    info_basic = repo_root / "lean/InfoGeometry/Information/Basic.lean"

    assert architecture.exists()
    assert basic.exists()
    assert info_basic.exists()

    text = architecture.read_text(encoding="utf-8")

    # Canonical layer labels (L0-L5)
    assert '"L0_Count"' in text
    assert '"L1_Projective"' in text
    assert '"L2_Operator"' in text
    assert '"L3_Krein"' in text
    assert '"L4_ModularTransport"' in text
    assert '"L5_ThermodynamicClosure"' in text

    # Numeric mapping contract for depth indices
    assert "| .count => 0" in text
    assert "| .projective => 1" in text
    assert "| .operator => 2" in text
    assert "| .krein => 3" in text
    assert "| .transport => 4" in text
    assert "| .thermo => 5" in text


def test_l0_modules_compile_gate() -> None:
    repo_root = Path(__file__).resolve().parents[1]

    # Keep this narrow and deterministic: compile only the L0-adjacent module surface.
    files = [
        "lean/InfoGeometry/Meta/Architecture.lean",
        "lean/InfoGeometry/Basic.lean",
        "lean/InfoGeometry/Information/Basic.lean",
    ]

    for fpath in files:
        cmd = ["lake", "env", "lean", fpath]
        proc = subprocess.run(cmd, cwd=repo_root, capture_output=True, text=True)
        assert proc.returncode == 0, (
            f"L0 compile gate failed for {fpath}.\n"
            f"STDOUT:\n{proc.stdout}\n\nSTDERR:\n{proc.stderr}"
        )
