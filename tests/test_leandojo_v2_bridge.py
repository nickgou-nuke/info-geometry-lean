import json
from pathlib import Path

from tools.infra.leandojo_v2_bridge import convert_theorem_record, run_bridge


def write_json_payload(path: Path, rows: list[dict]) -> None:
    path.write_text(json.dumps(rows, ensure_ascii=True), encoding="utf-8")


def test_convert_theorem_record_to_bridge_row() -> None:
    row = {
        "url": "https://github.com/example/repo",
        "commit": "abc123",
        "file_path": "lean/Foo.lean",
        "full_name": "Foo.bar",
        "theorem_statement": "theorem Foo.bar : True := by trivial",
        "start": [10, 2],
        "end": [12, 5],
        "traced_tactics": [
            {"tactic": "intro h", "state_before": "⊢ True", "state_after": "h : True ⊢ True"},
            {"tactic": "exact h", "state_before": "h : True ⊢ True", "state_after": "no goals"},
        ],
    }

    out = convert_theorem_record(row, source_file="random/train.json", line_no=3)

    assert out["bridgeVersion"] == "0.1.0"
    assert out["source"] == "leandojo_v2"
    assert out["theoremFullName"] == "Foo.bar"
    assert out["proofStepCount"] == 2
    assert out["firstGoalState"] == "⊢ True"
    assert out["lastGoalState"] == "no goals"
    assert out["positions"]["start"] == {"line": 10, "column": 2}


def test_run_bridge_converts_json_to_jsonl(tmp_path: Path) -> None:
    in_dir = tmp_path / "input"
    out_dir = tmp_path / "output"
    in_dir.mkdir()

    write_json_payload(
        in_dir / "train.json",
        [
            {
                "url": "https://github.com/example/repo",
                "commit": "abc123",
                "file_path": "lean/Foo.lean",
                "full_name": "Foo.bar",
                "theorem_statement": "theorem Foo.bar : True := by trivial",
                "start": [10, 2],
                "end": [12, 5],
                "traced_tactics": [{"tactic": "trivial", "state_before": "⊢ True", "state_after": "no goals"}],
            }
        ],
    )

    summary = run_bridge(input_dir=in_dir, output_dir=out_dir)

    out_file = out_dir / "leandojo_v2_bridge.jsonl"
    assert summary["rows"] == 1
    assert out_file.exists()

    lines = out_file.read_text(encoding="utf-8").strip().splitlines()
    assert len(lines) == 1
    payload = json.loads(lines[0])
    assert payload["theoremFullName"] == "Foo.bar"
    assert payload["proofStepCount"] == 1
