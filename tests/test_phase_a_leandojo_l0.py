import json
from pathlib import Path

from tools.infra.leandojo_v2_bridge import run_bridge


def test_phase_a_bridge_accepts_leandojo_v2_style_json(tmp_path: Path) -> None:
    input_dir = tmp_path / "leandojo_json"
    output_dir = tmp_path / "bridge_out"
    input_dir.mkdir()

    data = [
        {
            "url": "https://github.com/lean-dojo/LeanDojo-v2",
            "commit": "936ea0d",
            "file_path": "lean/InfoGeometry/Basic.lean",
            "full_name": "InfoGeometry.dummy_theorem",
            "theorem_statement": "theorem InfoGeometry.dummy_theorem : True := by trivial",
            "start": [5, 1],
            "end": [5, 42],
            "traced_tactics": [
                {"tactic": "trivial", "state_before": "⊢ True", "state_after": "no goals"}
            ],
        }
    ]

    (input_dir / "train.json").write_text(json.dumps(data), encoding="utf-8")

    summary = run_bridge(input_dir=input_dir, output_dir=output_dir)

    assert summary["rows"] == 1
    assert summary["files"] == 1

    out_jsonl = output_dir / "leandojo_v2_bridge.jsonl"
    assert out_jsonl.exists()
    row = json.loads(out_jsonl.read_text(encoding="utf-8").strip())

    assert row["source"] == "leandojo_v2"
    assert row["theoremFullName"] == "InfoGeometry.dummy_theorem"
    assert row["proofStepCount"] == 1
    assert row["positions"]["start"] == {"line": 5, "column": 1}


def test_l0_level_contract_files_exist_and_labels_present() -> None:
    repo_root = Path(__file__).resolve().parents[1]

    architecture = repo_root / "lean/InfoGeometry/Meta/Architecture.lean"
    basic = repo_root / "lean/InfoGeometry/Basic.lean"
    info_basic = repo_root / "lean/InfoGeometry/Information/Basic.lean"

    assert architecture.exists(), "Architecture layer contract file missing"
    assert basic.exists(), "InfoGeometry.Basic missing"
    assert info_basic.exists(), "InfoGeometry.Information.Basic missing"

    text = architecture.read_text(encoding="utf-8")
    assert '"L0_Count"' in text
    assert '"L1_Projective"' in text
    assert 'def RepDepth.toNat' in text
