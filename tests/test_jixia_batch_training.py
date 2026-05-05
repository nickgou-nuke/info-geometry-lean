import json
import subprocess
import sys
from pathlib import Path

from tools.infra.jixia_batch_training import (
    concat_jsonl,
    discover_lean_files,
    lean_files_from_cone_packets,
    raw_paths_for,
    run_pipeline,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "jixia_batch_training.py"


def _write_raw_jixia_fixture(raw_dir: Path, lean_file: Path) -> None:
    paths = raw_paths_for(raw_dir, lean_file)
    paths["dir"].mkdir(parents=True)
    paths["declaration"].write_text("[]", encoding="utf-8")
    paths["symbol"].write_text("[]", encoding="utf-8")
    paths["line"].write_text("[]", encoding="utf-8")
    paths["elaboration"].write_text(
        json.dumps(
            [
                {
                    "info": {
                        "tactic": {
                            "references": [["True", "intro"]],
                            "before": [{"pp": "⊢ True", "type": "True"}],
                            "after": [],
                        }
                    },
                    "ref": {"range": [20, 27], "original": True, "pp?": "trivial"},
                    "children": [],
                }
            ]
        ),
        encoding="utf-8",
    )


def test_discover_lean_files_is_deduped_and_sorted_by_prefix(tmp_path: Path) -> None:
    root = tmp_path / "lean"
    root.mkdir()
    a = root / "A.lean"
    b = root / "B.lean"
    a.write_text("", encoding="utf-8")
    b.write_text("", encoding="utf-8")

    files = discover_lean_files([a], [root])

    assert files == [a, b]


def test_lean_files_from_cone_packet_collects_source_excerpts(tmp_path: Path) -> None:
    lean_file = tmp_path / "lean" / "Demo.lean"
    lean_file.parent.mkdir()
    lean_file.write_text("theorem demo : True := by trivial\n", encoding="utf-8")
    packet = tmp_path / "cone.json"
    packet.write_text(
        json.dumps(
            {
                "schema": "info_geometry.causal_chiral_cone_prompt.v1",
                "apex": {"node": {"file": str(lean_file)}},
                "source_excerpts": [
                    {
                        "name": "Demo.demo",
                        "file": str(lean_file),
                        "source_excerpt": {"path": str(lean_file), "lines": []},
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    assert lean_files_from_cone_packets([packet]) == [lean_file]


def test_concat_jsonl_skips_missing_inputs(tmp_path: Path) -> None:
    a = tmp_path / "a.jsonl"
    out = tmp_path / "out.jsonl"
    a.write_text('{"x":1}\n\n{"x":2}', encoding="utf-8")

    count = concat_jsonl([a, tmp_path / "missing.jsonl"], out)

    assert count == 2
    assert len(out.read_text(encoding="utf-8").splitlines()) == 2


def test_run_pipeline_skip_jixia_builds_training_from_existing_raw(tmp_path: Path) -> None:
    lean_file = tmp_path / "lean" / "Demo.lean"
    lean_file.parent.mkdir()
    lean_file.write_text("theorem demo : True := by\n  trivial\n", encoding="utf-8")
    raw_dir = tmp_path / "raw"
    normalized_dir = tmp_path / "normalized"
    combined_dir = tmp_path / "combined"
    dataset_dir = tmp_path / "dataset"
    summary_out = tmp_path / "summary.json"
    _write_raw_jixia_fixture(raw_dir, lean_file)

    args = type(
        "Args",
        (),
        {
            "file": [lean_file],
            "prefix": [],
            "cone_packet": [],
            "max_files": None,
            "jixia_bin": Path("missing-jixia"),
            "raw_dir": raw_dir,
            "normalized_dir": normalized_dir,
            "combined_dir": combined_dir,
            "dataset_dir": dataset_dir,
            "summary_out": summary_out,
            "skip_jixia": True,
            "initializer": True,
            "jixia_arg": [],
            "keep_going": False,
            "build_training": True,
        },
    )()

    summary = run_pipeline(args)

    assert summary["combined_tactic_rows"] == 1
    assert (combined_dir / "jixia_tactic_transitions.jsonl").exists()
    sft = [json.loads(line) for line in (dataset_dir / "tactic_sft.jsonl").read_text(encoding="utf-8").splitlines()]
    assert sft[0]["source"] == "jixia"
    assert sft[0]["tactic"] == "trivial"


def test_run_pipeline_skip_jixia_accepts_cone_packet(tmp_path: Path) -> None:
    lean_file = tmp_path / "lean" / "Demo.lean"
    lean_file.parent.mkdir()
    lean_file.write_text("theorem demo : True := by\n  trivial\n", encoding="utf-8")
    raw_dir = tmp_path / "raw"
    normalized_dir = tmp_path / "normalized"
    combined_dir = tmp_path / "combined"
    dataset_dir = tmp_path / "dataset"
    summary_out = tmp_path / "summary.json"
    cone_packet = tmp_path / "cone.json"
    cone_packet.write_text(json.dumps({"source_excerpts": [{"file": str(lean_file)}]}), encoding="utf-8")
    _write_raw_jixia_fixture(raw_dir, lean_file)

    args = type(
        "Args",
        (),
        {
            "file": [],
            "prefix": [],
            "cone_packet": [cone_packet],
            "max_files": None,
            "jixia_bin": Path("missing-jixia"),
            "raw_dir": raw_dir,
            "normalized_dir": normalized_dir,
            "combined_dir": combined_dir,
            "dataset_dir": dataset_dir,
            "summary_out": summary_out,
            "skip_jixia": True,
            "initializer": True,
            "jixia_arg": [],
            "keep_going": False,
            "build_training": True,
        },
    )()

    summary = run_pipeline(args)

    assert summary["lean_files"] == [str(lean_file)]
    assert summary["cone_packets"] == [str(cone_packet)]
    assert summary["combined_tactic_rows"] == 1


def test_jixia_batch_training_cli_skip_jixia(tmp_path: Path) -> None:
    lean_file = tmp_path / "lean" / "Demo.lean"
    lean_file.parent.mkdir()
    lean_file.write_text("theorem demo : True := by\n  trivial\n", encoding="utf-8")
    raw_dir = tmp_path / "raw"
    out = tmp_path / "out"
    _write_raw_jixia_fixture(raw_dir, lean_file)
    out.mkdir()
    cone_packet = out / "cone.json"
    cone_packet.write_text(json.dumps({"source_excerpts": [{"file": str(lean_file)}]}), encoding="utf-8")

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--cone-packet",
            str(cone_packet),
            "--raw-dir",
            str(raw_dir),
            "--normalized-dir",
            str(out / "normalized"),
            "--combined-dir",
            str(out / "combined"),
            "--dataset-dir",
            str(out / "dataset"),
            "--summary-out",
            str(out / "summary.json"),
            "--skip-jixia",
            "--build-training",
        ],
        cwd=REPO_ROOT,
        check=True,
    )

    summary = json.loads((out / "summary.json").read_text(encoding="utf-8"))
    assert summary["combined_tactic_rows"] == 1
    assert (out / "dataset" / "tactic_sft.jsonl").exists()
