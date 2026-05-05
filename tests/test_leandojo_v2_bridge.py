import json
from pathlib import Path

from tools.infra.leandojo_v2_bridge import convert_theorem_record, load_decl_names, run_bridge


def write_json_payload(path: Path, rows: list[dict]) -> None:
    path.write_text(json.dumps(rows, ensure_ascii=True), encoding="utf-8")


def write_jsonl_payload(path: Path, rows: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=True) + "\n" for row in rows),
        encoding="utf-8",
    )


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
    assert out["declaration"] == "Foo.bar"
    assert out["proofStepCount"] == 2
    assert out["firstGoalState"] == "⊢ True"
    assert out["lastGoalState"] == "no goals"
    assert out["positions"]["start"] == {"line": 10, "column": 2}
    assert out["raw"] == row


def test_convert_theorem_record_accepts_schema_aliases() -> None:
    row = {
        "name": "Alias.demo",
        "file": "lean/Alias.lean",
        "type": "Alias.demo : True",
        "deps": ["True.intro"],
        "tactics": [
            {"text": "trivial", "before": "⊢ True", "after": "no goals"},
        ],
    }

    out = convert_theorem_record(row, source_file="alias.jsonl", line_no=1)

    assert out["theoremFullName"] == "Alias.demo"
    assert out["leanFile"] == "lean/Alias.lean"
    assert out["theoremStatement"] == "Alias.demo : True"
    assert out["dependencies"] == ["True.intro"]
    assert out["proofStepCount"] == 1
    assert out["firstGoalState"] == "⊢ True"
    assert out["lastGoalState"] == "no goals"
    assert out["tactics"][0]["tactic"] == "trivial"


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


def test_run_bridge_converts_jsonl_and_writes_coverage_report(tmp_path: Path) -> None:
    in_dir = tmp_path / "input"
    out_dir = tmp_path / "output"
    compare = tmp_path / "decls.jsonl"
    in_dir.mkdir()

    write_jsonl_payload(
        in_dir / "trace.jsonl",
        [
            {
                "name": "Foo.shared",
                "file": "lean/Foo.lean",
                "statement": "theorem Foo.shared : True := by trivial",
                "tactics": [{"text": "trivial", "before": "⊢ True", "after": "no goals"}],
            },
            {
                "name": "Foo.only_leandojo",
                "file": "lean/Foo.lean",
                "statement": "theorem Foo.only_leandojo : True := by trivial",
            },
        ],
    )
    write_jsonl_payload(
        compare,
        [
            {"name": "Foo.shared", "kind": "theorem"},
            {"name": "Foo.only_compare", "kind": "theorem"},
        ],
    )

    summary = run_bridge(input_dir=in_dir, output_dir=out_dir, compare_decl_paths=[compare])

    report_path = out_dir / "leandojo_v2_coverage_report.json"
    report = json.loads(report_path.read_text(encoding="utf-8"))

    assert summary["rows"] == 2
    assert summary["declarations"] == 2
    assert summary["rowsWithTactics"] == 1
    assert summary["rowsWithProofStates"] == 1
    assert summary["coverageReport"] == str(report_path)
    assert report["sharedDeclarationCount"] == 1
    assert report["onlyLeanDojoCount"] == 1
    assert report["onlyCompareCount"] == 1
    assert report["sharedSample"] == ["Foo.shared"]
    assert report["onlyLeanDojoSample"] == ["Foo.only_leandojo"]
    assert report["onlyCompareSample"] == ["Foo.only_compare"]


def test_load_decl_names_accepts_decl_name_lists_and_hydrated_components(tmp_path: Path) -> None:
    decl_names = tmp_path / "compiled_decl_names.json"
    hydrated = tmp_path / "structural-topology.json"
    decl_names.write_text(json.dumps({"decl_names": ["A.foo", "A.bar"]}), encoding="utf-8")
    hydrated.write_text(
        json.dumps(
            {
                "components": [
                    {
                        "componentId": "C0",
                        "representative": "B.rep",
                        "members": ["B.member"],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )

    assert load_decl_names(decl_names) == {"A.foo", "A.bar"}
    assert load_decl_names(hydrated) == {"B.rep", "B.member"}
