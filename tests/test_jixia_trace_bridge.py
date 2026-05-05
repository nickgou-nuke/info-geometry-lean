import json
import subprocess
import sys
from pathlib import Path

from tools.infra.jixia_trace_bridge import normalize_symbol, run_bridge


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "jixia_trace_bridge.py"


def test_normalize_symbol_converts_name_arrays_and_references(tmp_path: Path) -> None:
    row = {
        "name": ["Demo", "thm"],
        "kind": "theorem",
        "typeReadable": "True",
        "typeReferences": [["True"], ["Eq"]],
        "valueReferences": [["trivial"]],
        "isProp": True,
    }

    payload = normalize_symbol(row, tmp_path / "sym.json", 0)

    assert payload["schema"] == "info_geometry.jixia.symbol.v1"
    assert payload["name"] == "Demo.thm"
    assert payload["type_references"] == ["Eq", "True"]
    assert payload["value_references"] == ["trivial"]
    assert payload["authority"]["lean_remains_proof_authority"] is True


def test_run_bridge_writes_all_sidecars(tmp_path: Path) -> None:
    decl = tmp_path / "decl.json"
    sym = tmp_path / "sym.json"
    elab = tmp_path / "elab.json"
    lines = tmp_path / "lines.json"
    out = tmp_path / "out"
    decl.write_text(
        json.dumps(
            [
                {
                    "name": ["Demo", "thm"],
                    "kind": "theorem",
                    "ref": {"range": [0, 10], "original": True, "pp?": "theorem Demo.thm"},
                }
            ]
        ),
        encoding="utf-8",
    )
    sym.write_text(
        json.dumps(
            [
                {
                    "name": ["Demo", "thm"],
                    "kind": "theorem",
                    "typeReferences": [["True"]],
                    "valueReferences": [["trivial"]],
                    "isProp": True,
                }
            ]
        ),
        encoding="utf-8",
    )
    elab.write_text(
        json.dumps(
            [
                {
                    "info": {
                        "tactic": {
                            "references": [["trivial"]],
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
    lines.write_text(json.dumps([{"start": 20, "state": [{"pp": "⊢ True", "type": "True"}]}]), encoding="utf-8")

    summary = run_bridge(
        declaration_json=decl,
        symbol_json=sym,
        elaboration_json=elab,
        line_json=lines,
        output_dir=out,
    )

    assert summary["rows"] == {
        "declarations": 1,
        "symbols": 1,
        "tactic_transitions": 1,
        "line_states": 1,
    }
    assert (out / "jixia_tactic_transitions.jsonl").exists()
    tactic = json.loads((out / "jixia_tactic_transitions.jsonl").read_text(encoding="utf-8"))
    assert tactic["tactic_syntax"] == "trivial"
    assert tactic["before"][0]["pp"] == "⊢ True"


def test_jixia_trace_bridge_cli(tmp_path: Path) -> None:
    sym = tmp_path / "sym.json"
    out = tmp_path / "out"
    sym.write_text(json.dumps([{"name": ["Demo", "x"], "kind": "definition"}]), encoding="utf-8")

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--symbol-json",
            str(sym),
            "--output-dir",
            str(out),
        ],
        cwd=REPO_ROOT,
        check=True,
    )

    summary = json.loads((out / "jixia_trace_bridge_summary.json").read_text(encoding="utf-8"))
    assert summary["rows"]["symbols"] == 1
