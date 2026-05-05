import json
import subprocess
import sys
from pathlib import Path

from tools.infra.real_prover_trace_bridge import normalize_real_record, run_bridge


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "real_prover_trace_bridge.py"


def _real_payload() -> dict:
    return {
        "formal_statement": "theorem demo : True := by sorry",
        "collect_results": [
            {
                "declaration": "demo",
                "success": True,
                "calls": [
                    [
                        "⊢ True",
                        ["trivial", "exact True.intro"],
                        [-0.1, -0.2],
                        "STATE:\n⊢ True\nTACTIC:",
                    ]
                ],
                "nodes": [
                    {"id": 0, "parent": 0, "depth": 0, "tactic": "", "state": ["⊢ True"]},
                    {"id": 1, "parent": 0, "depth": 1, "tactic": "trivial", "state": []},
                ],
                "stop_cause": {"nodes": False, "depth": False, "calls": False},
            }
        ],
        "formal_proof": "theorem demo : True := by\ntrivial",
    }


def test_normalize_real_record_preserves_search_nodes(tmp_path: Path) -> None:
    source = tmp_path / "real.json"
    row = normalize_real_record(_real_payload(), source, None)

    assert row["schema"] == "info_geometry.real_prover_trace.v1"
    assert row["success"] is True
    assert row["authority"]["lean_remains_proof_authority"] is True
    result = row["collect_results"][0]
    assert result["declaration"] == "demo"
    assert result["node_count"] == 2
    assert result["call_count"] == 1
    assert result["tactic_candidate_count"] == 2
    assert result["calls"][0]["tactics"][0]["tactic"] == "trivial"


def test_run_bridge_writes_jsonl_and_summary(tmp_path: Path) -> None:
    src = tmp_path / "input.jsonl"
    out = tmp_path / "out"
    src.write_text(json.dumps(_real_payload()) + "\n", encoding="utf-8")

    summary = run_bridge(src, out)

    rows = (out / "real_prover_trace_bridge.jsonl").read_text(encoding="utf-8").splitlines()
    assert len(rows) == 1
    assert summary["records"] == 1
    assert summary["successful_records"] == 1
    assert summary["search_nodes"] == 2
    assert (out / "real_prover_trace_bridge_summary.json").exists()


def test_real_prover_trace_bridge_cli(tmp_path: Path) -> None:
    src = tmp_path / "input.json"
    out = tmp_path / "out"
    src.write_text(json.dumps(_real_payload()), encoding="utf-8")

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(src),
            "--output-dir",
            str(out),
        ],
        cwd=REPO_ROOT,
        check=True,
    )

    summary = json.loads((out / "real_prover_trace_bridge_summary.json").read_text(encoding="utf-8"))
    assert summary["generator_calls"] == 1
    assert summary["tactic_candidates"] == 2
