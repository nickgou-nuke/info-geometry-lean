from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "quality" / "mathfulness_audit.py"


def _write_required_inputs(tmp_path: Path) -> dict[str, Path]:
    paths = {
        "decls": tmp_path / "decls.jsonl",
        "significance": tmp_path / "significance.json",
        "policy_lint": tmp_path / "canonical-policy-lint.json",
        "frontier_gate": tmp_path / "frontier-gate-report.json",
        "pauli_seal": tmp_path / "pauli-seal-audit.json",
        "json_out": tmp_path / "mathfulness.json",
        "md_out": tmp_path / "mathfulness.md",
    }
    paths["significance"].write_text("[]\n", encoding="utf-8")
    paths["policy_lint"].write_text("{}\n", encoding="utf-8")
    paths["frontier_gate"].write_text("{}\n", encoding="utf-8")
    paths["pauli_seal"].write_text("{}\n", encoding="utf-8")
    return paths


def _run_audit(paths: dict[str, Path], *extra: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--decls",
            str(paths["decls"]),
            "--significance",
            str(paths["significance"]),
            "--policy-lint",
            str(paths["policy_lint"]),
            "--frontier-gate",
            str(paths["frontier_gate"]),
            "--pauli-seal",
            str(paths["pauli_seal"]),
            "--json-out",
            str(paths["json_out"]),
            "--md-out",
            str(paths["md_out"]),
            *extra,
        ],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def _write_decl(paths: dict[str, Path], source: Path, *, name: str, kind: str = "theorem") -> None:
    paths["decls"].write_text(
        json.dumps({"name": name, "kind": kind, "file": str(source), "line": 1}) + "\n",
        encoding="utf-8",
    )


def _single_classification(report_path: Path) -> str:
    report = json.loads(report_path.read_text(encoding="utf-8"))
    assert report["summary"]["total"] == 1
    return report["rows"][0]["classification"]


def test_true_only_trivial_theorem_is_vacuous_or_surrogate(tmp_path: Path) -> None:
    paths = _write_required_inputs(tmp_path)
    source = tmp_path / "Vacuous.lean"
    source.write_text("theorem vacuousTrue : True := by trivial\n", encoding="utf-8")
    _write_decl(paths, source, name="vacuousTrue", kind="theorem")

    result = _run_audit(paths)

    assert result.returncode == 0, result.stderr
    assert _single_classification(paths["json_out"]) == "vacuous_or_surrogate"


def test_named_bridge_context_is_review_hint_not_promotion(tmp_path: Path) -> None:
    paths = _write_required_inputs(tmp_path)
    source = tmp_path / "Bridge.lean"
    source.write_text("def SomeBridgeContext : Nat := 0\n", encoding="utf-8")
    _write_decl(paths, source, name="SomeBridgeContext", kind="def")

    result = _run_audit(paths)

    assert result.returncode == 0, result.stderr
    report = json.loads(paths["json_out"].read_text(encoding="utf-8"))
    row = report["rows"][0]
    assert row["classification"] == "needs_review_named_bridge"
    assert row["promotable"] is False


def test_gate_fails_empty_selected_prefix_and_reports_global_failure(tmp_path: Path) -> None:
    paths = _write_required_inputs(tmp_path)
    source = tmp_path / "Real.lean"
    source.write_text("theorem realTheorem : 1 = 1 := by rfl\n", encoding="utf-8")
    _write_decl(paths, source, name="realTheorem", kind="theorem")

    result = _run_audit(paths, "--file-prefix", "lean/Does/Not/Match", "--gate")

    assert result.returncode == 1
    report = json.loads(paths["json_out"].read_text(encoding="utf-8"))
    assert report["summary"]["total"] == 0
    assert "no_selected_declarations" in report["global_failures"]
