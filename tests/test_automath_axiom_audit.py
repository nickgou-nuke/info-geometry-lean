import subprocess
from pathlib import Path
from unittest.mock import patch

from tools.infra.automath_pipeline import LeanGate


def test_axiom_audit_appends_only_explicit_targets(tmp_path: Path):
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text("import Mathlib\ntheorem Example.result : True := trivial\n", encoding="utf-8")
    seen = {}

    def fake_run(command, *, cwd, capture_output, text, timeout, check):
        seen["command"] = command
        seen["source"] = Path(command[-1]).read_text(encoding="utf-8")
        return subprocess.CompletedProcess(command, 0, stdout="axioms: []\n", stderr="")

    with patch("tools.infra.automath_pipeline.subprocess.run", side_effect=fake_run):
        result = LeanGate._run_axiom_audit(candidate, ["Example.result"])

    assert result.returncode == 0
    assert seen["source"].startswith("import Lean\nimport Mathlib\n")
    assert seen["source"].endswith("#print axioms Example.result\n")
    assert seen["command"][:3] == ["lake", "env", "lean"]
    assert len(seen["command"]) == 4


def test_axiom_audit_target_validation_fails_before_lock_or_compiler():
    gate = LeanGate()
    with patch("tools.infra.automath_pipeline.acquire_build_lock") as lock:
        result = gate.check_file(Path("candidate.lean"), axiom_audit_declarations=["x; #eval 1"])
    assert not result.passed
    assert "invalid or duplicate" in result.errors
    lock.assert_not_called()


def test_duplicate_axiom_audit_targets_are_rejected():
    gate = LeanGate()
    with patch("tools.infra.automath_pipeline.acquire_build_lock") as lock:
        result = gate.check_file(Path("candidate.lean"), axiom_audit_declarations=["Example.x", "Example.x"])
    assert not result.passed
    lock.assert_not_called()
