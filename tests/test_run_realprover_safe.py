import os
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / "tools" / "run_realprover_safe.sh"


def test_run_realprover_safe_health_reports_installed_paths() -> None:
    proc = subprocess.run(
        ["bash", str(WRAPPER), "health"],
        cwd=ROOT,
        check=True,
        text=True,
        capture_output=True,
    )

    assert "realprover_safe=ok" in proc.stdout
    assert f"realprover_root={ROOT / 'external_refs' / 'REAL-Prover'}" in proc.stdout
    assert "prover_model_path=/home/goutev/models/frenzymath/REAL-Prover-model" in proc.stdout
    assert "lean_search=http://127.0.0.1:18080/retrieve_premises" in proc.stdout
    assert f"lean_test_path={ROOT}" in proc.stdout
    assert f"interactive_path={ROOT / 'external_refs' / 'interactive'}" in proc.stdout
    assert "expected_toolchain=leanprover/lean4:v4.28.0" in proc.stdout


def test_run_realprover_safe_active_lean_workspaces_are_428() -> None:
    expected = "leanprover/lean4:v4.28.0"
    assert (ROOT / "lean-toolchain").read_text().strip() == expected
    assert (ROOT / "external_refs" / "interactive" / "lean-toolchain").read_text().strip() == expected
    assert (ROOT / "external_refs" / "lean_test_v4160" / "lean-toolchain").read_text().strip() == expected


def test_run_realprover_safe_rejects_legacy_toolchain_even_with_env_override(
    tmp_path: Path,
) -> None:
    fake_workspace = tmp_path / "legacy-space"
    fake_workspace.mkdir()
    (fake_workspace / "lean-toolchain").write_text("leanprover/lean4:v4.16.0\n", encoding="utf-8")

    env = os.environ.copy()
    env["REALPROVER_LEAN_TEST_PATH"] = str(fake_workspace)
    env["REALPROVER_EXPECTED_TOOLCHAIN"] = "leanprover/lean4:v4.16.0"

    proc = subprocess.run(
        ["bash", str(WRAPPER), "health"],
        cwd=ROOT,
        env=env,
        text=True,
        capture_output=True,
    )

    assert proc.returncode == 1
    assert "expected leanprover/lean4:v4.28.0" in proc.stderr
