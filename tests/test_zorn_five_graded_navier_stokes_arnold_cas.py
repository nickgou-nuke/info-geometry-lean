"""
Multi-CAS Verification Suite for Archetypes XLII-LIV:
5-Graded Operator Zorn Algebra, BCFW Contact Recursion, Unified Three-Arnold Triad,
and Operator / 3D Navier-Stokes Lamb-Vorticity Depletion.

Runs exact verification across all 5 available Computer Algebra Systems:
1. SymPy (`tools/sympy/verify_zorn_five_graded_navier_stokes_arnold.py`)
2. SageMath (`tools/sage/verify_zorn_five_graded_navier_stokes_arnold.sage`)
3. GAP (`tools/gap/verify_zorn_five_graded_navier_stokes_arnold.g`)
4. Singular + `dmod.lib` (`tools/singular/verify_zorn_five_graded_navier_stokes_arnold.sing`)
5. Macaulay2 + `Dmodules` (`tools/macaulay2/verify_zorn_five_graded_navier_stokes_arnold.m2`)
"""

from __future__ import annotations
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def _run_cas(cmd: list[str]) -> str:
    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    output = (proc.stdout or "") + "\n" + (proc.stderr or "")
    assert proc.returncode == 0, f"Command {cmd} failed (exit {proc.returncode}):\n{output}"
    assert "ALL CHECKS PASSED" in output, f"Missing 'ALL CHECKS PASSED' in output:\n{output}"
    return output


def test_sympy_zorn_five_graded_navier_stokes_arnold() -> None:
    script = ROOT / "tools" / "sympy" / "verify_zorn_five_graded_navier_stokes_arnold.py"
    _run_cas([sys.executable, str(script)])


def test_sage_zorn_five_graded_navier_stokes_arnold() -> None:
    sage_bin = shutil.which("sage") or "/home/goutev/miniforge3/envs/sage/bin/sage"
    script = ROOT / "tools" / "sage" / "verify_zorn_five_graded_navier_stokes_arnold.sage"
    _run_cas([sage_bin, str(script)])


def test_gap_zorn_five_graded_navier_stokes_arnold() -> None:
    gap_bin = shutil.which("gap") or "/home/goutev/miniforge3/envs/sage/bin/gap"
    script = ROOT / "tools" / "gap" / "verify_zorn_five_graded_navier_stokes_arnold.g"
    _run_cas([gap_bin, "-b", "-q", str(script)])


def test_singular_zorn_five_graded_navier_stokes_arnold() -> None:
    singular_bin = shutil.which("Singular") or "/home/goutev/miniforge3/envs/sage/bin/Singular"
    script = ROOT / "tools" / "singular" / "verify_zorn_five_graded_navier_stokes_arnold.sing"
    _run_cas([singular_bin, "-q", str(script)])


def test_macaulay2_dmodules_zorn_five_graded_navier_stokes_arnold() -> None:
    m2_bin = shutil.which("M2") or "/usr/bin/M2"
    script = "tools/macaulay2/verify_zorn_five_graded_navier_stokes_arnold.m2"
    _run_cas([m2_bin, "-q", "-e", f'input "{script}"'])
