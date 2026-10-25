"""
Multi-CAS Verification Suite for the 7-Pillar Cuntz-Cantor-Clifford-Bogoliubov-Virasoro-SuperGrassmannian-Supercolor Synthesis:
1. Pillar 1: Cuntz Shift & Unitary Phase Tilt, Binary Cantor Tilt/Switch Local Cl(1,1), & Doubled Cuntz Hopping
2. Pillar 2: Tensor-Algebra Cuntz/Toeplitz Quotient, q-CCR Interpolation (q=-1 CAR, q=0 Cuntz, q=+1 CCR Trace No-Go), & Cuntz O_3 Tri-SUSY SU(3)
3. Pillar 3: Cl(n,n) = Cl(1,1)^{otimes n} Kronecker Tensor Tower & Jordan-Wigner Cross-Site CAR
4. Pillar 4: Tetrad/Vielbein-Defined Bogoliubov Transformed Frame on Doubled Spin-Polarized Copies & Hopping = {Q, Q}
5. Pillar 5: UHF Inductive Colimit Boundary (diagEmbedSucc, prefix-extension, stageHop bit-flip commutation)
6. Pillar 6: Heisenberg Current -> Sugawara Stress Tensor -> Virasoro Algebra & Weight-Shift Ladder [L_n, J_m] = -m J_{n+m}
7. Pillar 7: 5-Graded Super-Grassmannian Cl(5,5) = Cl(1,1) hat{otimes} Cl(4,4), KKT Quintic Law, Penrose Twistor Nullity, & Z2xZ2 Supercolor SUSY

Runs exact verification across all 5 available Computer Algebra Systems:
1. SymPy (`tools/sympy/verify_cuntz_clifford_bogoliubov_virasoro_supercolor.py`)
2. SageMath (`tools/sage/verify_cuntz_clifford_bogoliubov_virasoro_supercolor.sage`)
3. GAP (`tools/gap/verify_cuntz_clifford_bogoliubov_virasoro_supercolor.g`)
4. Singular + `dmod.lib` (`tools/singular/verify_cuntz_clifford_bogoliubov_virasoro_supercolor.sing`)
5. Macaulay2 + `Dmodules` (`tools/macaulay2/verify_cuntz_clifford_bogoliubov_virasoro_supercolor.m2`)
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


def test_sympy_cuntz_clifford_bogoliubov_virasoro_supercolor() -> None:
    script = ROOT / "tools" / "sympy" / "verify_cuntz_clifford_bogoliubov_virasoro_supercolor.py"
    _run_cas([sys.executable, str(script)])


def test_sage_cuntz_clifford_bogoliubov_virasoro_supercolor() -> None:
    sage_bin = shutil.which("sage") or "/home/goutev/miniforge3/envs/sage/bin/sage"
    script = ROOT / "tools" / "sage" / "verify_cuntz_clifford_bogoliubov_virasoro_supercolor.sage"
    _run_cas([sage_bin, str(script)])


def test_gap_cuntz_clifford_bogoliubov_virasoro_supercolor() -> None:
    gap_bin = shutil.which("gap") or "/home/goutev/miniforge3/envs/sage/bin/gap"
    script = ROOT / "tools" / "gap" / "verify_cuntz_clifford_bogoliubov_virasoro_supercolor.g"
    _run_cas([gap_bin, "-b", "-q", str(script)])


def test_singular_cuntz_clifford_bogoliubov_virasoro_supercolor() -> None:
    singular_bin = shutil.which("Singular") or "/home/goutev/miniforge3/envs/sage/bin/Singular"
    script = ROOT / "tools" / "singular" / "verify_cuntz_clifford_bogoliubov_virasoro_supercolor.sing"
    _run_cas([singular_bin, "-q", str(script)])


def test_macaulay2_dmodules_cuntz_clifford_bogoliubov_virasoro_supercolor() -> None:
    m2_bin = shutil.which("M2") or "/usr/bin/M2"
    script = "tools/macaulay2/verify_cuntz_clifford_bogoliubov_virasoro_supercolor.m2"
    _run_cas([m2_bin, "-q", "-e", f'input "{script}"'])
