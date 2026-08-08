#!/usr/bin/env python3
"""Omega Protocol verification runner.

Runs the standalone symbolic matrix witnesses and the Lean build that verifies
Fibonacci -> Clifford atom -> braid/Clifford integration -> Souriau/Möbius links.

Usage:
  python3 run_omega_protocol_checks.py
  python3 run_omega_protocol_checks.py --sympy-only
  python3 run_omega_protocol_checks.py --lean-only
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent

SYMPY_WITNESSES = [
    "artin_parity_braid_witness.py",
    "atomic_clifford_kan_sympy.py",
    "fibonacci_clifford_bridge_sympy.py",
    "braid_clifford_integration_sympy.py",
    "waveguide_ep_braid_spec.py",
    "scattering_smatrix_sympy.py",
    "nonhermitian_smatrix_defect_sympy.py",
    "silicon_photonic_chip_coefficients.py",
    "two_port_scattering_coefficients_sympy.py",
    "photonic_braid_chip_sim.py",
    "nonhermitian_kitaev_cuntz_chain.py",
    "tetron_parity_lifetime_bridge.py",
    "matrix2_kan_pauli_chain_sympy.py",
    "transfer_matrix_scattering_sympy.py",
    "photonic_hardware_layout_sympy.py",
    "optical_andreev_spinor_sympy.py",
    "exceptional_point_collapse.py",
]

LEAN_MODULES = [
    "AtomicCliffordKAN.lean",
    "FibonacciCliffordBridge.lean",
    "BraidCliffordIntegration.lean",
    "SouriauMoebiusCoupling.lean",
    "BogoliubovFrameTransport.lean",
    "WaveguideEPBraidSpec.lean",
    "ScatteringSMatrix.lean",
    "NonHermitianSMatrixDefect.lean",
    "SiliconPhotonicChipCoefficients.lean",
    "TwoPortScatteringCoefficients.lean",
    "ArtinParityFlowWitness.lean",
    "PhotonicCMTTMM.lean",
    "NonHermitianKitaevCuntzChain.lean",
    "TetronParityLifetimeBridge.lean",
    "Matrix2KANPauliChain.lean",
    "TransferMatrixScattering.lean",
    "PhotonicHardwareLayout.lean",
    "OpticalAndreevSpinor.lean",
    "ExceptionalPointCollapse.lean",
]



def run(cmd: list[str], *, cwd: Path = ROOT) -> tuple[bool, int | None]:
    print(f"\n>>> {' '.join(cmd)}", flush=True)
    result = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode != 0:
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        else:
            print(result.stdout, file=sys.stderr)
        return False, result.returncode
    return True, None


def run_sympy() -> tuple[int, list[str]]:
    print("\n=== SymPy matrix witnesses ===", flush=True)
    failures: list[str] = []
    for script in SYMPY_WITNESSES:
        ok, err = run([sys.executable, script])
        if not ok:
            failures.append(f"{script}: exit {err}")
    return len(failures), failures


def run_lean_modules() -> tuple[int, list[str]]:
    print("\n=== Lean module checks ===", flush=True)
    failures: list[str] = []
    for module in LEAN_MODULES:
        ok, err = run(["lake", "env", "lean", module])
        if not ok:
            failures.append(f"{module}: exit {err}")
    return len(failures), failures


def run_lake_build() -> tuple[int, list[str]]:
    print("\n=== Full Lean build ===", flush=True)
    ok, err = run(["lake", "build"])
    return (0, []) if ok else (1, [f"lake build: exit {err}"])


def main() -> int:
    parser = argparse.ArgumentParser(description="Run Omega Protocol verification checks")
    parser.add_argument("--sympy-only", action="store_true", help="run only SymPy witnesses")
    parser.add_argument("--lean-only", action="store_true", help="run only Lean checks/build")
    parser.add_argument(
        "--modules-only",
        action="store_true",
        help="for Lean mode, check modules but skip full lake build",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="exit with failure if any witness fails",
    )
    args = parser.parse_args()

    if args.sympy_only and args.lean_only:
        parser.error("--sympy-only and --lean-only are mutually exclusive")

    failures: list[str] = []

    if not args.lean_only:
        _, sympy_fail = run_sympy()
        failures.extend(sympy_fail)
    if not args.sympy_only:
        _, lean_fail = run_lean_modules()
        failures.extend(lean_fail)
        if not args.modules_only:
            _, build_fail = run_lake_build()
            failures.extend(build_fail)

    if failures:
        print("\nOMEGA_PROTOCOL_REPORT", file=sys.stderr)
        for item in failures:
            print(f" - {item}", file=sys.stderr)
        if args.strict:
            return 1
        print("\nOMEGA_PROTOCOL_COMPLETED_WITH_FAILURES", file=sys.stderr)
        return 0

    print("\nOMEGA_PROTOCOL_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
