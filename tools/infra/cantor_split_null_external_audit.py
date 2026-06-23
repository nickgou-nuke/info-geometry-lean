#!/usr/bin/env python3
"""Bounded external audit for the finite Cantor/split-null bridge.

This script keeps the external lanes honest:
- Macaulay2 with explicit `Dmodules` load;
- Sage + GAP for a hyperbolic/isotropic readback;
- in-process SymPy, clifford, and galgebra checks.

It writes a JSON artifact under `artifacts/split_cantor_null/` and prints a
compact status summary.  Timeout or failure is recorded as data, not upgraded to
proof evidence.
"""

from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path
from typing import Any

import sympy as sp
from clifford import Cl
from galgebra.ga import Ga

ROOT = Path(__file__).resolve().parents[2]
ARTIFACT_DIR = ROOT / "artifacts" / "split_cantor_null"
ARTIFACT_PATH = ARTIFACT_DIR / "cantor_split_null_external_audit.json"


def det_z(z: tuple[Any, ...]) -> Any:
    r, s, x1, x2, x3, y1, y2, y3 = z
    return sp.expand(r * s - (x1 * y1 + x2 * y2 + x3 * y3))


def add_z(x: tuple[Any, ...], y: tuple[Any, ...]) -> tuple[Any, ...]:
    return tuple(sp.expand(a + b) for a, b in zip(x, y, strict=True))


def mul_z(x: tuple[Any, ...], y: tuple[Any, ...]) -> tuple[Any, ...]:
    r, s, x1, x2, x3, y1, y2, y3 = x
    R, S, u1, u2, u3, v1, v2, v3 = y
    return (
        sp.expand(r * R + (x1 * v1 + x2 * v2 + x3 * v3)),
        sp.expand((y1 * u1 + y2 * u2 + y3 * u3) + s * S),
        sp.expand(r * u1 + S * x1 - (y2 * v3 - y3 * v2)),
        sp.expand(r * u2 + S * x2 - (y3 * v1 - y1 * v3)),
        sp.expand(r * u3 + S * x3 - (y1 * v2 - y2 * v1)),
        sp.expand(R * y1 + s * v1 + (x2 * u3 - x3 * u2)),
        sp.expand(R * y2 + s * v2 + (x3 * u1 - x1 * u3)),
        sp.expand(R * y3 + s * v3 + (x1 * u2 - x2 * u1)),
    )


def polar_z(x: tuple[Any, ...], y: tuple[Any, ...]) -> Any:
    return sp.expand(det_z(add_z(x, y)) - det_z(x) - det_z(y))


def run_subprocess(command: list[str], timeout: int) -> dict[str, Any]:
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
        if completed.returncode == 0:
            status = "ok"
        else:
            status = "error"
        return {
            "command": command,
            "timeout": timeout,
            "status": status,
            "exit_code": completed.returncode,
            "stdout": completed.stdout,
            "stderr": completed.stderr,
        }
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        stderr = exc.stderr.decode() if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        return {
            "command": command,
            "timeout": timeout,
            "status": "timeout",
            "exit_code": 124,
            "stdout": stdout,
            "stderr": stderr,
        }


def write_temp(suffix: str, content: str) -> str:
    handle = tempfile.NamedTemporaryFile("w", suffix=suffix, delete=False)
    with handle:
        handle.write(content)
    return handle.name


def macaulay2_singular_locus_lane() -> dict[str, Any]:
    script = write_temp(
        ".m2",
        """
needsPackage \"Dmodules\";
R = QQ[a,b,u1,u2,u3,v1,v2,v3];
q = a*b - u1*v1 - u2*v2 - u3*v3;
J = ideal jacobian matrix{{q}};
S = trim radical(q + J);
print(\"STATUS=loaded\");
print(\"Q=\" | toString q);
print(\"SING_DIM=\" | toString dim S);
print(\"SING_IDEAL=\" | toString S);
""".strip()
        + "\n",
    )
    return run_subprocess(["M2", "--script", script], timeout=60)


def macaulay2_derham0_lane() -> dict[str, Any]:
    script = write_temp(
        ".m2",
        """
needsPackage \"Dmodules\";
R = QQ[a,b,u1,u2,u3,v1,v2,v3];
q = a*b - u1*v1 - u2*v2 - u3*v3;
print(\"STATUS=loaded\");
print(\"METHOD=deRham0\");
H0 = deRham(0, q);
print(\"AFTER_DE_RHAM0\");
print(toString H0);
""".strip()
        + "\n",
    )
    return run_subprocess(["M2", "--script", script], timeout=60)


def sage_gap_lane() -> dict[str, Any]:
    script = write_temp(
        ".sage",
        """
from sage.all import *
M = matrix(QQ, 8, 8, [
0,1,0,0,0,0,0,0,
1,0,0,0,0,0,0,0,
0,0,0,0,0,-1,0,0,
0,0,0,0,0,0,-1,0,
0,0,0,0,0,0,0,-1,
0,0,-1,0,0,0,0,0,
0,0,0,-1,0,0,0,0,
0,0,0,0,-1,0,0,0])
v = vector(QQ,[0,0,1,0,0,0,0,0])
w = vector(QQ,[0,0,0,0,0,1,0,0])
print('STATUS=sage_ok')
print('Q(v)=', (v*M*v.column())[0])
print('Q(w)=', (w*M*w.column())[0])
print('B(v,w)=', (v*M*w.column())[0])
print('M_RANK=', M.rank())
print('GAP_S3_ORDER=', gap('Size(Group((1,2,3),(1,2)))'))
""".strip()
        + "\n",
    )
    return run_subprocess(["sage", script], timeout=60)


def sympy_lane() -> dict[str, Any]:
    top_right = (0, 0, 1, 0, 0, 0, 0, 0)
    bottom_left = (0, 0, 0, 0, 0, 1, 0, 0)
    zero = (0, 0, 0, 0, 0, 0, 0, 0)

    def bit_gen(bit: bool) -> tuple[Any, ...]:
        return bottom_left if bit else top_right

    def address_gen(word: list[bool]) -> tuple[Any, ...]:
        return zero if not word else bit_gen(word[-1])

    assert det_z(top_right) == 0
    assert det_z(bottom_left) == 0
    assert mul_z(top_right, top_right) == zero
    assert mul_z(bottom_left, bottom_left) == zero
    assert polar_z(top_right, top_right) == 0
    assert polar_z(bottom_left, bottom_left) == 0
    assert polar_z(top_right, bottom_left) == -1
    assert address_gen([True, False]) == top_right
    assert address_gen([False, True]) == bottom_left

    return {
        "status": "ok",
        "top_right_det": int(det_z(top_right)),
        "bottom_left_det": int(det_z(bottom_left)),
        "top_right_sq_zero": mul_z(top_right, top_right) == zero,
        "bottom_left_sq_zero": mul_z(bottom_left, bottom_left) == zero,
        "self_polar_zero": polar_z(top_right, top_right) == 0 and polar_z(bottom_left, bottom_left) == 0,
        "cross_polar": int(polar_z(top_right, bottom_left)),
    }


def clifford_lane() -> dict[str, Any]:
    _, blades = Cl(4, 4, firstIdx=1)
    e1 = blades["e1"]
    e5 = blades["e5"]
    n_plus = e1 + e5
    n_minus = e1 - e5
    return {
        "status": "ok",
        "n_plus_sq_zero": str(n_plus * n_plus) == "0",
        "n_minus_sq_zero": str(n_minus * n_minus) == "0",
        "anticommutator": str(n_plus * n_minus + n_minus * n_plus),
    }


def galgebra_lane() -> dict[str, Any]:
    ga = Ga("e1 e2 e3 e4 f1 f2 f3 f4", g=[1, 1, 1, 1, -1, -1, -1, -1])
    e1, _e2, _e3, _e4, f1, _f2, _f3, _f4 = ga.mv()
    n_plus = (e1 + f1).simplify()
    n_minus = (e1 - f1).simplify()
    return {
        "status": "ok",
        "n_plus_sq_zero": str((n_plus * n_plus).simplify()) == "0",
        "n_minus_sq_zero": str((n_minus * n_minus).simplify()) == "0",
        "anticommutator": str((n_plus * n_minus + n_minus * n_plus).simplify()),
    }


def main() -> None:
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    report = {
        "topic": "finite Cantor/split-null bridge external audit",
        "lanes": {
            "macaulay2_singular_locus": macaulay2_singular_locus_lane(),
            "macaulay2_derham0": macaulay2_derham0_lane(),
            "sage_gap": sage_gap_lane(),
            "sympy": sympy_lane(),
            "clifford": clifford_lane(),
            "galgebra": galgebra_lane(),
        },
    }
    ARTIFACT_PATH.write_text(json.dumps(report, indent=2, sort_keys=True))
    for name, lane in report["lanes"].items():
        print(f"{name}: status={lane.get('status')}")
    print(f"artifact={ARTIFACT_PATH}")


if __name__ == "__main__":
    main()
