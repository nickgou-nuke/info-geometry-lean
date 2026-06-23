#!/usr/bin/env python3
"""
Finite multi-system validator for the Penrose / Artin braid / Hecke / split-Cl(1,1)
digest packet.

Scope is deliberately finite and algebraic:
  * SymPy checks a 5-fold reflection on pentagrid labels, S3 braid generators,
    a Hecke quadratic relation, and a concrete split-Cl(1,1) matrix atom.
  * GAP checks the S3/Coxeter quotient and an Artin automorphism relation on F3.
  * Sage checks cyclotomic pentagrid arithmetic in Q(zeta_5) and S3 order.
  * clifford and galgebra check the same split signature atom / reflection closure.

Not claimed: Penrose tiling classification, quotient-space Klein bottle theorem,
Jones polynomial computation, Lorentz/Spin/Pin representation theorem, particle
physics, spacetime emergence, or an infinite categorical colimit construction.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
SAGE = shutil.which("sage") or "/home/goutev/miniforge3/envs/sage/bin/sage"
GAP = shutil.which("gap") or "/home/goutev/miniforge3/envs/sage/bin/gap"


def assert_zero_matrix(M: sp.Matrix, label: str) -> None:
    if any(sp.expand(x) != 0 for x in M):
        raise AssertionError(f"{label} is not zero: {M}")


def verify_sympy() -> dict[str, object]:
    # Pentagrid label reflection j ↦ -j mod 5 is involutive and fixes label 0.
    labels = list(range(5))
    rho = {j: (-j) % 5 for j in labels}
    assert {rho[j] for j in labels} == set(labels)
    assert all(rho[rho[j]] == j for j in labels)
    assert rho[0] == 0
    assert [rho[j] for j in labels] == [0, 4, 3, 2, 1]

    # Symmetric quotient of B3: adjacent transpositions satisfy braid and involution.
    def s1(t: tuple[int, int, int]) -> tuple[int, int, int]:
        a, b, c = t
        return (b, a, c)

    def s2(t: tuple[int, int, int]) -> tuple[int, int, int]:
        a, b, c = t
        return (a, c, b)

    basis = [(1, 2, 3), (3, 2, 1), (2, 1, 3)]
    for v in basis:
        assert s1(s1(v)) == v
        assert s2(s2(v)) == v
        assert s1(s2(s1(v))) == s2(s1(s2(v)))

    # Hecke characteristic equation for diagonal representatives with eigenvalues q and -1.
    q = sp.symbols("q")
    H = sp.diag(q, -1)
    I2 = sp.eye(2)
    assert_zero_matrix((H - q * I2) * (H + I2), "Hecke quadratic")

    # Split Cl(1,1) atom: e_+^2 = +1, e_-^2 = -1, anticommutator zero.
    ep = sp.Matrix([[1, 0], [0, -1]])
    em = sp.Matrix([[0, 1], [-1, 0]])
    assert_zero_matrix(ep * ep - I2, "ep^2 - I")
    assert_zero_matrix(em * em + I2, "em^2 + I")
    assert_zero_matrix(ep * em + em * ep, "Cl(1,1) anticommutator")

    return {
        "pentagrid_reflection": [rho[j] for j in labels],
        "s3_braid_relation": True,
        "hecke_quadratic": True,
        "cl11_matrix_atom": True,
    }


def run_gap() -> dict[str, object]:
    script = r'''
F := FreeGroup("x1", "x2", "x3");;
x1 := F.1;; x2 := F.2;; x3 := F.3;;
beta1 := GroupHomomorphismByImages(F, F, [x1,x2,x3], [x2, x2*x1*x2^-1, x3]);;
beta2 := GroupHomomorphismByImages(F, F, [x1,x2,x3], [x1, x3, x3*x2*x3^-1]);;
LHS := beta1 * beta2 * beta1;; RHS := beta2 * beta1 * beta2;;
if not (Image(LHS,x1)=Image(RHS,x1) and Image(LHS,x2)=Image(RHS,x2) and Image(LHS,x3)=Image(RHS,x3)) then Error("Artin automorphism braid relation failed"); fi;
S := SymmetricGroup(3);;
if Size(S) <> 6 then Error("S3 order failed"); fi;
if Order((1,2)) <> 2 or Order((2,3)) <> 2 then Error("adjacent transposition involution failed"); fi;
if (1,2)*(2,3)*(1,2) <> (2,3)*(1,2)*(2,3) then Error("S3 braid relation failed"); fi;
Print("GAP_OK\n");
'''
    proc = subprocess.run([GAP, "-q"], input=script, text=True, capture_output=True, check=True)
    assert "GAP_OK" in proc.stdout
    return {"gap_ok": True, "stdout": proc.stdout.strip()}


def run_sage() -> dict[str, object]:
    script = r'''
K.<z> = CyclotomicField(5)
assert z^4 + z^3 + z^2 + z + 1 == 0
roots = [z^j for j in range(5)]
assert [roots[(-j) % 5] for j in range(5)] == [z^((-j) % 5) for j in range(5)]
G = SymmetricGroup(3)
s1 = G((1,2)); s2 = G((2,3))
assert G.order() == 6
assert s1^2 == G.one() and s2^2 == G.one()
assert s1*s2*s1 == s2*s1*s2
print("SAGE_OK")
'''
    sage_cache = Path("/tmp/info_geometry_sage_cache")
    sage_cache.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "DOT_SAGE": str(sage_cache)}
    proc = subprocess.run([SAGE, "-c", script], text=True, capture_output=True, check=True, env=env)
    assert "SAGE_OK" in proc.stdout
    return {"sage_ok": True, "stdout": proc.stdout.strip()}


def verify_clifford() -> dict[str, object]:
    os.environ.setdefault("NUMBA_DISABLE_JIT", "1")
    os.environ.setdefault("NUMBA_CACHE_DIR", "/tmp/numba-cache")
    import clifford  # type: ignore

    layout, blades = clifford.Cl(1, 1, firstIdx=1)
    e1 = blades["e1"]
    e2 = blades["e2"]
    assert (e1 * e1)[()] == 1
    assert (e2 * e2)[()] == -1
    assert e1 * e2 + e2 * e1 == 0
    return {"clifford_ok": True, "dims": layout.dims}


def verify_galgebra() -> dict[str, object]:
    from galgebra.ga import Ga  # type: ignore

    ga = Ga("u v", g=[1, -1])
    u, v = ga.mv()
    assert str(u * u) == "1"
    assert str(v * v) == "-1"
    assert str(u * v + v * u) == "0"

    # Adjacent reflection normals for S3; check braid action on basis vectors.
    ga3 = Ga("e1 e2 e3", g=[1, 1, 1])
    e1, e2, e3 = ga3.mv()
    n12 = (e1 - e2) * (1 / sp.sqrt(2))
    n23 = (e2 - e3) * (1 / sp.sqrt(2))

    def r(n, x):
        return -n * x * n

    for x in (e1, e2, e3):
        assert r(n12, r(n12, x)) == x
        assert r(n23, r(n23, x)) == x
        assert r(n12, r(n23, r(n12, x))) == r(n23, r(n12, r(n23, x)))
    return {"galgebra_ok": True}


def main() -> None:
    result = {
        "sympy": verify_sympy(),
        "gap": run_gap(),
        "sage": run_sage(),
        "clifford": verify_clifford(),
        "galgebra": verify_galgebra(),
    }
    print("PENROSE_BRAID_LORENTZ_FINITE_PACKET_OK")
    print(json.dumps(result, sort_keys=True))
    print(
        "scope: finite pentagrid label reflection + S3/Artin braid relation + "
        "Hecke quadratic + split-Cl(1,1) atom only; no Lorentz/Pin/Penrose "
        "classification/Jones/infinite-colimit theorem asserted"
    )


if __name__ == "__main__":
    main()
