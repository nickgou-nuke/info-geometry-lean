#!/usr/bin/env python3
"""Unified backend witness for Klein-quadric monodromy and de Rham-log potential.

Stacked checks (best effort, optional backends):
  - SymPy: core algebraic identities + local residue integral model
  - GAP: determinant/polar Gram matrix rank/nullspace
  - Sage: hypersurface data, Jacobian singular ideal dimension
  - galgebra / Clifford: geometric-algebra sanity checks
  - Macaulay2: optional D-module / deRham attempt on f=q(a)q(b)q(a-b)

This is not a proof script; it is a reproducible computational bridge that
feeds Lean statements in `KleinQuadricMonodromy.lean`.
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
from dataclasses import dataclass
from typing import Any

from sympy import I, Matrix, diff, expand, exp, integrate, pi, simplify, symbols


@dataclass
class BlockResult:
    name: str
    ok: bool
    payload: Any


@dataclass
class PipelineConfig:
    heavy_macaulay2: bool = False
    macaulay2_timeout: int = 300


def run_cmd(cmd: list[str], input_text: str | None = None, timeout: int = 90) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        input=None if input_text is None else input_text.encode(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=timeout,
    )


def sympy_block() -> BlockResult:
    try:
        a0, a1, a2, a3, b0, b1, b2, b3 = symbols("a0 a1 a2 a3 b0 b1 b2 b3")

        def q(v0, v1, v2, v3):
            return v0 ** 2 + v1 ** 2 + v2 ** 2 + v3 ** 2

        qA = q(a0, a1, a2, a3)
        qB = q(b0, b1, b2, b3)
        qAB = q(a0 - b0, a1 - b1, a2 - b2, a3 - b3)
        f = expand(qA * qB * qAB)

        vars4 = (a0, a1, a2, a3, b0, b1, b2, b3)
        dlog = [expand(diff(f, x) / f) for x in vars4]

        # Local 1d residue model on C\{0} by circle parameterization z=R e^{it}.
        t, R = symbols("t R", positive=True, real=True)
        zt = R * exp(I * t)
        integrand = (1 / zt) * diff(zt, t)
        loop_integral = simplify(integrate(integrand, (t, 0, 2 * pi)))

        # Klein form itself is homogeneous quadratic in Plücker-like coordinates
        p01, p02, p03, p12, p13, p23 = symbols("p01 p02 p03 p12 p13 p23")
        Q = expand(p01 * p23 - p02 * p13 + p03 * p12)
        polar_PP = simplify(2 * Q)

        payload = {
            "f_total_degree": 6,
            "num_vars": 8,
            "grad_len": len(dlog),
            "sample_dlog_term_0": str(dlog[0]),
            "loop_integral": str(loop_integral),
            "circle_formula": "∮ dz/z = 2*pi*I",
            "Q_formula": str(Q),
            "polar_self_formula": str(polar_PP),
            "det_zero_self_orthogonal": "Q=0 iff polar(P,P)=2Q",
        }

        assert loop_integral == 2 * pi * I
        assert payload["grad_len"] == 8
        return BlockResult("sympy", True, payload)
    except Exception as exc:
        return BlockResult("sympy", False, {"error": repr(exc)})


def gap_block() -> BlockResult:
    if not shutil.which("gap"):
        return BlockResult("gap", False, {"error": "gap executable not found"})

    gap_code = r'''
# Polar Gram matrix for Klein form in coordinates [p01,p02,p03,p12,p13,p23]
M := [
 [ 0, 0, 0, 0, 0, 1],
 [ 0, 0, 0, 0,-1, 0],
 [ 0, 0, 0, 1, 0, 0],
 [ 0, 0, 1, 0, 0, 0],
 [ 0,-1, 0, 0, 0, 0],
 [ 1, 0, 0, 0, 0, 0]
];
M := Matrix(GF(101), M);
Print("rank=", RankMat(M), "\n");
Print("det=", DeterminantMat(M), "\n");
ns := NullspaceMat(M);
Print("nullity=", Length(ns), "\n");
if Length(ns) > 0 then
  Print("sample_nullvec=", ns[1], "\n");
fi;
'''

    cp = run_cmd(["gap", "-q"], input_text=gap_code)
    if cp.returncode != 0:
        return BlockResult("gap", False, {"error": cp.stderr.decode(errors="ignore")})

    return BlockResult("gap", True, {"stdout": cp.stdout.decode(errors="ignore")})


def sage_block() -> BlockResult:
    if not shutil.which("sage"):
        return BlockResult("sage", False, {"error": "sage executable not found"})

    # keep this in pure Sage via external process so it runs in Sage's Python kernel.
    sage_code = """
import json
R = PolynomialRing(QQ, ['a0','a1','a2','a3','b0','b1','b2','b3'])
gens = R.gens()
(a0,a1,a2,a3,b0,b1,b2,b3) = gens
qA = a0^2 + a1^2 + a2^2 + a3^2
qB = b0^2 + b1^2 + b2^2 + b3^2
qAB = (a0-b0)^2 + (a1-b1)^2 + (a2-b2)^2 + (a3-b3)^2
f = qA*qB*qAB
jac = [f.derivative(v) for v in gens]
print("vars", len(gens))
print("deg_f", f.total_degree())
print("jac_terms", len(jac))
I = ideal([f] + jac)
print("ideal_gens", I.ngens())
try:
    print("sing_dim", I.dimension())
except Exception as e:
    print("sing_dim_error", e)
"""

    cp = run_cmd(["sage", "-c", sage_code], timeout=120)
    if cp.returncode != 0:
        return BlockResult("sage", False, {"error": cp.stderr.decode(errors="ignore")})
    return BlockResult("sage", True, {"stdout": cp.stdout.decode(errors="ignore")})


def galgebra_block() -> BlockResult:
    try:
        from galgebra.ga import Ga

        ga = Ga("e0 e1 e2 e3", g=[1, 1, 1, 1], coords=None)
        e = ga.mv()
        B = e[0] ^ e[1] + e[2] ^ e[3]
        payload = {
            "status": "ok",
            "bivector_square": str((B * B).expand()),
        }
        return BlockResult("galgebra", True, payload)
    except Exception as exc:  # pragma: no cover - environment dependent
        return BlockResult("galgebra", False, {"error": repr(exc)})


def clifford_block() -> BlockResult:
    try:
        from clifford import Cl

        _, blades = Cl(1, 3)
        basis_count = len(blades)
        payload = {"basis_count": basis_count, "sample_blade": list(blades)[:4]}
        return BlockResult("clifford", True, payload)
    except Exception as exc:  # pragma: no cover - environment dependent
        return BlockResult("clifford", False, {"error": repr(exc)})


def macaulay2_block(config: PipelineConfig) -> BlockResult:
    # Prefer system Macaulay2 when available.
    m2 = shutil.which("M2") or shutil.which("m2-stack")
    if m2 is None:
        return BlockResult("macaulay2", False, {"error": "M2/m2-stack executable not found"})

    smoke_code = r'''
needsPackage "Dmodules";
needsPackage "BernsteinSato";
R = QQ[x]
f = x^2
h = deRham f;
print "m2_smoke_ok";
'''

    try:
        smoke = run_cmd([m2, "-q"], input_text=smoke_code, timeout=60)
    except subprocess.TimeoutExpired:
        return BlockResult(
            "macaulay2",
            False,
            {"error": "m2 deRham smoke check timed out unexpectedly"},
        )

    smoke_out = smoke.stdout.decode(errors="ignore") + "\n" + smoke.stderr.decode(errors="ignore")
    smoke_ok = (smoke.returncode == 0) and ("m2_smoke_ok" in smoke_out)

    if not config.heavy_macaulay2:
        return BlockResult("macaulay2", smoke_ok, {"stdout": smoke_out, "mode": "smoke"})

    heavy_code = r'''
needsPackage "Dmodules";
needsPackage "BernsteinSato";

R = QQ[a0,a1,a2,a3,b0,b1,b2,b3]
qA = a0^2 + a1^2 + a2^2 + a3^2
qB = b0^2 + b1^2 + b2^2 + b3^2
qAB = (a0-b0)^2 + (a1-b1)^2 + (a2-b2)^2 + (a3-b3)^2
f = qA*qB*qAB

found = false;
try (
  h = deRham f;
  print "deRham_ok";
  found = true;
);
if found then print "deRham_status=ok" else print "deRham_status=missing";
'''

    try:
        cp = run_cmd([m2, "-q"], input_text=heavy_code, timeout=config.macaulay2_timeout)
    except subprocess.TimeoutExpired:
        return BlockResult(
            "macaulay2",
            False,
            {
                "stdout": smoke_out,
                "error": "m2 deRham command timed out (computation may be intensive).",
                "heavy": True,
            },
        )

    full_out = cp.stdout.decode(errors="ignore") + "\n" + cp.stderr.decode(errors="ignore")
    if cp.returncode != 0:
        return BlockResult("macaulay2", False, {"stdout": smoke_out + "\n" + full_out, "heavy": True})

    out = "smoke:\n" + smoke_out + "\nfull:\n" + full_out
    ok = "deRham_status=ok" in full_out
    return BlockResult("macaulay2", smoke_ok and ok, {"stdout": out, "heavy": True})


def pretty(result: BlockResult) -> str:
    return f"[{result.name}] ok={result.ok} -> {result.payload}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--heavy", action="store_true", help="run full 8-variable deRham in Macaulay2")
    parser.add_argument("--m2-timeout", type=int, default=300, help="timeout for full Macaulay2 deRham")
    args = parser.parse_args()

    config = PipelineConfig(heavy_macaulay2=args.heavy, macaulay2_timeout=args.m2_timeout)

    blocks = [
        sympy_block(),
        gap_block(),
        sage_block(),
        galgebra_block(),
        clifford_block(),
        macaulay2_block(config),
    ]

    for b in blocks:
        print(pretty(b))

    # one-line status summary suitable for scripts
    summary = {b.name: b.ok for b in blocks}
    print("SUMMARY", summary)


if __name__ == "__main__":
    main()
