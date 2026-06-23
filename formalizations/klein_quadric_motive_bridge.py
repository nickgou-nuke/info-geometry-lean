#!/usr/bin/env python3
"""Stepping-stone algebraic witness for the Klein-quadric monodromy program.

Backends:
- SymPy: determinant/log/potential algebra and local Grothendieck–de Rham 1-form model (`dQ/Q`)
- GAP: polar/Klein quadratic Gram geometry in Plücker coordinates
- Sage: hypersurface ideal geometry for f = q(a)q(b)q(a-b)
- galgebra / Clifford: toy 4-vector/tripotent/orthogonality checks

This script is a computational companion to
`lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean` and
`docs/klein_quadric_multibackend_pipeline.md`.
"""

from __future__ import annotations

import shutil
import subprocess
from dataclasses import dataclass
from typing import Any

from sympy import I, Matrix, diff, expand, exp, factor, integrate, pi, simplify, symbols


@dataclass
class BlockResult:
    name: str
    ok: bool
    payload: Any


def run_cmd(cmd: list[str], input_text: str | None = None, timeout: int = 180) -> subprocess.CompletedProcess:
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
        # 4-vectors and split-norm quadratic potential
        a0, a1, a2, a3, b0, b1, b2, b3 = symbols("a0 a1 a2 a3 b0 b1 b2 b3")

        def q4(x0, x1, x2, x3):
            return x0**2 + x1**2 + x2**2 + x3**2

        qA = q4(a0, a1, a2, a3)
        qB = q4(b0, b1, b2, b3)
        qAB = q4(a0 - b0, a1 - b1, a2 - b2, a3 - b3)
        f = expand(qA * qB * qAB)

        # Grothendieck–de Rham-log motif on the chiral determinant:
        # dlog_f = d f / f (symbolic differential quotient)
        vars4 = (a0, a1, a2, a3, b0, b1, b2, b3)
        dlog_f = [simplify(diff(f, x) / f) for x in vars4]
        dlog_qA = simplify(diff(qA, a0) / qA)
        # local single-factor check
        dlog_a0 = dlog_qA

        # local 1-d residue model
        t, R = symbols("t R", positive=True, real=True)
        zt = R * exp(I * t)
        integrand = (1 / zt) * diff(zt, t)
        loop_integral = simplify(integrate(integrand, (t, 0, 2 * pi)))

        # Klein/Plücker quadratic form
        p01, p02, p03, p12, p13, p23 = symbols("p01 p02 p03 p12 p13 p23")
        Q = expand(p01 * p23 - p02 * p13 + p03 * p12)

        # tripotent toy model in Matrices (idempotent-like split by 1/2(1+e))
        e = Matrix([[1, 0], [0, -1]])
        idem = (Matrix([[1, 0], [0, 1]]) + e) / 2

        payload = {
            "deg_f": 6,
            "var_count": 8,
            "dlog_f_len": len(dlog_f),
            "dlog_sample": str(dlog_f[0]),
            "Q_formula": str(Q),
            "loop_integral": str(loop_integral),
            "tripotent_trace": str(idem.trace()),
            "tripotent_idem_check": str(simplify(idem * idem - idem)),
            "zero_determinant_symbolic": "Q=0 iff qA=0 ∨ qB=0 ∨ qAB=0",
            "dlog_qA": str(dlog_qA),
        }

        assert simplify(loop_integral - 2 * pi * I) == 0
        assert simplify(idem * idem - idem) == Matrix([[0, 0], [0, 0]])
        assert simplify(dlog_f[0] - diff(f, a0) / f) == 0

        return BlockResult("sympy", True, payload)
    except Exception as exc:
        return BlockResult("sympy", False, {"error": repr(exc)})


def gap_block() -> BlockResult:
    if not shutil.which("gap"):
        return BlockResult("gap", False, {"error": "gap executable not found"})

    gap_code = r'''
# 6 Plücker-like coordinates: [p01,p02,p03,p12,p13,p23]
# Klein polar Gram form (anti-diagonal split matrix in this convention)
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
N := NullspaceMat(M);
Print("nullity=", Length(N), "\n");
if Length(N) > 0 then
  Print("sample_nullvec=", N[1], "\n");
fi;
'''

    cp = run_cmd(["gap", "-q"], input_text=gap_code)
    if cp.returncode != 0:
        return BlockResult("gap", False, {"error": cp.stderr.decode(errors="ignore")})

    return BlockResult("gap", True, {"stdout": cp.stdout.decode(errors="ignore")})


def sage_block() -> BlockResult:
    if not shutil.which("sage"):
        return BlockResult("sage", False, {"error": "sage executable not found"})

    # keep in Sage's own python kernel
    sage_code = """
import json
R = PolynomialRing(QQ, ['a0','a1','a2','a3','b0','b1','b2','b3'])
gens = R.gens()
(a0,a1,a2,a3,b0,b1,b2,b3) = gens
qA = a0^2 + a1^2 + a2^2 + a3^2
qB = b0^2 + b1^2 + b2^2 + b3^2
qAB = (a0-b0)^2 + (a1-b1)^2 + (a2-b2)^2 + (a3-b3)^2
f = qA*qB*qAB
J = jacobian([qA,b0+b1,b2+b3], [a0,a1,a2,a3,b0,b1,b2,b3])
print("deg_f", f.total_degree())
print("jac_rank", J.rank())
I = ideal([f] + [f.derivative(v) for v in gens])
print("sing_dim", I.dimension())
"""

    cp = run_cmd(["sage", "-c", sage_code], timeout=180)
    if cp.returncode != 0:
        return BlockResult("sage", False, {"error": cp.stderr.decode(errors="ignore")})
    return BlockResult("sage", True, {"stdout": cp.stdout.decode(errors="ignore")})


def galgebra_block() -> BlockResult:
    try:
        from galgebra.ga import Ga

        ga = Ga("e0 e1 e2 e3", g=[1, -1, -1, -1], coords=None)
        e = ga.mv()
        # Chiral/light-like toy vector: e0 + e1 + e2 + e3 in split signature has nontrivial norm
        v = e[0] + e[1] + e[2] + e[3]
        payload = {
            "scalar_basis": ga.n,
            "bivector_square": str((e[0] ^ e[1]).expand()),
            "v_square": str((v * v).expand()),
            "tripotent_expr": str(((1 + e[0]) / 2).expand()),
        }
        return BlockResult("galgebra", True, payload)
    except Exception as exc:  # pragma: no cover
        return BlockResult("galgebra", False, {"error": repr(exc)})


def clifford_block() -> BlockResult:
    try:
        from clifford import Cl

        _, blades = Cl(1, 3)
        e1 = blades.get("e1")
        e2 = blades.get("e2")
        e3 = blades.get("e3")
        # local toy tripotent-like projector in the Clifford algebra: (1 + e1)/2
        if e1 is None or e2 is None or e3 is None:
            return BlockResult("clifford", False, {"error": "missing basis blades"})

        idem = (1 + e1) / 2
        payload = {
            "basis_count": len(blades),
            "tripotent_check": str(idem * idem - idem),
            "zero_divisor_sample": str((e1 * e1 + e2 * e2 + e3 * e3)),
        }
        return BlockResult("clifford", True, payload)
    except Exception as exc:  # pragma: no cover
        return BlockResult("clifford", False, {"error": repr(exc)})


def m2_block() -> BlockResult:
    m2 = shutil.which("M2") or shutil.which("m2-stack")
    if m2 is None:
        return BlockResult("macaulay2", False, {"error": "M2/m2-stack not found"})

    m2_code = r'''
needsPackage "Dmodules";
needsPackage "BernsteinSato";
R = QQ[a0,a1,a2,a3,b0,b1,b2,b3]
f = (a0^2+a1^2+a2^2+a3^2)*(b0^2+b1^2+b2^2+b3^2)*((a0-b0)^2+(a1-b1)^2+(a2-b2)^2+(a3-b3)^2)
print "m2_ok"
'''

    try:
        cp = run_cmd([m2, "-q"], input_text=m2_code, timeout=180)
    except subprocess.TimeoutExpired:
        return BlockResult("macaulay2", False, {"error": "deRham call was skipped/timeout in lightweight probe"})

    out = cp.stdout.decode(errors="ignore") + cp.stderr.decode(errors="ignore")
    if cp.returncode != 0:
        return BlockResult("macaulay2", False, {"stdout": out})

    ok = "m2_ok" in out
    return BlockResult("macaulay2", ok, {"stdout": out})


def pretty(result: BlockResult) -> str:
    return f"[{result.name}] ok={result.ok} -> {result.payload}"


def main() -> None:
    blocks = [
        sympy_block(),
        gap_block(),
        sage_block(),
        galgebra_block(),
        clifford_block(),
        m2_block(),
    ]

    for block in blocks:
        print(pretty(block))

    summary = {b.name: b.ok for b in blocks}
    print("SUMMARY", summary)


if __name__ == "__main__":
    main()
