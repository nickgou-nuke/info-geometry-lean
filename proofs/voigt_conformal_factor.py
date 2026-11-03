#!/usr/bin/env python3
"""Word-model census for `InfoGeometry.Physics.VoigtConformalFactor`.

Certifies the exact matrix identities transcribed into Lean from Pauli's
*Relativitaetstheorie* (Encyklopaedie V 19, 1921), German original:

  (1) Lorentz boost ``L(b, g)``:      L^T eta L  =  eta        [Pauli Sec. 4, Eq. (I)/(II)]
      under ``g * r = 1`` and ``r^2 + b^2 = 1``  (g = gamma = 1/r, Pauli Eq. (8)).
  (2) Voigt boost ``V(b, r)`` (1887):  V^T eta V  =  (1 - b^2) eta   [Pauli Sec. 1 fn. 12]
      the conformal (light-cone preserving, non-isometric) reading;
      Voigt divides only the transverse coordinates: x' = x - vt,
      y' = y / gamma, z' = z / gamma, t' = t - vx/c^2.
  (3a) spatial swap E (x0 <-> x1):     E^T eta E = eta        [Pauli Sec. 24 reflections]
  (3b) time flip D (x3 -> -x3):        D^T eta D = eta
  (4) ``boost = g *. V``               (Voigt = boost minus the overall dilation)
  (5) ``V(b,r) * V(-b,r) = (1-b^2) * I`` [the kappa(v)*kappa(-v) product at the
      conformal level: Pauli Sec. 4 pp. 554-555, resolved to 1 after the
      Einstein/Poincare kappa(v) = 1 normalization]
  (6) ``L(b,g) * L(-b,g) = 1`` (the resolved group identity)
  (7) quadratic-form corollaries: eta(Vx, Vx) = (1-b^2) eta(x,x) (hypothesis-free given (2)),
      eta(Lx, Lx) = eta(x,x).

Conventions (Pauli Sec. 4): coordinates ordered (x0, x1, x2, x3), with x3 the
time slot, so eta = diag(1, 1, 1, -1) and the null cone is
x0^2 + x1^2 + x2^2 - x3^2 = 0 (Pauli's Eq. (2) with x4 = c*t placed last).

Strict mode: any failure exits 1, so the Lean transcription must be gated on
this script's success.
"""
from __future__ import annotations

import sys

import sympy as sp


def must(mat: sp.Matrix, expected: sp.Matrix, tag: str, failures: list[str]) -> None:
    if sp.simplify(mat - expected) == sp.zeros(mat.rows, mat.cols):
        print(f"  [OK]      {tag}")
    else:
        print(f"  [FAIL]    {tag}")
        print(f"            candidate:\n{sp.simplify(mat)}")
        failures.append(tag)


def main() -> int:
    b = sp.Symbol("b", real=True)
    r = sp.sqrt(1 - b**2)          # r = sqrt(1-b^2), so r^2 + b^2 = 1 identically
    g = 1 / r                      # g * r = 1 identically

    eta = sp.diag(1, 1, 1, -1)

    voigt = sp.Matrix([
        [r, 0, 0, 0],
        [0, r, 0, 0],
        [0, 0, 1, -b],
        [0, 0, -b, 1],
    ])
    voigt_rev = voigt.subs(b, -b)

    boost = sp.Matrix([
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, g, -g * b],
        [0, 0, -g * b, g],
    ])
    boost_rev = boost.subs(b, -b)

    spatial_swap = sp.Matrix([
        [0, 1, 0, 0],
        [1, 0, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 1],
    ])
    time_flip = sp.diag(1, 1, 1, -1)

    failures: list[str] = []
    print("voigt_conformal_factor census (strict):")

    # (1) Lorentz boost is eta-isometric.
    must(boost.T * eta * boost, eta, "(1) boost^T eta boost = eta", failures)

    # (2) Voigt boost is conformal with factor (1-b^2).
    must(voigt.T * eta * voigt, (1 - b**2) * eta,
         "(2) voigt^T eta voigt = (1-b^2) eta", failures)

    # (3a)/(3b) elementary isometries.
    must(spatial_swap.T * eta * spatial_swap, eta,
         "(3a) spatial_swap^T eta spatial_swap = eta", failures)
    must(time_flip.T * eta * time_flip, eta,
         "(3b) time_flip^T eta time_flip = eta", failures)

    # (4) boost = g * voigt.
    must(boost, g * voigt, "(4) boost = g * voigt", failures)

    # (5) Voigt round-trip: the unresolved kappa product.
    must(voigt * voigt_rev, (1 - b**2) * sp.eye(4),
         "(5) voigt(b) voigt(-b) = (1-b^2) I", failures)

    # (6) resolved boost round-trip.
    must(boost * boost_rev, sp.eye(4), "(6) boost(b) boost(-b) = I", failures)

    # (7) quadratic-form corollaries.
    x0, x1, x2, x3 = sp.symbols("x0 x1 x2 x3", real=True)
    xv = sp.Matrix([x0, x1, x2, x3])
    q = lambda v: (v.T * eta * v)[0, 0]
    if sp.simplify(q(voigt * xv) - (1 - b**2) * q(xv)) == 0:
        print("  [OK]      (7a) eta(voigt x, voigt x) = (1-b^2) eta(x,x)")
    else:
        print("  [FAIL]    (7a) eta(voigt x, voigt x) = (1-b^2) eta(x,x)")
        failures.append("(7a)")
    if sp.simplify(q(boost * xv) - q(xv)) == 0:
        print("  [OK]      (7b) eta(boost x, boost x) = eta(x,x)")
    else:
        print("  [FAIL]    (7b) eta(boost x, boost x) = eta(x,x)")
        failures.append("(7b)")

    total = 8
    passed = total - len(failures)
    print(f"\n{passed}/{total} checks passed; failures: {failures or 'none'}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
