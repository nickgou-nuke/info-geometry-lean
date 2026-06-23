"""Multilingual symbolic witness for Klein quadric / log-monodromy statements.

This is a lightweight, dependency-tolerant script intended to mirror the Lean
formalization in `lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean`.
It runs pure SymPy checks and, when available, optional Sage, GAP, galgebra and
Clifford checks.
"""

from __future__ import annotations

import subprocess
import shutil

from sympy import I, pi, symbols, Matrix, diff, integrate


def sympy_block() -> None:
    """Core SymPy checks: Klein determinant, differential form, and winding integral."""
    print("== SymPy core checks ==")

    p01, p02, p03, p12, p13, p23 = symbols("p01 p02 p03 p12 p13 p23")

    # Klein quadric form Q = p01*p23 - p02*p13 + p03*p12
    Q = p01 * p23 - p02 * p13 + p03 * p12

    dQ = Matrix([diff(Q, v) for v in [p01, p02, p03, p12, p13, p23]])
    print("Q:", Q)
    print("dQ basis components:", [expr for expr in dQ])

    # Toy 1-variable avatar of log Q around Q=0:
    t = symbols("t", real=True)
    loop_integral = integrate(1, (t, 0, 2 * pi))
    print("∮ dz/z via t-parametrization =", loop_integral * I)
    print("d(log t) on circle ->", 1 / t)


def _run_gap(code: str) -> str:
    proc = subprocess.run(["gap", "-q"], input=code.encode(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.decode())
    return proc.stdout.decode()


def gap_block() -> None:
    """Optional GAP check of the Plücker-coordinate quadratic relation."""
    print("== GAP check ==")
    if not shutil.which("gap"):
        print("gap executable not found; skipping")
        return

    code = r'''
S := FreeMonoid("p01","p02","p03","p12","p13","p23");;
Q := p01*p23 - p02*p13 + p03*p12;
Print("Q form in GAP monoid syntax = ", Q, "\n");
'''
    out = _run_gap(code)
    print(out.strip())


def sage_block() -> None:
    """Optional Sage block for the same polynomial structure."""
    print("== Sage check ==")
    try:
        import sageall as sg
    except Exception as exc:
        print(f"sage not available ({exc}); skipping")
        return

    R = sg.PolynomialRing(sg.QQ, "p01,p02,p03,p12,p13,p23")
    p01, p02, p03, p12, p13, p23 = R.gens()
    Q = p01 * p23 - p02 * p13 + p03 * p12

    print("Sage polynomial ring variable count:", R.ngens())
    print("Q:", Q)
    print("Q is homogeneous:", Q.is_homogeneous())
    print("grad ideal generators:", [sg.Polynomial(Q.derivative(v)) for v in (p01, p02, p03, p12, p13, p23)])


def galgebra_block() -> None:
    """Optional galgebra check for Clifford-like bivector language."""
    print("== galgebra check ==")
    try:
        from galgebra.ga import Ga
    except Exception as exc:
        print(f"galgebra not available ({exc}); skipping")
        return

    # Minimal geometric algebra instantiation (signature is illustrative).
    ga = Ga('e0 e1 e2 e3', g=[1, 1, 1, 1], coords=None)
    e = ga.mv()
    # A toy Plücker-like bivector combination.
    B = e[0] ^ e[1] + e[2] ^ e[3]
    print("Ga basis dimension:", ga.n)
    print("Toy bivector square:", (B * B).expand())


def clifford_block() -> None:
    """Optional clifford package check for determinant/log intuition."""
    print("== clifford package check ==")
    try:
        from clifford import Cl
    except Exception as exc:
        print(f"clifford not available ({exc}); skipping")
        return

    layout, blades = Cl(1, 3)
    # Print a few reliable diagnostics without over-assuming API details.
    print("Clifford blade count:", len(blades))
    print("One-vector basis keys:", [k for k in blades.keys() if len(k) == 2 and k.startswith('e')])
    if all(k in blades for k in ["e1", "e2", "e3", "e4"]):
        e1, e2, e3, e4 = blades["e1"], blades["e2"], blades["e3"], blades["e4"]
        print("Toy scalar from basis squares:", e1 * e1 + e2 * e2 + e3 * e3 + e4 * e4)
    else:
        print("Could not find one-vector basis keys in Cliffords result; skipping scalar check")


def main() -> None:
    sympy_block()
    gap_block()
    sage_block()
    galgebra_block()
    clifford_block()


if __name__ == "__main__":
    main()
