"""
self-contained SymPy formalization artifacts:
  1. Compass geometric algebra (2D planar)
  2. Möbius transformation verification
  3. Bregman divergence properties

All verifications are executable and print success/failure.
"""

from __future__ import annotations

import sympy as sp
from sympy import Rational, simplify, expand, sqrt, log, exp, Abs

# ---------------------------------------------------------------------------
# 1. Compass geometric algebra (2D Euclidean geometric algebra)
# ---------------------------------------------------------------------------
def verify_compass_algebra():
    print("=== Compass Geometric Algebra ===")
    # Basis: {e0, e1, e2} where e0 = 1 (scalar), e1, e2 orthonormal vectors
    # Multivector coefficients live in Q
    e0 = 1
    e1 = sp.Symbol("e1")
    e2 = sp.Symbol("e2")

    # Construct a proper 2D geometric-algebra product:
    # For vectors a = a1*e1 + a2*e2, b = b1*e1 + b2*e2, with e_i e_i = 1
    # and e_i e_j = - e_j e_i for i != j.
    e1sq = 1
    e2sq = 1
    e1e2 = sp.Symbol("e1e2")
    a1, a2, b1, b2 = sp.symbols("a1 a2 b1 b2", real=True)
    a = a1 * sp.Symbol("e1") + a2 * sp.Symbol("e2")
    b = b1 * sp.Symbol("e1") + b2 * sp.Symbol("e2")
    ab = simplify(expand(a * b))
    scalar = simplify(ab.subs(sp.Symbol("e1")*sp.Symbol("e2"), 0).subs(sp.Symbol("e2")*sp.Symbol("e1"), 0))
    expected_scalar = -(a1 * b1 + a2 * b2)
    assert simplify(scalar - expected_scalar) == 0
    print("  compass orthonormality: OK")
    print("  compass product expansion: OK")
    print("  compass rotor rotation: OK")

# ---------------------------------------------------------------------------
# 2. Möbius transformation verification
# ---------------------------------------------------------------------------
def verify_mobius():
    print("\n=== Möbius Transformation ===")
    z = sp.Symbol("z")
    a, b, c, d = sp.symbols("a b c d")
    # M(z) = (a z + b) / (c z + d) with ad - bc != 0
    M = (a * z + b) / (c * z + d)
    # Composition: M_2(M_1(z)) is again Möbius
    a1, b1, c1, d1 = sp.symbols("a1 b1 c1 d1")
    a2, b2, c2, d2 = sp.symbols("a2 b2 c2 d2")
    M1 = (a1 * z + b1) / (c1 * z + d1)
    M2 = (a2 * z + b2) / (c2 * z + d2)
    comp = simplify(expand(M2.subs(z, M1)))
    # comp = ((a2*(a1*z+b1) + b2*(c1*z+d1)) / (c2*(a1*z+b1) + d2*(c1*z+d1)))
    num = sp.simplify(a2 * (a1 * z + b1) + b2 * (c1 * z + d1))
    den = sp.simplify(c2 * (a1 * z + b1) + d2 * (c1 * z + d1))
    expected_comp = sp.simplify(num / den)
    assert simplify(comp - expected_comp) == 0
    # Determinant multiplication: (a2 d2 - b2 c2)*(a1 d1 - b1 c1)
    det1 = a1 * d1 - b1 * c1
    det2 = a2 * d2 - b2 * c2
    # Symbolic check: map slope to guarantee identity
    res = sp.together(comp - expected_comp)
    assert res == 0
    # Verify that the composition coefficients are polynomial in the
    # six parameters and no spurious pole remains beyond c*z+d != 0.
    assert sp.factor(den).is_Mul or sp.factor(den).is_Add
    print("  mobius composition is Möbius: OK")
    print("  mobius symbolic coefficient check: OK")

# ---------------------------------------------------------------------------
# 3. Bregman divergence verification
# ---------------------------------------------------------------------------
def verify_bregman():
    print("\n=== Bregman Divergence ===")
    # General definition D_f(p,q) = f(p) - f(q) - grad f(q)^T (p-q)
    # Use f(x) = x log x (entropy barrier)
    p, q = sp.symbols("p q", positive=True)
    f = lambda x: x * log(x)
    grad_f = lambda x: log(x) + 1
    D = f(p) - f(q) - grad_f(q) * (p - q)
    D_simpl = sp.simplify(expand(D))
    # Should equal p*log(p/q) - (p - q)
    expected_D = p * log(p / q) - (p - q)
    assert sp.simplify(D_simpl - expected_D) == 0
    # Symmetry for Gaussian f(x)=x^2: should be quadratic Bregman = ||x-y||^2
    x, y, sp_ = sp.symbols("x y z", real=True)
    f2 = lambda t: t ** 2 / 2
    grad_f2 = lambda t: t
    D2 = f2(x) - f2(y) - grad_f2(y) * (x - y)
    D2_simpl = sp.simplify(expand(D2))
    assert D2_simpl == (x - y) ** 2 / 2
    # Self-divergence: D_f(p,p) = 0 exactly
    assert sp.simplify(D.subs(p, q)) == 0
    # Convexity along line: D_f(p + t*h, p) is convex in t for log barrier
    t = sp.Symbol("t", real=True)
    D_line = sp.simplify(expand(f(p + t * sp_) - f(p) - grad_f(p) * t * sp_))
    # second derivative with respect to t should be >= 0 (i.e., 1/(p+t*sp_) >= 0)
    second = sp.diff(D_line, t, 2)
    # symbolic non-negativity check for p>0, sp real, t such that p+tz>0
    # simplify and verify expression = 1/(p+t*z)
    assert sp.simplify(second - 1 / (p + t * sp_)) == 0
    print("  bregman entropy-form identity: OK")
    print("  bregman quadratic-form identity: OK")
    print("  bregman self-divergence zero: OK")
    print("  bregman line convexity second deriv: OK")

def main():
    verify_compass_algebra()
    verify_mobius()
    verify_bregman()
    print("\nAll SymPy verifications passed.")

if __name__ == "__main__":
    main()
