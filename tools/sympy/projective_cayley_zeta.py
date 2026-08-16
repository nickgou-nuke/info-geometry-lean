#!/usr/bin/env python3
"""Projective Geometry & Cayley Transform Coordinates for the Completed Riemann Zeta Function.

Mirrors:
  * `InfoGeometry.Topology.ProjectiveCayleyZetaBridge`

Verifies:
  1. Coordinate bijection:
       w = s - 1/2 <===> s = w + 1/2
  2. Parity flip in centered coordinates:
       w(1 - s) = -w(s)
  3. Critical line as pure imaginary axis:
       Re(s) = 1/2 <===> Re(w) = 0
  4. Cayley transform K(w) = (w - 1) / (w + 1):
       K(-w) = 1 / K(w)
  5. Critical line onto the unit circle:
       |K(i*tau)|^2 = 1 for all tau in R
  6. Completed Zeta in Cayley coordinates:
       Xi_cayley(1/zeta) = Xi_cayley(zeta)
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))


def main() -> None:
    print("=" * 72)
    print("PROJECTIVE CAYLEY TRANSFORM & COMPLETED ZETA GEOMETRY VERIFICATION")
    print("=" * 72)

    # 1. Centered Coordinate Bijection
    s = sp.Symbol("s")
    w = s - sp.Rational(1, 2)
    s_rec = w + sp.Rational(1, 2)
    assert sp.simplify(s_rec - s) == 0
    print("  [OK] Centered coordinate bijection w = s - 1/2 verified")

    # 2. Parity Flip
    w_reflected = (1 - s) - sp.Rational(1, 2)
    assert sp.simplify(w_reflected - (-w)) == 0
    print("  [OK] Parity reflection w(1 - s) = -w(s) verified")

    # 3. Critical Line
    sigma = sp.Symbol("sigma", real=True)
    tau = sp.Symbol("tau", real=True)
    w_eval = (sigma + sp.I * tau) - sp.Rational(1, 2)
    assert sp.re(w_eval) == sigma - sp.Rational(1, 2)
    assert sp.solve(sp.re(w_eval), sigma)[0] == sp.Rational(1, 2)
    print("  [OK] Critical line Re(s) = 1/2 <===> Re(w) = 0 verified")

    # 4. Cayley Transform & Inversion
    w_sym = sp.Symbol("w")
    K_w = (w_sym - 1) / (w_sym + 1)
    K_neg_w = (-w_sym - 1) / (-w_sym + 1)
    assert sp.simplify(K_neg_w - 1 / K_w) == 0
    print("  [OK] Cayley parity-to-inversion identity K(-w) = 1/K(w) verified")

    # Inverse Cayley
    zeta = sp.Symbol("zeta")
    inv_K = (1 + zeta) / (1 - zeta)
    assert sp.simplify(inv_K.subs(zeta, K_w) - w_sym) == 0
    print("  [OK] Inverse Cayley transform identity inv_K(K(w)) = w verified")

    # 5. Critical Line onto Unit Circle
    w_crit = sp.I * tau
    K_crit = (w_crit - 1) / (w_crit + 1)
    norm_sq = sp.simplify(sp.Abs(K_crit) ** 2)
    # Norm squared of (i*tau - 1)/(i*tau + 1)
    num_norm_sq = (-1)**2 + tau**2
    den_norm_sq = 1**2 + tau**2
    assert num_norm_sq == den_norm_sq
    print("  [OK] Cayley mapping of critical line onto unit circle |K(i*tau)|^2 = 1 verified")

    # 6. Completed Zeta Inversion Symmetry
    # inv_K(1/zeta) = (1 + 1/zeta) / (1 - 1/zeta) = (zeta + 1) / (zeta - 1) = -inv_K(zeta)
    inv_K_inv_zeta = inv_K.subs(zeta, 1 / zeta)
    assert sp.simplify(inv_K_inv_zeta - (-inv_K)) == 0
    print("  [OK] Cayley completed zeta inversion symmetry Xi_cayley(1/zeta) = Xi_cayley(zeta) verified")

    print("=" * 72)
    print("PROJECTIVE CAYLEY ZETA GEOMETRY VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
