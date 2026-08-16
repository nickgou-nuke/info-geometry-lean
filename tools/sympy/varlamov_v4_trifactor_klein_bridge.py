#!/usr/bin/env python3
"""Finite Varlamov V4 / trifactor / Klein-glide bridge witness.

This script is an assertion-backed computational companion for
`Topology/VarlamovV4TrifactorKleinBridge.lean`.

It checks only finite algebra:
  * three tripotent branches cycle with order three;
  * the branches label the three non-identity elements of V4;
  * each labelled V4 element is an involution;
  * the concrete pg glide G(x,y)=(x+1/2,-y) satisfies
    G T_y G^{-1} = T_y^{-1} pointwise.

No Clifford classification, quotient-manifold classification, or physical
triality theorem is asserted.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def verify_varlamov_v4_trifactor_klein_bridge() -> None:
    # V4 sign-reflection matrices.
    I = sp.eye(2)
    W1 = sp.diag(-1, 1)
    W2 = sp.diag(1, -1)
    W12 = W1 * W2
    v4 = {"W1": W1, "W2": W2, "W12": W12}

    # Tripotent branches and the aligned triality-shaped cycle.
    sector_label = {-1: "W1", 0: "W2", 1: "W12"}
    trip_cycle = {-1: 0, 0: 1, 1: -1}
    v4_cycle = {"W1": "W2", "W2": "W12", "W12": "W1"}

    for s in (-1, 0, 1):
        assert s**3 == s
        assert trip_cycle[trip_cycle[trip_cycle[s]]] == s
        assert sector_label[trip_cycle[s]] == v4_cycle[sector_label[s]]
        g = v4[sector_label[s]]
        assert_matrix_eq(f"sector {s} involution", g * g, I)
        assert g != I

    # Trifactor diagonal projectors for OP=diag(-1,0,+1) in branch order.
    OP = sp.diag(-1, 0, 1)
    P_neg = (OP**2 - OP) / 2
    P_zero = sp.eye(3) - OP**2
    P_pos = (OP**2 + OP) / 2
    assert_matrix_eq("OP^3=OP", OP**3, OP)
    assert_matrix_eq("partition", P_neg + P_zero + P_pos, sp.eye(3))
    for P in (P_neg, P_zero, P_pos):
        assert_matrix_eq("projector idempotent", P * P, P)
    for A, B in ((P_neg, P_zero), (P_neg, P_pos), (P_zero, P_pos)):
        assert_matrix_eq("projector orthogonal", A * B, sp.zeros(3))

    # Concrete pg action: Tx(x,y)=(x+1,y), Ty(x,y)=(x,y+1), G(x,y)=(x+1/2,-y).
    x, y = sp.symbols("x y")

    def Ty(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (p[0], p[1] + 1)

    def Ty_inv(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (p[0], p[1] - 1)

    def G(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (p[0] + sp.Rational(1, 2), -p[1])

    def G_inv(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (p[0] - sp.Rational(1, 2), -p[1])

    p = (x, y)
    lhs = G(Ty(G_inv(p)))
    rhs = Ty_inv(p)
    assert tuple(sp.simplify(a - b) for a, b in zip(lhs, rhs)) == (0, 0)

    print("VARLAMOV_V4_TRIFACTOR_KLEIN_BRIDGE_OK")
    print("scope: finite V4/tripotent cycle plus pointwise pg glide relation only")


if __name__ == "__main__":
    verify_varlamov_v4_trifactor_klein_bridge()
