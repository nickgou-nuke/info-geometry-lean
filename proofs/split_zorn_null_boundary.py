#!/usr/bin/env python3
"""
Symbolic witness for the finite split Zorn null-boundary spine.

This verifies the exact polynomial identities mirrored in Lean:
- detZ(X * Y) = detZ(X) detZ(Y) for concrete Zorn cells;
- a nonzero top-right generator n has detZ(n)=0;
- n*n=0;
- null factors absorb products into the null cone.

No analytic, GNS, exceptional-group, or Cantor-colimit closure theorem is
claimed here.
"""

import sympy as sp


def detZ(Z):
    r, s, x1, x2, x3, y1, y2, y3 = Z
    return sp.expand(r * s - (x1 * y1 + x2 * y2 + x3 * y3))


def mulZ(X, Y):
    r, s, x1, x2, x3, y1, y2, y3 = X
    R, S, u1, u2, u3, v1, v2, v3 = Y
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


xs = sp.symbols("r s x1 x2 x3 y1 y2 y3")
ys = sp.symbols("R S u1 u2 u3 v1 v2 v3")
X = xs
Y = ys

composition = sp.expand(detZ(mulZ(X, Y)) - detZ(X) * detZ(Y))
assert sp.simplify(composition) == 0

n = (0, 0, 1, 0, 0, 0, 0, 0)
z = (0, 0, 0, 0, 0, 0, 0, 0)
assert detZ(n) == 0
assert n != z
assert mulZ(n, n) == z
assert detZ(mulZ(n, Y)) == 0

print("split_zorn_null_boundary: symbolic checks passed")
