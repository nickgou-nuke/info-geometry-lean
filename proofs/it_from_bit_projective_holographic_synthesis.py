#!/usr/bin/env python3
"""SymPy witness for ItFromBitProjectiveHolographicSynthesis.lean.

Integrated audit of the finite kernels:
  * Pauli/quaternion paravector determinant = Minkowski interval;
  * rank-one spinor dyad is null;
  * Penrose incidence omega = i X pi;
  * R^(4,4) affine chart embeds into the null cone of R^(5,5);
  * O(5,5)-type coordinate reflections preserve Q55;
  * Hill--Wheeler det(H-E N) factorization;
  * CPT averaging projects to Re(s)=1/2;
  * UHF diagonal duplication preserves normalized reference averages.

Analytic CP3/Cantor, Pin(5,5), C*-GNS, and Hilbert--Polya claims are deferred_interfaces
in Lean, not asserted by this script.
"""

import sympy as sp

I = sp.I

# ---------------------------------------------------------------------------
# Pauli/quaternion paravectors and null rays.
# ---------------------------------------------------------------------------
t, x, y, z = sp.symbols("t x y z")
X = sp.Matrix([[t + z, x - I * y], [x + I * y, t - z]])
assert sp.simplify(X.det() - (t**2 - x**2 - y**2 - z**2)) == 0

a, b, c, d = sp.symbols("a b c d")
dyad = sp.Matrix([[a * c, a * d], [b * c, b * d]])
assert sp.simplify(dyad.det()) == 0

pi0, pi1 = sp.symbols("pi0 pi1")
pi = sp.Matrix([pi0, pi1])
omega = I * X * pi
assert sp.simplify(omega[0] - I * ((t + z) * pi0 + (x - I * y) * pi1)) == 0
assert sp.simplify(omega[1] - I * ((x + I * y) * pi0 + (t - z) * pi1)) == 0

# ---------------------------------------------------------------------------
# Projective affine conformal closure R^(4,4) -> Null(R^(5,5)).
# ---------------------------------------------------------------------------
x0, x1, x2, x3, y0, y1, y2, y3, u, v = sp.symbols(
    "x0 x1 x2 x3 y0 y1 y2 y3 u v", real=True
)
Q44 = x0**2 + x1**2 + x2**2 + x3**2 - (y0**2 + y1**2 + y2**2 + y3**2)
U = (1 - Q44) / 2
V = (1 + Q44) / 2
assert sp.expand(Q44 + U**2 - V**2) == 0

Q55 = x0**2 + x1**2 + x2**2 + x3**2 + u**2 - (y0**2 + y1**2 + y2**2 + y3**2 + v**2)
Q55_reflect_u = x0**2 + x1**2 + x2**2 + x3**2 + (-u)**2 - (y0**2 + y1**2 + y2**2 + y3**2 + v**2)
Q55_reflect_v = x0**2 + x1**2 + x2**2 + x3**2 + u**2 - (y0**2 + y1**2 + y2**2 + y3**2 + (-v)**2)
assert sp.expand(Q55_reflect_u - Q55) == 0
assert sp.expand(Q55_reflect_v - Q55) == 0

# ---------------------------------------------------------------------------
# Hill--Wheeler generalized eigenvalue / projection algebra.
# ---------------------------------------------------------------------------
E, h0, h1, n0, n1 = sp.symbols("E h0 h1 n0 n1")
H = sp.diag(h0, h1)
N = sp.diag(n0, n1)
assert sp.factor((H - E * N).det() - (h0 - E * n0) * (h1 - E * n1)) == 0

P0 = sp.Matrix([[1, 0], [0, 0]])
P1 = sp.Matrix([[0, 0], [0, 1]])
assert P0 * P0 == P0
assert P0 + P1 == sp.eye(2)

# CPT averaging is the Hill--Wheeler-style projection onto the fixed line.
sigma, tau = sp.symbols("sigma tau", real=True)
s = sigma + I * tau
cpt = 1 - sp.conjugate(s)
avg = sp.simplify((s + cpt) / 2)
assert sp.simplify(sp.re(avg) - sp.Rational(1, 2)) == 0
assert sp.simplify(1 - sp.conjugate(avg) - avg) == 0

# UHF/Cantor finite cut: duplicate cells, normalized reference average unchanged.
def diag_embed(vals):
    out = []
    for val in vals:
        out.extend([val, val])
    return out

vals = [sp.symbols(f"a{i}") for i in range(4)]
emb = diag_embed(vals)
assert sp.simplify(sum(emb) / len(emb) - sum(vals) / len(vals)) == 0

print("it_from_bit_projective_holographic_synthesis.py: all witnesses passed")
