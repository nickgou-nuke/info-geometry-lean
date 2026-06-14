#!/usr/bin/env sage -python
"""Sage exact witnesses for raw Klein split-complex spinor stabilizers."""
from sage.all import QQ, PolynomialRing

R = PolynomialRing(QQ, names=("r", "s", "x", "y", "u", "v"))
r, s, x, y, u, v = R.gens()

# Split complex pair arithmetic over QQ-polynomial ring.
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def neg(a): return (-a[0], -a[1])
def sub(a, b): return add(a, neg(b))
def mul(a, b): return (a[0]*b[0] + a[1]*b[1], a[0]*b[1] + a[1]*b[0])
def qsmul(t, a): return (t*a[0], t*a[1])

ZERO = (R(0), R(0))
ONE = (R(1), R(0))
E = (R(1), R(1))
EBAR = (R(1), R(-1))

def det(M):
    aa, ab, ba, bb = M
    return sub(mul(aa, bb), mul(ab, ba))

def act(M, psi):
    aa, ab, ba, bb = M
    p, n = psi
    return (add(mul(aa, p), mul(ab, n)), add(mul(ba, p), mul(bb, n)))

assert mul(E, EBAR) == ZERO
b = (x, y)
Mgen = (ONE, b, ZERO, ONE)
assert det(Mgen) == ONE
assert act(Mgen, (ONE, ZERO)) == (ONE, ZERO)

# Eq. 5.22 strengthened shape: if a generic stabilizer has first column (1,0),
# its determinant is the lower-right entry, so determinant one forces unipotent form.
d = (u, v)
Mgen_shape = (ONE, b, ZERO, d)
assert det(Mgen_shape) == d
assert sub(det(Mgen_shape), ONE) == sub(d, ONE)

# Eq. 5.23-style determinant-one lower Ebar family used by the Lean CsSL2 bundle.
Mnull_det_one = (ONE, ZERO, qsmul(s, EBAR), ONE)
assert det(Mnull_det_one) == ONE
assert act(Mnull_det_one, (E, ZERO)) == (E, ZERO)

# More general raw null-stabilizer equations: aa*E=E and ba*E=0.
Mnull = (add(ONE, qsmul(r, EBAR)), b, qsmul(s, EBAR), (u, v))
assert act(Mnull, (E, ZERO)) == (E, ZERO)
assert Mnull[0][0] + Mnull[0][1] == 1
assert Mnull[2][0] + Mnull[2][1] == 0
# Eq. 5.23 scalar criterion: z*E is controlled exactly by z.re + z.im.
assert sub(mul(Mnull[0], E), E) == qsmul(Mnull[0][0] + Mnull[0][1] - 1, E)
assert mul(Mnull[2], E) == qsmul(Mnull[2][0] + Mnull[2][1], E)
# Eq. 5.23 first-column shape: these scalar equations are exactly Ebar-line forms.
r_param = Mnull[0][0] - 1
s_param = Mnull[2][0]
assert Mnull[0] == add(ONE, qsmul(r_param, EBAR))
assert Mnull[2] == qsmul(s_param, EBAR)

# Eq. 5.24-style diagonal-null row-sum criterion for (E,E).
aa, ab, ba, bb = (r, s), (x, y), (u, v), (R.gen(0) + R.gen(2), R.gen(1) - R.gen(3))
Mdiag = (aa, ab, ba, bb)
out = act(Mdiag, (E, E))
row1 = aa[0] + aa[1] + ab[0] + ab[1]
row2 = ba[0] + ba[1] + bb[0] + bb[1]
assert sub(out[0], E) == qsmul(row1 - 1, E)
assert sub(out[1], E) == qsmul(row2 - 1, E)

print("SAGE_KLEIN_SPINOR_E_ZERO_DIVISOR_OK")
print("SAGE_KLEIN_SPINOR_GENERIC_UNIPOTENT_DET_ONE_OK")
print("SAGE_KLEIN_SPINOR_GENERIC_STABILIZER_SHAPE_OK")
print("SAGE_KLEIN_SPINOR_NULL_E_SCALAR_CONDITIONS_OK")
print("SAGE_KLEIN_SPINOR_NULL_FIRST_COLUMN_EBAR_SHAPE_OK")
print("SAGE_KLEIN_SPINOR_NULL_EBAR_FAMILY_DET_ONE_OK")
print("SAGE_KLEIN_SPINOR_NULL_EBAR_FAMILY_STABILIZES_OK")
print("SAGE_KLEIN_SPINOR_DIAGONAL_NULL_ROW_CONDITION_OK")
