from sage.all import *

Q = QQ

def Tz(N, Z):
    return Q(N - Z) / 2

assert 2 * Tz(12, 11) == 1

mu = Q(219) / 100
md = Q(467) / 100
ms = Q(94)
assert md - mu == Q(62) / 25
assert (mu + md) / 2 == Q(343) / 100
assert (mu - md) / 2 == -Q(31) / 25
assert ms == 94

R = PolynomialRing(QQ, ["a", "b", "c", "d", "bc", "deltaNH", "cc", "asymCSB", "asymCIB", "A", "t"])
a, b, c, d, bc, deltaNH, cc, asymCSB, asymCIB, A, t = R.gens()

def IMME(a0, b0, c0, tz):
    return a0 + b0 * tz + c0 * tz**2

def cubic_IMME(a0, b0, c0, d0, tz):
    return IMME(a0, b0, c0, tz) + d0 * tz**3

assert IMME(a, b, c, t) - IMME(a, b, c, -t) == 2 * b * t
assert cubic_IMME(a, b, c, d, t) - cubic_IMME(a, b, c, d, -t) == 2 * b * t + 2 * d * t**3

def generalized_IMME(A0, a0, bc0, delta0, asym1, cc0, asym2, tz):
    return a0 + bc0 + delta0 + 2 * asym1 * tz + (cc0 + Q(4) / A0 * asym2) * tz**2

assert generalized_IMME(A, a, bc, deltaNH, 0, cc, 0, t) == IMME(a + bc + deltaNH, 0, cc, t)
assert Q(782) / 1000 == Q(391) / 500

def scattering_CIB(app, ann, anp):
    return (app + ann) / 2 - anp

def scattering_CSB(app, ann):
    return app - ann

assert scattering_CIB(0, 0, -Q(57) / 10) == Q(57) / 10
assert scattering_CSB(Q(3) / 4, -Q(3) / 4) == Q(3) / 2

assert Q(93957) / 100 - Q(93828) / 100 == Q(129) / 100
assert Q(280894) / 100 - Q(280842) / 100 == Q(13) / 25
assert Q(466787) / 100 - Q(466766) / 100 == Q(21) / 100
assert -133 - 0 == -133
assert 477 - 0 == 477
assert -1298 - 0 == -1298

print({
    "qcd_split": md - mu,
    "isoscalar": (mu + md) / 2,
    "isovector": (mu - md) / 2,
    "deltaNH": Q(391) / 500,
    "CIB_anchor": scattering_CIB(0, 0, -Q(57) / 10),
    "MED_26Si_4plus": 477,
})
