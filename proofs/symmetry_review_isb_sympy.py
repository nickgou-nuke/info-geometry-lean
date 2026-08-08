import sympy as sp

Q = sp.Rational

def Tz(N, Z):
    return (N - Z) / 2

N, Z = sp.symbols("N Z")
assert sp.expand(2 * Tz(N, Z) - (N - Z)) == 0

mu = Q(219, 100)
md = Q(467, 100)
ms = Q(94)
isoscalar = (mu + md) / 2
isovector = (mu - md) / 2
assert md - mu == Q(62, 25)
assert isoscalar == Q(343, 100)
assert isovector == -Q(31, 25)
assert ms == 94

def class_III(d, tau3_i, tau3_j):
    return sp.factor(d * (tau3_i + tau3_j))

d = sp.symbols("d")
assert class_III(d, 1, -1) == 0
assert sp.factor(class_III(d, 1, 1) + class_III(d, -1, -1)) == 0

a, b, c, cc, bc, deltaNH, asymCSB, asymCIB, A, t, cubic = sp.symbols(
    "a b c cc bc deltaNH asymCSB asymCIB A t cubic", nonzero=True
)

def IMME(a0, b0, c0, tz):
    return sp.factor(a0 + b0 * tz + c0 * tz**2)

def cubic_IMME(a0, b0, c0, d0, tz):
    return sp.factor(IMME(a0, b0, c0, tz) + d0 * tz**3)

assert sp.factor(IMME(a, b, c, t) - IMME(a, b, c, -t)) == 2 * b * t
assert sp.simplify(cubic_IMME(a, b, c, cubic, t) - cubic_IMME(a, b, c, cubic, -t) - (2*b*t + 2*cubic*t**3)) == 0

def generalized_IMME(A0, a0, bc0, delta0, asym1, cc0, asym2, tz):
    return sp.factor(a0 + bc0 + delta0 + 2 * asym1 * tz + (cc0 + Q(4) / A0 * asym2) * tz**2)

assert sp.simplify(generalized_IMME(A, a, bc, deltaNH, 0, cc, 0, t) - IMME(a + bc + deltaNH, 0, cc, t)) == 0
assert Q(782, 1000) == Q(391, 500)

def scattering_CIB(app, ann, anp):
    return sp.factor((Q(app) + Q(ann)) / 2 - Q(anp))

def scattering_CSB(app, ann):
    return sp.factor(Q(app) - Q(ann))

assert scattering_CIB(0, 0, -Q(57, 10)) == Q(57, 10)
assert scattering_CSB(Q(3, 4), -Q(3, 4)) == Q(3, 2)

def mass_split(left, right):
    return left - right

assert mass_split(Q(93957, 100), Q(93828, 100)) == Q(129, 100)
assert mass_split(Q(280894, 100), Q(280842, 100)) == Q(13, 25)
assert mass_split(Q(466787, 100), Q(466766, 100)) == Q(21, 100)

def MED(Eminus, Eplus):
    return Eminus - Eplus

assert MED(-133, 0) == -133
assert MED(-175, 0) == -175
assert MED(-151, 0) == -151
assert MED(477, 0) == 477
assert MED(-1298, 0) == -1298

print({
    "qcd_split": md - mu,
    "isoscalar": isoscalar,
    "isovector": isovector,
    "deltaNH": Q(391, 500),
    "CIB_anchor": scattering_CIB(0, 0, -Q(57, 10)),
    "MED_26Si_4plus": MED(477, 0),
})
