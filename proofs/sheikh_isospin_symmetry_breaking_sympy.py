import sympy as sp

Q = sp.Rational

def two_Tz(N, Z):
    return N - Z

def Tz(N, Z):
    return Q(N - Z, 2)

mu = Q(219, 100)
md = Q(467, 100)
ms = Q(94, 1)

isoscalar = sp.factor((mu + md) / 2)
isovector = sp.factor((mu - md) / 2)

assert md - mu == Q(62, 25)
assert isoscalar == Q(343, 100)
assert isovector == -Q(31, 25)
assert isoscalar + isovector == mu
assert isoscalar - isovector == md
assert ms == 94

tz_n = Q(1, 2)
tz_p = -Q(1, 2)

def class_I(a, b, tau_dot):
    return sp.factor(a + b * tau_dot)

def class_II(c, tau3_i, tau3_j, tau_dot):
    return sp.factor(c * (tau3_i * tau3_j - tau_dot / 3))

def class_III(d, tau3_i, tau3_j):
    return sp.factor(d * (tau3_i + tau3_j))

d = sp.symbols("d")
assert class_III(d, tz_n, tz_p) == 0
assert sp.factor(class_III(d, tz_n, tz_n) + class_III(d, tz_p, tz_p)) == 0

a, b, c, t = sp.symbols("a b c t")

def IMME(a0, b0, c0, tz):
    return sp.factor(a0 + b0 * tz + c0 * tz**2)

assert sp.factor(IMME(a, b, c, t) - IMME(a, b, c, -t)) == 2 * b * t
assert sp.simplify(IMME(a, b, c, t) + IMME(a, b, c, -t) - (2 * a + 2 * c * t**2)) == 0

splits = {
    "n-p": (Q(93957, 100), Q(93828, 100), Q(129, 100)),
    "3H-3He": (Q(280894, 100), Q(280842, 100), Q(13, 25)),
    "5He-5Li": (Q(466787, 100), Q(466766, 100), Q(21, 100)),
    "7Li-7Be": (Q(653389, 100), Q(653424, 100), -Q(7, 20)),
}

for left, right, diff in splits.values():
    assert left - right == diff

print({
    "two_Tz_16_16": two_Tz(16, 16),
    "qcd_isoscalar": isoscalar,
    "qcd_isovector": isovector,
    "classIII_np": class_III(Q(7), tz_n, tz_p),
    "IMME_mirror_difference": sp.factor(IMME(a, b, c, t) - IMME(a, b, c, -t)),
    "table_splits": {name: diff for name, (_, _, diff) in splits.items()},
})
