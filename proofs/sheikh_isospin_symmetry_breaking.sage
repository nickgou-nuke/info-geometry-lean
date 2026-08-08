from sage.all import *

Q = QQ

def two_Tz(N, Z):
    return ZZ(N) - ZZ(Z)

def Tz(N, Z):
    return Q(N - Z) / 2

mu = Q(219) / 100
md = Q(467) / 100
ms = Q(94)

isoscalar = (mu + md) / 2
isovector = (mu - md) / 2

assert md - mu == Q(62) / 25
assert isoscalar == Q(343) / 100
assert isovector == -Q(31) / 25
assert isoscalar + isovector == mu
assert isoscalar - isovector == md
assert ms == 94

tz_n = Q(1) / 2
tz_p = -Q(1) / 2

def henley_class_I(a, b, tau_dot):
    return a + b * tau_dot

def henley_class_II(c, tau3_i, tau3_j, tau_dot):
    return c * (tau3_i * tau3_j - tau_dot / 3)

def henley_class_III(d, tau3_i, tau3_j):
    return d * (tau3_i + tau3_j)

R = PolynomialRing(QQ, ["a", "b", "c", "d", "t"])
a, b, c, d, t = R.gens()

assert henley_class_III(d, R(tz_n), R(tz_p)) == 0
assert henley_class_III(d, R(tz_n), R(tz_n)) + henley_class_III(d, R(tz_p), R(tz_p)) == 0

def IMME(a0, b0, c0, tz):
    return a0 + b0 * tz + c0 * tz**2

assert IMME(a, b, c, t) - IMME(a, b, c, -t) == 2 * b * t
assert IMME(a, b, c, t) + IMME(a, b, c, -t) == 2 * a + 2 * c * t**2

splits = {
    "n-p": (Q(93957) / 100, Q(93828) / 100, Q(129) / 100),
    "3H-3He": (Q(280894) / 100, Q(280842) / 100, Q(13) / 25),
    "5He-5Li": (Q(466787) / 100, Q(466766) / 100, Q(21) / 100),
    "7Li-7Be": (Q(653389) / 100, Q(653424) / 100, -Q(7) / 20),
}

for left, right, diff in splits.values():
    assert left - right == diff

print({
    "two_Tz_16_16": two_Tz(16, 16),
    "qcd_isoscalar": isoscalar,
    "qcd_isovector": isovector,
    "classIII_np": henley_class_III(Q(7), tz_n, tz_p),
    "IMME_mirror_difference": IMME(a, b, c, t) - IMME(a, b, c, -t),
    "table_splits": {name: diff for name, (_, _, diff) in splits.items()},
})
