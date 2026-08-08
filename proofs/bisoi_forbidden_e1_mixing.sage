Q = RationalField()

def equal_mixing_amplitude(Mexp, M01, M10):
    return Mexp / (M01 + M10)

def mixing_probability(Mexp, M01, M10):
    return equal_mixing_amplitude(Mexp, M01, M10)^2

nuclei = {
    "30P": (30, 15, 15, Q(138)/Q(10000), -Q(228)/Q(10000), Q(801)/Q(10000)),
    "32S": (32, 16, 16, Q(162)/Q(10000), Q(1086)/Q(10000), -Q(127)/Q(10000)),
    "34Cl": (34, 17, 17, Q(160)/Q(100000), Q(819)/Q(100000), Q(2533)/Q(100000)),
    "36Ar": (36, 18, 18, Q(38)/Q(10000), -Q(144)/Q(10000), -Q(233)/Q(10000)),
}

out = {}
for name, (A, Z, N, Mexp, M01, M10) in nuclei.items():
    assert Z == N
    b = equal_mixing_amplitude(Mexp, M01, M10)
    b2 = mixing_probability(Mexp, M01, M10)
    assert b * (M01 + M10) == Mexp
    out[name] = (b, b2, 100*b2)

assert out["30P"][1] == Q(2116)/Q(36481)
assert out["32S"][1] == Q(26244)/Q(919681)
assert out["34Cl"][1] == Q(400)/Q(175561)
assert out["36Ar"][1] == Q(1444)/Q(142129)

R.<Mexp,M01,M10,b> = PolynomialRing(Q)
constraint = b * (M01 + M10) - Mexp
assert constraint(Mexp=Q(138)/Q(10000), M01=-Q(228)/Q(10000), M10=Q(801)/Q(10000), b=out["30P"][0]) == 0

print(out)
