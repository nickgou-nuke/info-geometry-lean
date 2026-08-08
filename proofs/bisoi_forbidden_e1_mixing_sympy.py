import sympy as sp

Q = sp.Rational

nuclei = {
    "30P": {"A": 30, "Z": 15, "N": 15, "Mexp": Q(138, 10000), "M01": -Q(228, 10000), "M10": Q(801, 10000)},
    "32S": {"A": 32, "Z": 16, "N": 16, "Mexp": Q(162, 10000), "M01": Q(1086, 10000), "M10": -Q(127, 10000)},
    "34Cl": {"A": 34, "Z": 17, "N": 17, "Mexp": Q(160, 100000), "M01": Q(819, 100000), "M10": Q(2533, 100000)},
    "36Ar": {"A": 36, "Z": 18, "N": 18, "Mexp": Q(38, 10000), "M01": -Q(144, 10000), "M10": -Q(233, 10000)},
}

def equal_mixing_amplitude(Mexp, M01, M10):
    return sp.factor(Mexp / (M01 + M10))

def mixing_probability(Mexp, M01, M10):
    return sp.factor(equal_mixing_amplitude(Mexp, M01, M10) ** 2)

out = {}
for name, d in nuclei.items():
    assert d["Z"] == d["N"]
    b = equal_mixing_amplitude(d["Mexp"], d["M01"], d["M10"])
    b2 = mixing_probability(d["Mexp"], d["M01"], d["M10"])
    assert sp.factor(b * (d["M01"] + d["M10"]) - d["Mexp"]) == 0
    out[name] = {"b": b, "b2": b2, "percent": sp.factor(100 * b2)}

assert out["30P"]["b2"] == Q(2116, 36481)
assert out["32S"]["b2"] == Q(26244, 919681)
assert out["34Cl"]["b2"] == Q(400, 175561)
assert out["36Ar"]["b2"] == Q(1444, 142129)

assert Q(57, 10) < out["30P"]["percent"] < Q(59, 10)
assert Q(28, 10) < out["32S"]["percent"] < Q(29, 10)
assert Q(22, 100) < out["34Cl"]["percent"] < Q(24, 100)
assert Q(100, 100) < out["36Ar"]["percent"] < Q(102, 100)

print(out)
