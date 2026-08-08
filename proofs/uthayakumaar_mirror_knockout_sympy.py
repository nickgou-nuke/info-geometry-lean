import sympy as sp

Q = sp.Rational

Mn47 = {"A": 47, "Z": 25, "N": 22}
Ti47 = {"A": 47, "Z": 22, "N": 25}
Cr45 = {"A": 45, "Z": 24, "N": 21}
Sc45 = {"A": 45, "Z": 21, "N": 24}

def two_tz(x):
    return x["N"] - x["Z"]

def mirror_pair(x, y):
    return x["A"] == y["A"] and x["Z"] == y["N"] and x["N"] == y["Z"]

assert mirror_pair(Mn47, Ti47)
assert mirror_pair(Cr45, Sc45)
assert two_tz(Mn47) == -3 and two_tz(Ti47) == 3
assert two_tz(Cr45) == -3 and two_tz(Sc45) == 3

def med(e_proton_rich, e_neutron_rich):
    return e_proton_rich - e_neutron_rich

def suppression_line(delta_s):
    return Q(61, 100) - Q(2, 125) * delta_s

deltaS_Ti47 = Q(1916, 1000)
deltaS_Mn47 = Q(1442, 100)
Rs_Ti47 = sp.factor(suppression_line(deltaS_Ti47))
Rs_Mn47 = sp.factor(suppression_line(deltaS_Mn47))
assert Rs_Ti47 == Q(72418, 125000)
assert Rs_Mn47 == Q(4741, 12500)
assert Rs_Mn47 < Rs_Ti47

tau_Ti47 = Q(331)
tau_Mn47 = Q(687)
assert tau_Ti47 < tau_Mn47

E_Ti47_7half = Q(1594, 10)
E_Mn47_7half = Q(1226, 10)
assert med(E_Mn47_7half, E_Ti47_7half) == -Q(184, 5)

BM1_Ti47 = Q(445, 10000)
BM1_ratio = Q(97, 100)
assert abs(BM1_ratio - 1) <= Q(1, 10)
assert Q(89, 100) <= BM1_ratio <= Q(105, 100)

inclusive_asymmetry_factor = Q(11)
assert inclusive_asymmetry_factor > 10
assert Q(1067, 1000) > 1

print({
    "twoTz": (two_tz(Mn47), two_tz(Ti47), two_tz(Cr45), two_tz(Sc45)),
    "Rs": (Rs_Mn47, Rs_Ti47),
    "MED_7half_keV": med(E_Mn47_7half, E_Ti47_7half),
    "tau_ps": (tau_Ti47, tau_Mn47),
    "BM1_ratio": BM1_ratio,
})
