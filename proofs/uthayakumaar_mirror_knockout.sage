Q = RationalField()

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
    return Q(61) / Q(100) - (Q(2) / Q(125)) * delta_s

deltaS_Ti47 = Q(1916) / Q(1000)
deltaS_Mn47 = Q(1442) / Q(100)
Rs_Ti47 = suppression_line(deltaS_Ti47)
Rs_Mn47 = suppression_line(deltaS_Mn47)
assert Rs_Ti47 == Q(72418) / Q(125000)
assert Rs_Mn47 == Q(4741) / Q(12500)
assert Rs_Mn47 < Rs_Ti47

E_Ti47_7half = Q(1594) / Q(10)
E_Mn47_7half = Q(1226) / Q(10)
assert med(E_Mn47_7half, E_Ti47_7half) == -Q(184) / Q(5)

BM1_ratio = Q(97) / Q(100)
assert abs(BM1_ratio - 1) <= Q(1) / Q(10)

R.<deltaS,Rs,dRs> = PolynomialRing(Q)
constraint = Rs - (Q(61) / Q(100) - (Q(2) / Q(125)) * deltaS)
assert constraint(deltaS=deltaS_Ti47, Rs=Rs_Ti47, dRs=0) == 0
assert constraint(deltaS=deltaS_Mn47, Rs=Rs_Mn47, dRs=0) == 0

print((Rs_Mn47, Rs_Ti47, med(E_Mn47_7half, E_Ti47_7half), BM1_ratio))
