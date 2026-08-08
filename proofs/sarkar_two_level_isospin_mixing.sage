from sage.all import *

Q = QQ

def observed_gap(E1, E2):
    return E2 - E1

def H11(E1, E2, b2):
    return E1 + b2 * observed_gap(E1, E2)

def H22(E1, E2, b2):
    return E2 - b2 * observed_gap(E1, E2)

def unperturbed_gap(E1, E2, b2):
    return H22(E1, E2, b2) - H11(E1, E2, b2)

R = PolynomialRing(QQ, ["E1", "E2", "b2", "gap", "obs_gap"])
E1, E2, b2, gap, obs_gap = R.gens()

assert H11(E1, E2, b2) + H22(E1, E2, b2) == E1 + E2
assert unperturbed_gap(E1, E2, b2) == (1 - 2 * b2) * observed_gap(E1, E2)

def b2_from_gap(gap0, obs_gap0):
    return (1 - gap0 / obs_gap0) / 2

assert (1 - 2 * b2_from_gap(gap, obs_gap)) * obs_gap == gap

def H12sq(E1, E2, b2):
    return (b2 - b2**2) * observed_gap(E1, E2)**2

assert H12sq(E1, E2, Q(1) / 2) == observed_gap(E1, E2)**2 / 4

Mg24_E1 = Q(982811) / 100
Mg24_E2 = Q(996719) / 100
Mg24_shell_gap = Q(3)
Mg24_obs_gap = observed_gap(Mg24_E1, Mg24_E2)
Mg24_b2_gap = b2_from_gap(Mg24_shell_gap, Mg24_obs_gap)

assert Mg24_obs_gap == Q(3477) / 25
assert Mg24_b2_gap == Q(567) / 1159
assert Q(48) / 100 < Mg24_b2_gap < Q(49) / 100
assert unperturbed_gap(Mg24_E1, Mg24_E2, Mg24_b2_gap) == Mg24_shell_gap

Co54_H11 = Q(265244) / 100
Co54_H22 = Q(285084) / 100
assert Co54_H22 - Co54_H11 == Q(992) / 5

print({
    "Mg24_obs_gap": Mg24_obs_gap,
    "Mg24_b2_gap": Mg24_b2_gap,
    "Mg24_unperturbed_gap": unperturbed_gap(Mg24_E1, Mg24_E2, Mg24_b2_gap),
    "Co54_gap": Co54_H22 - Co54_H11,
})
