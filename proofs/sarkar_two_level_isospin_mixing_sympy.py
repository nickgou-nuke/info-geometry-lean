import sympy as sp

Q = sp.Rational

def observed_gap(E1, E2):
    return E2 - E1

def H11(E1, E2, b2):
    return E1 + b2 * observed_gap(E1, E2)

def H22(E1, E2, b2):
    return E2 - b2 * observed_gap(E1, E2)

def unperturbed_gap(E1, E2, b2):
    return H22(E1, E2, b2) - H11(E1, E2, b2)

E1, E2, b2, gap, obs_gap, shell_gap, trace_defect, n = sp.symbols(
    "E1 E2 b2 gap obs_gap shell_gap trace_defect n", nonzero=True
)

assert sp.expand(H11(E1, E2, b2) + H22(E1, E2, b2) - (E1 + E2)) == 0
assert sp.expand(unperturbed_gap(E1, E2, b2) - (1 - 2 * b2) * observed_gap(E1, E2)) == 0

def b2_from_gap(gap0, obs_gap0):
    return sp.factor((1 - gap0 / obs_gap0) / 2)

assert sp.simplify((1 - 2 * b2_from_gap(gap, obs_gap)) * obs_gap - gap) == 0

def H12sq(E1, E2, b2):
    return sp.factor((b2 - b2**2) * observed_gap(E1, E2)**2)

assert sp.factor(H12sq(E1, E2, Q(1, 2)) - observed_gap(E1, E2)**2 / 4) == 0

def delta_bar(shell_gap0, trace_defect0, n0):
    return shell_gap0 + n0 * abs(trace_defect0)

def semi_empirical_b2(shell_gap0, obs_gap0, trace_defect0, n0):
    return sp.factor(((1 - shell_gap0 / obs_gap0) - n0 * abs(trace_defect0) / obs_gap0) / 2)

Mg24_E1 = Q(982811, 100)
Mg24_E2 = Q(996719, 100)
Mg24_shell_gap = Q(3)
Mg24_obs_gap = observed_gap(Mg24_E1, Mg24_E2)
Mg24_b2_gap = b2_from_gap(Mg24_shell_gap, Mg24_obs_gap)

assert Mg24_obs_gap == Q(3477, 25)
assert Mg24_b2_gap == Q(567, 1159)
assert Q(48, 100) < Mg24_b2_gap < Q(49, 100)
assert unperturbed_gap(Mg24_E1, Mg24_E2, Mg24_b2_gap) == Mg24_shell_gap

Mg24_b2_eff_fit = Q(3957, 10000)
Mg24_b2_free_fit = Q(2755, 10000)
assert Q(31, 100) < Mg24_b2_eff_fit < Q(49, 100)
assert Q(31, 100) < Mg24_b2_free_fit + Q(607, 10000) < Q(49, 100)

Co54_E1 = Q(265198, 100)
Co54_E2 = Q(285130, 100)
Co54_H11 = Q(265244, 100)
Co54_H22 = Q(285084, 100)
assert observed_gap(Co54_E1, Co54_E2) == Q(4983, 25)
assert Co54_H22 - Co54_H11 == Q(992, 5)

P30_bi2_percent = Q(4723, 1000)
S32_bf2_percent = Q(2688, 1000)
Cl34_bi2_percent = Q(237, 1000)
Ar36_bf2_percent = Q(2460, 1000)
assert S32_bf2_percent == Q(336, 125)
assert Ar36_bf2_percent == Q(123, 50)

print({
    "Mg24_obs_gap": Mg24_obs_gap,
    "Mg24_b2_gap": Mg24_b2_gap,
    "Mg24_unperturbed_gap": unperturbed_gap(Mg24_E1, Mg24_E2, Mg24_b2_gap),
    "Co54_gap": Co54_H22 - Co54_H11,
    "P30_bi2_percent": P30_bi2_percent,
})
