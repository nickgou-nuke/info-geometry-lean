import sympy as sp

Q = sp.Rational

def mirror_asymmetry_ratio(eps):
    return sp.factor(((1 + eps) / (1 - eps)) ** 2)

uniform_one_body = Q(752, 1000)
uniform_two_body = Q(410, 1000)
uniform_eta = sp.factor((uniform_one_body - uniform_two_body) / uniform_one_body)
assert uniform_eta == Q(171, 376)
assert Q(45, 100) < uniform_eta < Q(46, 100)

woods_saxon_eta = Q(445, 1000)
assert Q(44, 100) < woods_saxon_eta < Q(45, 100)

eps_uniform_A1_negligible = -Q(872, 10000)
eps_uniform_A0_negligible = Q(120, 1000)
eps_ws_A1_negligible = -Q(852, 10000)
eps_ws_A0_negligible = Q(116, 1000)

R_uniform_A1_negligible = mirror_asymmetry_ratio(eps_uniform_A1_negligible)
R_uniform_A0_negligible = mirror_asymmetry_ratio(eps_uniform_A0_negligible)
R_ws_A1_negligible = mirror_asymmetry_ratio(eps_ws_A1_negligible)
R_ws_A0_negligible = mirror_asymmetry_ratio(eps_ws_A0_negligible)

assert R_uniform_A1_negligible == Q(1301881, 1846881)
assert Q(70, 100) < R_uniform_A1_negligible < Q(71, 100)
assert R_uniform_A0_negligible == Q(196, 121)
assert Q(161, 100) < R_uniform_A0_negligible < Q(162, 100)
assert Q(70, 100) < R_ws_A1_negligible < Q(72, 100)
assert Q(158, 100) < R_ws_A0_negligible < Q(160, 100)

higher_order_upper_relative = Q(1, 1000)
assert higher_order_upper_relative == Q(1, 10) ** 3

pf_average_lower_shell = Q(615, 1000)
assert sp.factor(Q(2, 3) * pf_average_lower_shell) == Q(41, 100)

C, radial_num, radial_den, eta, A1, A0 = sp.symbols(
    "C radial_num radial_den eta A1 A0", nonzero=True
)
epsilon = sp.factor(
    3 * C * (radial_num / radial_den) * ((eta * A1 - A0) / (A1 + 3 * A0))
)
assert epsilon.subs({C: 1, radial_num: 1, radial_den: 1, eta: uniform_eta, A1: 1, A0: 0}) == 3 * uniform_eta

print({
    "uniform_eta": uniform_eta,
    "R_uniform_A1_negligible": R_uniform_A1_negligible,
    "R_uniform_A0_negligible": R_uniform_A0_negligible,
    "R_ws_A1_negligible": R_ws_A1_negligible,
    "R_ws_A0_negligible": R_ws_A0_negligible,
    "two_body_coefficient": Q(41, 100),
})
