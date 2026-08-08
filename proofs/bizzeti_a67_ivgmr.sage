Q = RationalField()

def mirror_asymmetry_ratio(eps):
    return ((1 + eps) / (1 - eps))^2

uniform_one_body = Q(752) / Q(1000)
uniform_two_body = Q(410) / Q(1000)
uniform_eta = (uniform_one_body - uniform_two_body) / uniform_one_body
assert uniform_eta == Q(171) / Q(376)
assert Q(45) / Q(100) < uniform_eta < Q(46) / Q(100)

woods_saxon_eta = Q(445) / Q(1000)
assert Q(44) / Q(100) < woods_saxon_eta < Q(45) / Q(100)

eps_uniform_A1_negligible = -Q(872) / Q(10000)
eps_uniform_A0_negligible = Q(120) / Q(1000)
eps_ws_A1_negligible = -Q(852) / Q(10000)
eps_ws_A0_negligible = Q(116) / Q(1000)

R_uniform_A1_negligible = mirror_asymmetry_ratio(eps_uniform_A1_negligible)
R_uniform_A0_negligible = mirror_asymmetry_ratio(eps_uniform_A0_negligible)
R_ws_A1_negligible = mirror_asymmetry_ratio(eps_ws_A1_negligible)
R_ws_A0_negligible = mirror_asymmetry_ratio(eps_ws_A0_negligible)

assert R_uniform_A1_negligible == Q(1301881) / Q(1846881)
assert Q(70) / Q(100) < R_uniform_A1_negligible < Q(71) / Q(100)
assert R_uniform_A0_negligible == Q(196) / Q(121)
assert Q(161) / Q(100) < R_uniform_A0_negligible < Q(162) / Q(100)
assert Q(70) / Q(100) < R_ws_A1_negligible < Q(72) / Q(100)
assert Q(158) / Q(100) < R_ws_A0_negligible < Q(160) / Q(100)

pf_average_lower_shell = Q(615) / Q(1000)
assert (Q(2) / Q(3)) * pf_average_lower_shell == Q(41) / Q(100)

R.<C,radial_num,radial_den,eta,A1,A0> = PolynomialRing(Q)
F = FractionField(R)
epsilon = 3 * F(C) * (F(radial_num) / F(radial_den)) * (
    (F(eta) * F(A1) - F(A0)) / (F(A1) + 3 * F(A0))
)
assert epsilon(C=1, radial_num=1, radial_den=1, eta=uniform_eta, A1=1, A0=0) == 3 * uniform_eta

print((uniform_eta, R_uniform_A1_negligible, R_uniform_A0_negligible,
       R_ws_A1_negligible, R_ws_A0_negligible, Q(41) / Q(100)))
