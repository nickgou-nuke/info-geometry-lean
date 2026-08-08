import sympy as sp

Q = sp.Rational


def T3(Z, N):
    return (Q(Z) - Q(N)) / 2


assert T3(33, 34) == -Q(1, 2)
assert T3(34, 33) == Q(1, 2)

As725_BE1 = Q(14, 10_000_000)
Se717_BE1 = Q(4, 10_000_000)
As725_ME1 = Q(37, 10_000)
Se717_ME1 = Q(20, 10_000)

As319_BE1 = Q(83, 10_000_000)
Se303_BE1_upper = Q(14, 10_000_000)
As319_ME1 = Q(91, 10_000)
Se303_ME1_upper = Q(37, 10_000)

assert As725_BE1 / Se717_BE1 == Q(7, 2)
assert As725_ME1 / Se717_ME1 == Q(37, 20)
assert As319_BE1 / Se303_BE1_upper == Q(83, 14)
assert As319_ME1 / Se303_ME1_upper == Q(91, 37)

MIV = Q(29, 10_000)
MIS = Q(9, 10_000)
assert MIS / MIV == Q(9, 29)

radial_cubic_siegert_ratio = Q(834, 1000)
charge_correction_1MeV = Q(190, 10_000_000)
magnetic_correction_1MeV = Q(53, 100_000)
assert radial_cubic_siegert_ratio == Q(417, 500)
assert charge_correction_1MeV < Q(1, 1000)
assert magnetic_correction_1MeV < Q(1, 1000)

C = Q(116, 1000)
one_body = Q(752, 1000)
two_body = Q(410, 1000)
eta = (one_body - two_body) / one_body
pf_average_r2 = Q(615, 1000)

assert eta == Q(171, 376)
assert Q(45, 100) < eta < Q(46, 100)
assert Q(2, 3) * pf_average_r2 == two_body


def mirror_ratio(eps):
    return sp.factor(((1 + eps) / (1 - eps)) ** 2)


eps_A1_negligible = -Q(872, 10_000)
eps_A0_negligible = Q(120, 1000)
eps_WS_A1_negligible = -Q(852, 10_000)
eps_WS_A0_negligible = Q(116, 1000)

assert mirror_ratio(eps_A1_negligible) == Q(1301881, 1846881)
assert mirror_ratio(eps_A0_negligible) == Q(196, 121)
assert Q(70, 100) < mirror_ratio(eps_WS_A1_negligible) < Q(72, 100)
assert Q(158, 100) < mirror_ratio(eps_WS_A0_negligible) < Q(160, 100)


def eq60_epsilon_kernel(C0, radial_ratio, eta0, A1, A0):
    return sp.factor(3 * C0 * radial_ratio * ((eta0 * A1 - A0) / (A1 + 3 * A0)))


assert eq60_epsilon_kernel(C, one_body, eta, 1, 0) == Q(14877, 125000)
assert Q(67 - 1, 4 * 20) * (1 + 1) == Q(33, 20)

print({
    "T3_As": T3(33, 34),
    "T3_Se": T3(34, 33),
    "TableI_first_BE1_ratio": As725_BE1 / Se717_BE1,
    "eta": eta,
    "R_A1_negligible": mirror_ratio(eps_A1_negligible),
    "R_A0_negligible": mirror_ratio(eps_A0_negligible),
})
