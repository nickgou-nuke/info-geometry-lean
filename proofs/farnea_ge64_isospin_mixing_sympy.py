import sympy as sp

Q = sp.Rational


def T3(Z, N):
    return (Q(Z) - Q(N)) / 2


def mass_number(N, Z):
    return Q(N) + Q(Z)


assert mass_number(32, 32) == 64
assert T3(32, 32) == 0
assert 40 + 32 - 4 * 2 == 64

large_delta = -Q(39, 10)
small_delta = -Q(9, 100)
chi2_large = Q(54, 100)
chi2_small = Q(80, 100)


def quadrupole_content(delta):
    return sp.factor(delta**2 / (1 + delta**2))


assert chi2_large < chi2_small
assert quadrupole_content(large_delta) == Q(1521, 1621)
assert quadrupole_content(large_delta) > Q(93, 100)

tau9_upper = Q(4)
tau7 = Q(431, 10)
tau5 = Q(242, 10)
lambda7 = Q(232, 10000)
assert tau9_upper < tau5 < tau7
assert Q(43) < 1 / lambda7 < Q(432, 10)

I1665 = Q(567)
I1048 = Q(130)
I747 = Q(89)
assert I1665 + I1048 + I747 == 786
assert I1048 + I747 < I1665

BE1_64 = Q(247, 1_000_000_000)
BM2_64 = Q(606, 100)
BE1_66 = Q(37, 10_000_000)
BM2_66 = Q(39, 10_000)
BM2_68 = Q(71, 100)

assert BE1_64 / BE1_66 == Q(247, 3700)
assert BE1_64 < BE1_66
assert BM2_64 / BM2_66 == Q(20200, 13)
assert BM2_68 < BM2_64

BE2_64_747 = Q(1)
BE2_66_886 = Q(4, 10)
assert BE2_64_747 / BE2_66_886 == Q(5, 2)


def alpha_difference(alpha_i, alpha_f):
    return alpha_i - alpha_f


def eq6_amplitude_scale(alpha_i, alpha_f):
    return sp.factor(Q(2, 3) * alpha_difference(alpha_i, alpha_f) ** 2)


def eq7_BE1_64(alpha2, be1_66):
    return sp.factor(Q(8, 3) * alpha2 * be1_66)


def alpha2_from_BE1(be1_64, be1_66):
    return sp.factor(Q(3, 8) * be1_64 / be1_66)


assert eq6_amplitude_scale(1, -1) == Q(8, 3)
alpha2 = alpha2_from_BE1(BE1_64, BE1_66)
assert alpha2 == Q(741, 29600)
assert 100 * alpha2 == Q(741, 296)
assert Q(24, 1000) < alpha2 < Q(26, 1000)
assert eq7_BE1_64(alpha2, BE1_66) == BE1_64

print({
    "T3_Ge64": T3(32, 32),
    "quadrupole_content_delta_-3.9": quadrupole_content(large_delta),
    "BE1_64_over_66": BE1_64 / BE1_66,
    "alpha2": alpha2,
    "alpha2_percent": 100 * alpha2,
})
