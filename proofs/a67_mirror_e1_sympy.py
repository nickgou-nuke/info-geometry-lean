import sympy as sp

Q = sp.Rational

A = 67
Z_As, N_As = 33, 34
Z_Se, N_Se = 34, 33
assert Z_As == N_Se
assert Z_Se == N_As

two_Ji = 9
spin_den = two_Ji + 1

M_IV_725_717 = Q(29, 10000)
M_IS_725_717 = Q(9, 10000)

BE1_As_725 = (M_IV_725_717 + M_IS_725_717) ** 2 / spin_den
BE1_Se_717 = (M_IV_725_717 - M_IS_725_717) ** 2 / spin_den
ratio_725_717 = sp.factor(BE1_As_725 / BE1_Se_717)
alpha_725_717 = sp.factor(M_IS_725_717 / M_IV_725_717)

assert BE1_As_725 == Q(361, 250000000)
assert BE1_Se_717 == Q(1, 2500000)
assert ratio_725_717 == Q(361, 100)
assert Q(3, 10) < alpha_725_717 < Q(2, 5)

MIV_319_303 = sp.Interval.open(Q(45, 10000), Q(64, 10000))
MIS_319_303 = sp.Interval.open(Q(27, 10000), Q(45, 10000))
assert Q(11, 2000) in MIV_319_303
assert Q(9, 2500) in MIS_319_303

e, R, DeltaE0, ri, rj = sp.symbols("e R DeltaE0 ri rj", nonzero=True)
C_IVGMR = ((A - 1) * e**2) / (4 * R * DeltaE0)
one_body = ri**3 / R**2
two_body = ri * rj**2 / R**3
M_IS_induced = sp.factor(C_IVGMR * (one_body + two_body))

unit_kernel = M_IS_induced.subs({e: 1, R: 1, DeltaE0: 20, ri: 1, rj: 1})
assert unit_kernel == Q(33, 20)

print({
    "pair": "67As/67Se",
    "BE1_As_725": BE1_As_725,
    "BE1_Se_717": BE1_Se_717,
    "ratio_725_717": ratio_725_717,
    "MIS_over_MIV": alpha_725_717,
    "IVGMR_unit_kernel": unit_kernel,
})
