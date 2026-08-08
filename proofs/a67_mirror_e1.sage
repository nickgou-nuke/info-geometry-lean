Q = RationalField()

A = Q(67)
Z_As, N_As = 33, 34
Z_Se, N_Se = 34, 33
assert Z_As == N_Se
assert Z_Se == N_As

two_Ji = 9
spin_den = Q(two_Ji + 1)

M_IV_725_717 = Q(29) / Q(10000)
M_IS_725_717 = Q(9) / Q(10000)

BE1_As_725 = (M_IV_725_717 + M_IS_725_717)^2 / spin_den
BE1_Se_717 = (M_IV_725_717 - M_IS_725_717)^2 / spin_den
ratio_725_717 = BE1_As_725 / BE1_Se_717
alpha_725_717 = M_IS_725_717 / M_IV_725_717

assert BE1_As_725 == Q(361) / Q(250000000)
assert BE1_Se_717 == Q(1) / Q(2500000)
assert ratio_725_717 == Q(361) / Q(100)
assert Q(3) / Q(10) < alpha_725_717 < Q(2) / Q(5)

R.<e,r,DeltaE0,ri,rj> = PolynomialRing(Q)
F = FractionField(R)
eF, rF, DeltaE0F, riF, rjF = F(e), F(r), F(DeltaE0), F(ri), F(rj)
C_IVGMR = ((A - 1) * eF^2) / (4 * rF * DeltaE0F)
one_body = riF^3 / rF^2
two_body = riF * rjF^2 / rF^3
M_IS_induced = C_IVGMR * (one_body + two_body)
unit_kernel = M_IS_induced(e=1, r=1, DeltaE0=20, ri=1, rj=1)

assert unit_kernel == Q(33) / Q(20)

print((BE1_As_725, BE1_Se_717, ratio_725_717, alpha_725_717, unit_kernel))
