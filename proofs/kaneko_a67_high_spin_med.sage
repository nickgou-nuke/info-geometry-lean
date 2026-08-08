Q = RationalField()

def total_med(VCM, VCr, ell, ls):
    return VCM + VCr + ell + ls

epsilon_ll_g9 = Q(-95)
epsilon_ll_f5 = Q(-58)
assert epsilon_ll_g9 - epsilon_ll_f5 == -37

epsilon_ls_g9_Se = Q(-66)
epsilon_ls_f5_Se = Q(66)
assert epsilon_ls_g9_Se - epsilon_ls_f5_Se == -132

am = Q(280)
def radial_med(m_p32_9half, m_p32_J):
    return am * (m_p32_9half / 2 - m_p32_J / 2)

assert radial_med(Q(4), Q(4)) == 0
assert radial_med(Q(4), Q(3)) == 140

high_VCM = Q(-40)
high_VCr = Q(140)
high_ell = Q(0)
high_ls = Q(-132)
high_med = total_med(high_VCM, high_VCr, high_ell, high_ls)
assert high_VCr + high_ls == 8
assert high_med == -32
assert abs(high_med) < 3 * abs(high_VCM)
assert Q(8) == 2 * Q(9)/Q(2) - 1

R.<VCM,VCr,ell,ls,MED> = PolynomialRing(Q)
constraint = MED - (VCM + VCr + ell + ls)
assert constraint(VCM=high_VCM, VCr=high_VCr, ell=high_ell, ls=high_ls, MED=high_med) == 0

print((epsilon_ll_g9 - epsilon_ll_f5, epsilon_ls_g9_Se - epsilon_ls_f5_Se, high_med))
