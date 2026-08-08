import sympy as sp

Q = sp.Rational

def med(e_minus_tz, e_plus_tz):
    return e_minus_tz - e_plus_tz

def total_med(VCM, VCr, ell, ls):
    return sp.factor(VCM + VCr + ell + ls)

epsilon_ll_g9 = Q(-95)
epsilon_ll_f5 = Q(-58)
epsilon_ll_p3 = Q(135)
assert epsilon_ll_g9 - epsilon_ll_f5 == -37

epsilon_ls_g9_Se = Q(-66)
epsilon_ls_f5_Se = Q(66)
assert epsilon_ls_g9_Se - epsilon_ls_f5_Se == -132

am = Q(280)
def radial_med(m_p32_9half, m_p32_J):
    return sp.factor(am * (m_p32_9half / 2 - m_p32_J / 2))

assert radial_med(Q(4), Q(4)) == 0
assert radial_med(Q(4), Q(3)) == 140

proton_g9_jump = Q(2)
neutron_g9_jump = Q(1)
assert proton_g9_jump + neutron_g9_jump == 3

high_VCM = Q(-40)
high_VCr = Q(140)
high_ell = Q(0)
high_ls = Q(-132)
high_med = total_med(high_VCM, high_VCr, high_ell, high_ls)

assert high_VCr + high_ls == 8
assert high_med == -32
assert abs(high_med) < 3 * abs(high_VCM)
assert Q(8) == 2 * Q(9, 2) - 1

print({
    "epsilon_ll_gap_g9_f5": epsilon_ll_g9 - epsilon_ll_f5,
    "epsilon_ls_gap_g9_f5": epsilon_ls_g9_Se - epsilon_ls_f5_Se,
    "radial_4_to_3": radial_med(Q(4), Q(3)),
    "g9_total_jump": proton_g9_jump + neutron_g9_jump,
    "high_spin_MED": high_med,
})
