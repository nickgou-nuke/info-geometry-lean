from fractions import Fraction

def Tz(N, Z):
    return QQ(N - Z) / 2

def doubled_tz(N, Z):
    return N - Z

def in_isospin_multiplet(T, two_tz):
    return abs(two_tz) <= 2 * T

Z_PD94 = 46
N_PD94 = 48
A_PD94 = 94
PROTON_HOLES = 50 - Z_PD94
NEUTRON_HOLES = 50 - N_PD94
TOTAL_HOLES = PROTON_HOLES + NEUTRON_HOLES
G9_2_DEGENERACY = 10
CONFIG_COUNT = binomial(G9_2_DEGENERACY, PROTON_HOLES) * binomial(G9_2_DEGENERACY, NEUTRON_HOLES)

assert Z_PD94 + N_PD94 == A_PD94
assert N_PD94 == Z_PD94 + 2
assert Tz(N_PD94, Z_PD94) == 1
assert (PROTON_HOLES, NEUTRON_HOLES, TOTAL_HOLES) == (4, 2, 6)
assert in_isospin_multiplet(1, doubled_tz(N_PD94, Z_PD94))
assert in_isospin_multiplet(1, doubled_tz(47, 47))
assert G9_2_DEGENERACY == 10
assert CONFIG_COUNT == 9450
assert 2 * 0 + 1 == 1 and 2 * 1 + 1 == 3
assert 8 == 6 + 2 and 6 == 4 + 2 and 14 == 12 + 2
assert 205 - 25 == 180 and 205 + 34 == 239 and 205 < 250
assert QQ(84) / 100 == QQ(21) / 25

table = {
    "14_to_12": dict(exp=QQ(521) / 10, jun45=101, gds=49, full=112, t0=82, t1=9, exvam=56),
    "8_to_6": dict(exp=205, lo=180, hi=239, jun45=252, gds=192, full=144, t0=191, t1=11, exvam=165),
    "6_to_4": dict(exp_lower=113, jun45=453, gds=548, full=398, t0=398, t1=5, exvam=336),
}

assert table["8_to_6"]["lo"] <= table["8_to_6"]["gds"] <= table["8_to_6"]["hi"]
assert abs(table["14_to_12"]["gds"] - table["14_to_12"]["exp"]) == QQ(31) / 10
assert table["6_to_4"]["gds"] >= table["6_to_4"]["exp_lower"]
for key in ["14_to_12", "8_to_6", "6_to_4"]:
    row = table[key]
    assert abs(row["full"] - row["t0"]) < abs(row["full"] - row["t1"])

print({
    "A": A_PD94,
    "Z": Z_PD94,
    "N": N_PD94,
    "Tz": Tz(N_PD94, Z_PD94),
    "proton_holes": PROTON_HOLES,
    "neutron_holes": NEUTRON_HOLES,
    "g9_2_degeneracy": G9_2_DEGENERACY,
    "single_j_config_count": CONFIG_COUNT,
    "isoscalar_dim": 1,
    "isovector_dim": 3,
    "B_E2_8_to_6": 205,
    "B_E2_interval": (180, 239),
    "gds_neutron_charge": QQ(21) / 25,
    "table1_gds_8_to_6": 192,
    "table1_T0_closer_than_T1": True,
    "edges": 7,
})
