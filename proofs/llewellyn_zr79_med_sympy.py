import sympy as sp

Q = sp.Rational

def Tz(N, Z):
    return Q(N - Z, 2)

assert Tz(39, 40) == -Q(1, 2)
assert Tz(40, 39) == Q(1, 2)

def MED(excitation_tz_neg_half, excitation_tz_pos_half):
    return excitation_tz_neg_half - excitation_tz_pos_half

def level_from_transition(lower, gamma):
    return lower + gamma

states = {
    "7/2": dict(Ezr=Q(184), Ey=Q(183), Eth_zr=Q(228), Eth_y=Q(226), med=Q(1), err=Q(1)),
    "9/2": dict(Ezr=Q(416), Ey=Q(411), Eth_zr=Q(522), Eth_y=Q(515), med=Q(5), err=Q(2)),
    "11/2": dict(Ezr=Q(715), Ey=Q(726), Eth_zr=Q(886), Eth_y=Q(875), med=-Q(11), err=Q(4)),
    "13/2": dict(Ezr=Q(1042), Ey=Q(1042), Eth_zr=Q(1291), Eth_y=Q(1291), med=Q(0), err=Q(1)),
}

for row in states.values():
    central = MED(row["Ezr"], row["Ey"])
    assert abs(central - row["med"]) <= row["err"]

assert MED(states["7/2"]["Ezr"], states["7/2"]["Ey"]) == 1
assert MED(states["9/2"]["Ezr"], states["9/2"]["Ey"]) == 5
assert MED(states["11/2"]["Ezr"], states["11/2"]["Ey"]) == -11
assert MED(states["13/2"]["Ezr"], states["13/2"]["Ey"]) == 0

beta_y_184 = Q(294, 1000)
beta_y_227_411 = Q(296, 1000)
beta_y_high = Q(304, 1000)
beta_zr_184 = Q(298, 1000)
beta_zr_high = Q(304, 1000)
assert beta_y_184 < beta_y_227_411 < beta_y_high
assert beta_zr_184 < beta_zr_high

assert level_from_transition(183, 227) - 411 == -1
assert level_from_transition(184, 230) - 416 == -2
assert abs(level_from_transition(183, 227) - 411) <= 3
assert abs(level_from_transition(184, 230) - 416) <= 3

def ncci_residual(experimental_med, theoretical_med):
    return experimental_med - theoretical_med

assert abs(ncci_residual(1, 228 - 226)) <= 2
assert abs(ncci_residual(5, 522 - 515)) <= 2
assert 10 * 4 == 40

print({
    "Tz_Zr79": Tz(39, 40),
    "Tz_Y79": Tz(40, 39),
    "MED_7_2": MED(184, 183),
    "MED_9_2": MED(416, 411),
    "MED_11_2": MED(715, 726),
    "Zr_cascade_discrepancy": level_from_transition(184, 230) - 416,
})
