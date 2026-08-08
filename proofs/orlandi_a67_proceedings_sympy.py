import sympy as sp

Q = sp.Rational

calibration = Q(56, 100)

def centroid_shift_time(c_forward, c_reverse):
    return sp.factor(((c_reverse - c_forward) * calibration) / 2)

raw_tau = centroid_shift_time(Q(409497, 100), Q(409805, 100))
assert raw_tau == Q(1078, 1250)

tau_As67 = Q(7, 10)
tau_Se67 = Q(13, 10)
assert tau_As67 < tau_Se67

tau_As69_known = Q(194, 100)
tau_As69_corrected = Q(21, 10)
assert abs(tau_As69_corrected - tau_As69_known) < Q(1, 5)

branching = [Q(10, 100), Q(84, 100), Q(6, 100)]
assert sum(branching) == 1

BE1_As_725 = Q(13, 10)
BE1_Se_717 = Q(1)
BE1_As_319 = Q(81, 10)
BE1_Se_304 = Q(17, 10)

ratio_first = sp.factor(BE1_As_725 / BE1_Se_717)
ratio_second = sp.factor(BE1_As_319 / BE1_Se_304)

assert ratio_first == Q(13, 10)
assert ratio_second == Q(81, 17)
assert abs(ratio_first - 1) <= Q(3, 10)
assert ratio_second > 4
assert tau_As67 < Q(12) / 4

print({
    "raw_centroid_tau_ns": raw_tau,
    "tau_ns": ("67As", tau_As67, "67Se", tau_Se67),
    "branching_Se67": branching,
    "BE1_ratios": (ratio_first, ratio_second),
})
