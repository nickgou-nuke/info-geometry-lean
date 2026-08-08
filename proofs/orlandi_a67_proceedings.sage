Q = RationalField()

calibration = Q(56) / Q(100)

def centroid_shift_time(c_forward, c_reverse):
    return ((c_reverse - c_forward) * calibration) / 2

raw_tau = centroid_shift_time(Q(409497) / Q(100), Q(409805) / Q(100))
assert raw_tau == Q(1078) / Q(1250)

tau_As67 = Q(7) / Q(10)
tau_Se67 = Q(13) / Q(10)
assert tau_As67 < tau_Se67

branching = [Q(10) / Q(100), Q(84) / Q(100), Q(6) / Q(100)]
assert sum(branching) == 1

ratio_first = (Q(13) / Q(10)) / Q(1)
ratio_second = (Q(81) / Q(10)) / (Q(17) / Q(10))

assert ratio_first == Q(13) / Q(10)
assert ratio_second == Q(81) / Q(17)
assert abs(ratio_first - 1) <= Q(3) / Q(10)
assert ratio_second > 4

R.<cForward,cReverse,tau> = PolynomialRing(Q)
constraint = 2 * tau - (cReverse - cForward) * calibration
assert constraint(cForward=Q(409497)/Q(100), cReverse=Q(409805)/Q(100), tau=raw_tau) == 0

print((raw_tau, tau_As67, tau_Se67, ratio_first, ratio_second))
