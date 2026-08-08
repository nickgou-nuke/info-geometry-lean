import sympy as sp

Q = sp.Rational

def Tz(N, Z):
    return Q(N - Z, 2)

assert Tz(12, 11) == Q(1, 2)
assert Tz(11, 12) == -Q(1, 2)

Z, N, mp, mn, M, c2 = sp.symbols("Z N mp mn M c2", nonzero=True)

def binding_energy(Z0, N0, mp0, mn0, M0, c20):
    return sp.factor((Z0 * mp0 + N0 * mn0 - M0) * c20)

B = binding_energy(Z, N, mp, mn, M, c2)
assert sp.simplify(Z * mp + N * mn - B / c2 - M) == 0

def delta_vpn_oe(Bfun, Z0, N0):
    return sp.factor(((Bfun(Z0, N0) - Bfun(Z0, N0 - 2)) -
                      (Bfun(Z0 - 1, N0) - Bfun(Z0 - 1, N0 - 2))) / 2)

def delta_vpn_eo(Bfun, Z0, N0):
    return sp.factor(((Bfun(Z0, N0) - Bfun(Z0, N0 - 1)) -
                      (Bfun(Z0 - 2, N0) - Bfun(Z0 - 2, N0 - 1))) / 2)

a, b, c = sp.symbols("a b c")
affine = lambda z, n: a * z + b * n + c
assert delta_vpn_oe(affine, Z, N) == 0
assert delta_vpn_eo(affine, Z, N) == 0

def mirror_delta(delta_tz_neg_half, delta_tz_pos_half):
    return sp.factor(delta_tz_neg_half - delta_tz_pos_half)

def central_delta(row):
    return mirror_delta(row["neg"], row["pos"])

def within_error(row):
    return abs(central_delta(row) - row["reported"]) <= row["error"]

rows = {
    "A7": dict(pos=Q(5970), neg=Q(5785), reported=-Q(185), error=Q(35)),
    "A9": dict(pos=Q(1037), neg=Q(914), reported=-Q(123), error=Q(13)),
    "A13": dict(pos=Q(2222), neg=Q(1661), reported=-Q(562), error=Q(3)),
    "A15": dict(pos=Q(41320, 10), neg=Q(41384, 10), reported=Q(64, 10), error=Q(1, 10)),
    "A17": dict(pos=Q(14625, 10), neg=Q(935), reported=-Q(527), error=Q(7)),
    "A19": dict(pos=Q(36966, 10), neg=Q(37467, 10), reported=Q(500, 10), error=Q(3, 10)),
    "A23": dict(pos=Q(318140, 100), neg=Q(31920, 10), reported=Q(106, 10), error=Q(1, 10)),
    "A25": dict(pos=Q(10650, 10), neg=Q(10650, 10), reported=Q(3, 10), error=Q(3, 10)),
    "A29": dict(pos=Q(101510, 100), neg=Q(971), reported=-Q(44), error=Q(5)),
}

assert central_delta(rows["A7"]) == -185
assert central_delta(rows["A9"]) == -123
assert within_error(rows["A13"])
assert central_delta(rows["A15"]) == Q(64, 10)
assert within_error(rows["A17"])
assert within_error(rows["A19"])
assert central_delta(rows["A23"]) == Q(106, 10)
assert within_error(rows["A25"])
assert within_error(rows["A29"])

def near_zero_band(x):
    return abs(x) <= 50

assert near_zero_band(central_delta(rows["A25"]))
assert not near_zero_band(central_delta(rows["A13"]))
assert not near_zero_band(central_delta(rows["A17"]))

large = [A for A in [7, 11, 15, 19] if A % 4 == 3]
small = [A for A in [9, 13, 17, 21] if A % 4 == 1]
assert large == [7, 11, 15, 19]
assert small == [9, 13, 17, 21]

print({
    "Tz_23Na": Tz(12, 11),
    "delta_A7": central_delta(rows["A7"]),
    "delta_A13": central_delta(rows["A13"]),
    "A25_near_zero": near_zero_band(central_delta(rows["A25"])),
    "large_mod4": large,
    "small_mod4": small,
})
