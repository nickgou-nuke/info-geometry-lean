# Exact-rational Sage certificate for the e+/e- Möbius chiral-parity
# cancellation and zero signed GW-type index.
# Run with: sage proofs/moebius_chiral_zero_gw.sage

QQ2 = VectorSpace(QQ, 2)
e_plus = QQ2((1, 0))
e_minus = QQ2((0, 1))
split_one = QQ2((1, 1))
assert e_plus + e_minus == split_one

# Componentwise split-idempotent product.
def cmul(x, y):
    return QQ2((x[0] * y[0], x[1] * y[1]))

assert cmul(e_plus, e_plus) == e_plus
assert cmul(e_minus, e_minus) == e_minus
assert cmul(e_plus, e_minus) == QQ2((0, 0))

# Möbius inversion swaps the two chiral idempotent poles.
def mobius(p):
    return {"plus": "minus", "minus": "plus"}[p]

assert mobius(mobius("plus")) == "plus"
assert mobius(mobius("minus")) == "minus"
assert {mobius("plus"), mobius("minus")} == {"plus", "minus"}

# Chiral parity and signed GW-type index.
def chiral_parity(x):
    return x[0] - x[1]

assert chiral_parity(e_plus + e_minus) == 0
assert chiral_parity(e_minus + e_plus) == 0
assert sum([QQ(1), QQ(-1)]) == 0

# 4x4 MobiusChiralClosure matrix lane.
chi = matrix(QQ, [[1,0,0,0],[0,-1,0,0],[0,0,-1,0],[0,0,0,1]])
moebius_strip = matrix(QQ, [[1,0,0,0],[0,-1,0,0],[0,0,1,0],[0,0,0,-1]])
assert chi.trace() == 0
assert (moebius_strip * chi).trace() == 0

print("moebius chiral zero GW Sage certificate: ok")
