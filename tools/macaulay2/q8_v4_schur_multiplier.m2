-- Exact-rational Macaulay2 certificate for Q8 Schur cover of V4
-- Explicitly loads Dmodules as requested.

needsPackage "Dmodules"

-- We work over the exact rational field adjoined with I (since i^2 = -1)
QQi = QQ[i] / (i^2 + 1)

-- Define the 2x2 matrices over the base ring QQi
M_i = matrix {{i, 0}, {0, -i}}
M_j = matrix {{0, 1}, {-1, 0}}
M_k = matrix {{0, i}, {i, 0}}
I2 = matrix {{1, 0}, {0, 1}}

-- Verify Q8 relations
assert (M_i^2 == -I2)
assert (M_j^2 == -I2)
assert (M_k^2 == -I2)
assert (M_i * M_j * M_k == -I2)

-- Verify Projective Commutativity
assert (M_i * M_j == - (M_j * M_i))

print "M2: Q8 Schur Cover of V4 relations verified successfully using exact rationals."
exit 0
