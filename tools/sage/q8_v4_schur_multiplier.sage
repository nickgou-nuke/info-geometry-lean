# Exact-rational Sage certificate for Q8 Schur cover of V4
K.<i> = QuadraticField(-1)
M2 = MatrixSpace(K, 2, 2)

M_i = M2([[i, 0], [0, -i]])
M_j = M2([[0, 1], [-1, 0]])
M_k = M2([[0, i], [i, 0]])
I2 = M2([[1, 0], [0, 1]])

assert M_i^2 == -I2
assert M_j^2 == -I2
assert M_k^2 == -I2
assert M_i * M_j * M_k == -I2

assert M_i * M_j == -(M_j * M_i)

print("Sage: Q8 Schur Cover of V4 relations verified successfully.")
