# Sage witness for the finite Hestenes/Krein commuting square.
#
# The code checks the same skeleton as the Lean tower theorem:
#   J^2 = 1,
#   I^2 = -1,
#   J I J = -I,
# and the block embedding preserves the relations.

R = QQ
I2 = identity_matrix(R, 2)
I = matrix(R, [[0, -1], [1, 0]])
J = matrix(R, [[1, 0], [0, -1]])


def embed(M):
    return block_diagonal_matrix(M, M)


assert J^2 == I2
assert I^2 == -I2
assert J * I * J == -I

EJ = embed(J)
EI = embed(I)
I4 = identity_matrix(R, 4)

assert EJ^2 == I4
assert EI^2 == -I4
assert EJ * EI * EJ == -EI
assert embed(J * I * J) == EJ * EI * EJ

print("hestenes_krein_colimit.sage: J_compat and I_compat verified")
