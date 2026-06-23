# SageMath verification of Hodge-Trifactor operator and partition factors

# 1. Operator algebra
# We verify using a matrix representation of the projectors:
# P_ex = diag(1, 0, 0), P_co = diag(0, 1, 0), P_har = diag(0, 0, 1)
# Then T = P_ex - P_co = diag(1, -1, 0)
P_ex_mat = matrix(SR, [[1, 0, 0], [0, 0, 0], [0, 0, 0]])
P_co_mat = matrix(SR, [[0, 0, 0], [0, 1, 0], [0, 0, 0]])
P_har_mat = matrix(SR, [[0, 0, 0], [0, 0, 0], [0, 0, 1]])

assert P_ex_mat + P_co_mat + P_har_mat == matrix.identity(3)
assert P_ex_mat^2 == P_ex_mat
assert P_co_mat^2 == P_co_mat
assert P_har_mat^2 == P_har_mat
assert P_ex_mat * P_co_mat == 0

T = P_ex_mat - P_co_mat
assert T^3 == T
print("SageMath: Hodge-Trifactor operator algebra verified.")

# 2. Partition functions
x = var('x')
B = 1 / (1 - x)
F = 1 + x
H = 1 - x

assert (B * H).simplify_full() == 1
assert (F * H).simplify_full() == 1 - x^2
print("SageMath: Partition functions verified successfully.")
