import sympy as sp


A = sp.Matrix([[1, 1], [1, 0]])
I2 = sp.eye(2)
assert A * A == A + I2
assert A.det() == -1

allowed = {
    (0, 0): A[0, 0] == 1,
    (0, 1): A[0, 1] == 1,
    (1, 0): A[1, 0] == 1,
    (1, 1): A[1, 1] == 1,
}
assert allowed[(0, 0)]
assert allowed[(0, 1)]
assert allowed[(1, 0)]
assert not allowed[(1, 1)]

sqrt5 = sp.sqrt(5)
phi = (1 + sqrt5) / 2
assert sp.simplify(phi**2 - phi - 1) == 0

for n in range(12):
    word_n = sp.fibonacci(n + 2)
    word_np1 = sp.fibonacci(n + 3)
    word_np2 = sp.fibonacci(n + 4)
    assert word_np2 == word_np1 + word_n

beta = sp.symbols("beta", real=True)
finite_partition_zero = sp.fibonacci(2) * sp.exp(-0 * beta)
assert sp.simplify(finite_partition_zero - 1) == 0

print("CuntzKriegerPrimon.py: Fibonacci adjacency and partition identities verified")
