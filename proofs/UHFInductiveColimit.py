import sympy as sp


def kron_embed(A):
    """UHF inclusion M_n -> M_{2n}, A |-> A tensor I_2."""
    return sp.kronecker_product(A, sp.eye(2))


a, b, c, d = sp.symbols("a b c d")
A = sp.Matrix([[a, b], [c, d]])
B = sp.Matrix([[1, 2], [3, 4]])

assert kron_embed(A + B) == kron_embed(A) + kron_embed(B)
assert kron_embed(A * B) == kron_embed(A) * kron_embed(B)
assert kron_embed(sp.eye(2)) == sp.eye(4)

# Diagonal MASA: a finite cylinder function duplicates over the next bit.
u0, u1, v0, v1 = sp.symbols("u0 u1 v0 v1")
f = [u0, u1]
g = [v0, v1]


def diag_embed(values):
    out = []
    for value in values:
        out.extend([value, value])
    return out


def pointwise_add(x, y):
    return [a + b for a, b in zip(x, y)]


def pointwise_mul(x, y):
    return [a * b for a, b in zip(x, y)]


assert diag_embed(pointwise_add(f, g)) == pointwise_add(diag_embed(f), diag_embed(g))
assert diag_embed(pointwise_mul(f, g)) == pointwise_mul(diag_embed(f), diag_embed(g))
assert diag_embed([1, 1]) == [1, 1, 1, 1]

# Finite graded supertrace local factors sit on the diagonal cylinder system.
x2, x3, x5 = sp.symbols("x2 x3 x5")
graded_level_3 = sp.expand((1 - x2) * (1 - x3) * (1 - x5))
embedded_level_3 = diag_embed([graded_level_3])

assert embedded_level_3 == [graded_level_3, graded_level_3]

print("UHFInductiveColimit.py: UHF tensor inclusion and diagonal cylinder embedding verified")
