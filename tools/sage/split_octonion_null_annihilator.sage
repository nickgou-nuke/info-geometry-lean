#!/usr/bin/env sage
"""Exact coordinate audit for null annihilators in the canonical Zorn model.

This is a discovery/regression lane for Baez--Huerta Proposition 7.  All
calculations use exact rational arithmetic and the same coordinate order and
multiplication signs as the canonical Lean Zorn owner:

    (a, b, x0, x1, x2, y0, y1, y2).

Lean remains the proof authority; this script does not certify a Lean theorem.
"""

from sage.all import QQ, PolynomialRing, matrix, vector


def cross(x, y):
    return vector(x.base_ring(), [
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
    ])


def dot(x, y):
    return sum(x[i] * y[i] for i in range(3))


def mul(X, Y):
    """Canonical Zorn product used by Lean."""
    R = X.base_ring()
    a, b = X[0], X[1]
    c, d = Y[0], Y[1]
    x, y = vector(R, X[2:5]), vector(R, X[5:8])
    u, v = vector(R, Y[2:5]), vector(R, Y[5:8])
    return vector(R, [
        a * c + dot(x, v),
        dot(y, u) + b * d,
        *(a * u + d * x - cross(y, v)),
        *(c * y + b * v + cross(x, u)),
    ])


def trace(X):
    return X[0] + X[1]


def norm(X):
    return X[0] * X[1] - dot(vector(X.base_ring(), X[2:5]),
                              vector(X.base_ring(), X[5:8]))


def imaginary(c):
    """Seven imaginary coordinates (a,x,y) as an eight-coordinate Zorn vector."""
    R = c.base_ring()
    return vector(R, [c[0], -c[0], *c[1:4], *c[4:7]])


def right_mul_imaginary_matrix(X):
    """Matrix of Y |-> Y*X from the 7d imaginary space to the 8d Zorn space."""
    R = X.base_ring()
    basis7 = [vector(R, [1 if i == j else 0 for i in range(7)]) for j in range(7)]
    columns = [mul(imaginary(e), X) for e in basis7]
    return matrix(R, 8, 7, lambda i, j: columns[j][i])


def audit_null_vector(label, X):
    assert X != 0
    assert trace(X) == 0
    assert norm(X) == 0
    R = right_mul_imaginary_matrix(X)
    K = R.right_kernel()
    assert R.rank() == 4
    assert K.dimension() == 3

    kernel_vectors = [imaginary(v) for v in K.basis()]
    for Y in kernel_vectors:
        assert mul(Y, X) == 0
        assert norm(Y) == 0
    for Y in kernel_vectors:
        for Z in kernel_vectors:
            assert mul(Y, Z) + mul(Z, Y) == 0

    x7 = vector(QQ, [X[0], *X[2:5], *X[5:8]])
    assert x7 in K
    partner = next(v for v in K.basis() if matrix(QQ, [x7, v]).rank() == 2)
    Y = imaginary(partner)
    assert mul(X, X) == 0
    assert mul(Y, X) == 0
    assert mul(X, Y) == 0
    assert mul(Y, Y) == 0

    print(f"{label}: rank(R_x)={R.rank()}, dim(Ann_x)={K.dimension()}")


# Exact representatives covering diagonal and off-diagonal null shapes, including a = 0.
SAMPLES = {
    "upper nilpotent": vector(QQ, [0, 0, 1, 0, 0, 0, 0, 0]),
    "lower nilpotent": vector(QQ, [0, 0, 0, 0, 0, 1, 0, 0]),
    "mixed a=0": vector(QQ, [0, 0, 1, 0, 0, 0, 1, 0]),
    "nonzero diagonal patch": vector(QQ, [1, -1, 1, 0, 0, -1, 0, 0]),
    "rational generic patch": vector(QQ, [2, -2, 1, 2, 3, 1, 1, -7 / QQ(3)]),
}

for sample_label, sample in SAMPLES.items():
    audit_null_vector(sample_label, sample)


# Symbolic generic audit on the dense patch a != 0 and x2 != 0.  The null equation
# is imposed by eliminating y2: x dot y = -a^2.
P = PolynomialRing(QQ, names=("a", "x0", "x1", "x2", "y0", "y1"))
F = P.fraction_field()
a, x0, x1, x2, y0, y1 = F.gens()
y2 = (-a**2 - x0 * y0 - x1 * y1) / x2
X = vector(F, [a, -a, x0, x1, x2, y0, y1, y2])
R_X = right_mul_imaginary_matrix(X)

# For a != 0, choose the lower vector v freely.  Solving Y*X=0 gives
# c = -(v dot x)/a and u = (c*x - v cross y)/a.
parameter_columns = []
for j in range(3):
    v = vector(F, [1 if i == j else 0 for i in range(3)])
    x = vector(F, [x0, x1, x2])
    y = vector(F, [y0, y1, y2])
    c = -dot(v, x) / a
    u = (c * x - cross(v, y)) / a
    parameter_columns.append(vector(F, [c, *u, *v]))
P_ann = matrix(F, 7, 3, lambda i, j: parameter_columns[j][i])

assert norm(X) == 0
assert R_X * P_ann == 0
assert P_ann.rank() == 3
assert R_X.rank() == 4
print("symbolic dense patch: rank(R_x)=4, explicit annihilator parametrization rank=3")
print("all exact null-annihilator audits passed")
