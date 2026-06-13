#!/usr/bin/env sage -python
"""Sage exact-rational Zorn split-octonion verifier."""

from sage.all import QQ


def V(x):
    return [QQ(c) for c in x]


def dot(x, y):
    return sum(x[i] * y[i] for i in range(3))


def cross(x, y):
    return V([
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
    ])


def Z(a, u, v, b):
    return (QQ(a), V(u), V(v), QQ(b))


def zadd(X, Y):
    return Z(X[0] + Y[0], [X[1][i] + Y[1][i] for i in range(3)],
             [X[2][i] + Y[2][i] for i in range(3)], X[3] + Y[3])


def zneg(X):
    return Z(-X[0], [-c for c in X[1]], [-c for c in X[2]], -X[3])


def zsub(X, Y):
    return zadd(X, zneg(Y))


def zscale(r, X):
    r = QQ(r)
    return Z(r * X[0], [r * c for c in X[1]], [r * c for c in X[2]], r * X[3])


def zmul(X, Y):
    a, u, v, b = X
    c, x, y, d = Y
    vxy = cross(v, y)
    uxx = cross(u, x)
    return Z(a*c + dot(u, y),
             [a*x[i] + d*u[i] - vxy[i] for i in range(3)],
             [c*v[i] + b*y[i] + uxx[i] for i in range(3)],
             dot(v, x) + b*d)


def ztrace(X):
    return X[0] + X[3]


def znorm(X):
    return X[0]*X[3] - dot(X[1], X[2])


def zconj(X):
    return Z(X[3], [-c for c in X[1]], [-c for c in X[2]], X[0])


def zone():
    return Z(1, [0, 0, 0], [0, 0, 0], 1)


def zscalar(r):
    return Z(r, [0, 0, 0], [0, 0, 0], r)


def components(X):
    return [X[0], *X[1], *X[2], X[3]]


def is_zero(X):
    return all(c == 0 for c in components(X))


def assert_zero(name, X):
    if not is_zero(X):
        raise AssertionError(f"{name} failed: {components(X)}")
    print(f"PASS: {name}")


def assert_not_zero(name, X):
    if is_zero(X):
        raise AssertionError(f"{name} unexpectedly vanished")
    print(f"PASS: {name}: {components(X)}")


def assoc(X, Y, W):
    return zsub(zmul(zmul(X, Y), W), zmul(X, zmul(Y, W)))


samples = [
    Z(2, [1, 3, -1], [4, 0, 2], -3),
    Z(QQ(1)/2, [0, 1, 2], [-2, 5, 1], QQ(7)/3),
    Z(0, [1, 0, 0], [0, 1, 0], 0),
]

for k, X in enumerate(samples):
    assert_zero(f"sample {k}: X + conjugate(X) = Tr(X)1",
                zsub(zadd(X, zconj(X)), zscalar(ztrace(X))))
    assert_zero(f"sample {k}: X conjugate(X) = N(X)1",
                zsub(zmul(X, zconj(X)), zscalar(znorm(X))))
    assert_zero(f"sample {k}: quadratic identity",
                zadd(zsub(zmul(X, X), zscale(ztrace(X), X)), zscalar(znorm(X))))

E1 = Z(0, [1, 0, 0], [0, 0, 0], 0)
E2 = Z(0, [0, 1, 0], [0, 0, 0], 0)
E3 = Z(0, [0, 0, 1], [0, 0, 0], 0)
assert_not_zero("nonassociativity witness", assoc(E1, E2, E3))
assert_zero("left alternativity witness", assoc(E1, E1, E2))
assert_zero("right alternativity witness", assoc(E2, E1, E1))

P = Z(1, [1, 0, 0], [0, 0, 0], 0)
assert ztrace(P) == 1 and znorm(P) == 0
assert_zero("trace-one norm-zero idempotent", zsub(zmul(P, P), P))

Q = Z(0, [1, 0, 0], [0, 0, 0], 0)
assert ztrace(Q) == 0 and znorm(Q) == 0
assert_zero("trace-zero norm-zero nilpotent", zmul(Q, Q))

print("All Sage exact-rational Zorn checks passed.")
