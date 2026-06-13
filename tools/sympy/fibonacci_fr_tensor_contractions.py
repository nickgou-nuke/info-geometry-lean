#!/usr/bin/env python3
"""
Exact Fibonacci F/R tensor-contraction validator.

This verifies the three-anyon Fibonacci braid representation in the
tau tau tau -> tau fusion sector.

It deliberately does NOT collapse to the S3 quotient: sigma_i^2 != 1.
"""

import sympy as sp


z, s = sp.symbols("z s")

# z = primitive 10th root of unity, z = exp(pi*i/5)
# Phi_10(z) = z^4 - z^3 + z^2 - z + 1 = 0
#
# s = sqrt(1/phi)
# 1/phi = phi - 1 = z + z^(-1) - 1.
# Since z^5 = -1, z^(-1) = z^9 = -z^4.
# Hence 1/phi = z - z^4 - 1.
relations = [
    z**4 - z**3 + z**2 - z + 1,
    s**2 - (z - z**4 - 1),
]

G = sp.groebner(relations, z, s, order="lex", domain=sp.QQ)


def red(expr):
    """Reduce an expression modulo the exact Fibonacci cyclotomic field relations."""
    expr = sp.expand(expr)
    rem = G.reduce(sp.Poly(expr, z, s, domain=sp.QQ))[1]
    return sp.expand(rem.as_expr())


def red_matrix(M):
    return M.applyfunc(red)


def assert_zero_matrix(name, M):
    Rm = red_matrix(M)
    if any(Rm[i, j] != 0 for i in range(Rm.rows) for j in range(Rm.cols)):
        raise AssertionError(f"{name} failed:\n{Rm}")
    print(f"PASS: {name}")


def assert_nonzero_matrix(name, M):
    Rm = red_matrix(M)
    if all(Rm[i, j] == 0 for i in range(Rm.rows) for j in range(Rm.cols)):
        raise AssertionError(f"{name} unexpectedly vanished")
    print(f"PASS: {name}")
    print(Rm)


# a = 1/phi
a = z - z**4 - 1

F = sp.Matrix([
    [a,  s],
    [s, -a],
])

# R^1_{tau,tau} = exp(-4*pi*i/5) = z^(-4) = z^6
# R^tau_{tau,tau} = exp(3*pi*i/5) = z^3
R = sp.diag(z**6, z**3)

B1 = R
B2 = F * R * F

I2 = sp.eye(2)

assert_zero_matrix("F^2 = I", F * F - I2)

assert_zero_matrix(
    "Artin braid relation B1 B2 B1 = B2 B1 B2",
    B1 * B2 * B1 - B2 * B1 * B2,
)

assert_nonzero_matrix(
    "non-Abelianity [B1, B2] != 0",
    B1 * B2 - B2 * B1,
)

assert_nonzero_matrix(
    "Fibonacci phase survives: B1^2 != I",
    B1 * B1 - I2,
)

assert_nonzero_matrix(
    "Fibonacci phase survives: B2^2 != I",
    B2 * B2 - I2,
)

print("Reduced B1:")
print(red_matrix(B1))

print("Reduced B2 = F R F:")
print(red_matrix(B2))

print("All exact Fibonacci F/R tensor-contraction checks passed.")
