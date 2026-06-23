#!/usr/bin/env python3
"""Finite two-point GNS mirror for the AFP Gelfand_Naimark_Segal step.

Algebra: C^2, represented by pairs (a0,a1).
Involution: componentwise conjugation.
Cyclic vector: Omega=(1,1).
Inner product: <x,y> = conjugate(x0)*y0 + conjugate(x1)*y1.
Representation: pi(a)x = componentwise product a*x.
"""

import sympy as sp


def inner2(x, y):
    return sp.conjugate(x[0]) * y[0] + sp.conjugate(x[1]) * y[1]


def involution(a):
    return (sp.conjugate(a[0]), sp.conjugate(a[1]))


def mul_vec(a, x):
    return (a[0] * x[0], a[1] * x[1])


def add_vec(a, b):
    return (a[0] + b[0], a[1] + b[1])


def eq_pair(u, v):
    return all(sp.simplify(u[i] - v[i]) == 0 for i in range(2))


def main():
    a0, a1, b0, b1, x0, x1, y0, y1 = sp.symbols(
        "a0 a1 b0 b1 x0 x1 y0 y1", complex=True
    )
    a = (a0, a1)
    b = (b0, b1)
    x = (x0, x1)
    y = (y0, y1)
    omega_vec = (sp.Integer(1), sp.Integer(1))

    # vector state recovery by definition
    omega_a = inner2(omega_vec, mul_vec(a, omega_vec))
    assert sp.simplify(omega_a - (a0 + a1)) == 0

    # cyclicity: x = pi(x) Omega
    assert eq_pair(mul_vec(x, omega_vec), x)

    # representation laws
    assert eq_pair(mul_vec(add_vec(a, b), x), add_vec(mul_vec(a, x), mul_vec(b, x)))
    assert eq_pair(mul_vec(mul_vec(a, b), x), mul_vec(a, mul_vec(b, x)))
    assert eq_pair(mul_vec(omega_vec, x), x)

    # involution reverses products (commutative here, still checked as stated)
    assert eq_pair(involution(mul_vec(a, b)), mul_vec(involution(b), involution(a)))

    # adjoint relation <a*x,y> = <x,a^* y>
    lhs = inner2(mul_vec(a, x), y)
    rhs = inner2(x, mul_vec(involution(a), y))
    assert sp.simplify(lhs - rhs) == 0

    print("finite two-point GNS checks ok")


if __name__ == "__main__":
    main()
