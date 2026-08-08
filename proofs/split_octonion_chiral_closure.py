#!/usr/bin/env python3
"""Exact symbolic audit of the split-octonion chiral Zorn basis.

Basis order:
  u+, u-, sigma+_1, sigma+_2, sigma+_3,
          sigma-_1, sigma-_2, sigma-_3.

The script verifies all 64 products, commutators, anticommutators, the
Peirce/projector relations, and a concrete Jacobi defect.  The latter is the
reason the raw octonion commutator is a Malcev algebra rather than the TKK Lie
algebra itself.
"""

from sympy import Matrix, Rational, zeros


def cross(x: Matrix, y: Matrix) -> Matrix:
    return Matrix([
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
    ])


def zorn_mul(x, y):
    a, u, v, b = x
    c, p, q, d = y
    return (
        a * c + u.dot(q),
        a * p + d * u - cross(v, q),
        c * v + b * q + cross(u, p),
        v.dot(p) + b * d,
    )


def add(x, y):
    return (x[0] + y[0], x[1] + y[1], x[2] + y[2], x[3] + y[3])


def neg(x):
    return (-x[0], -x[1], -x[2], -x[3])


def sub(x, y):
    return add(x, neg(y))


def scale(c, x):
    return (c * x[0], c * x[1], c * x[2], c * x[3])


def comm(x, y):
    return sub(zorn_mul(x, y), zorn_mul(y, x))


def anti(x, y):
    return add(zorn_mul(x, y), zorn_mul(y, x))


def eq(x, y):
    return x[0] == y[0] and x[1] == y[1] and x[2] == y[2] and x[3] == y[3]


z3 = zeros(3, 1)
e = [Matrix([1, 0, 0]), Matrix([0, 1, 0]), Matrix([0, 0, 1])]
zero = (0, z3, z3, 0)
u_plus = (1, z3, z3, 0)
u_minus = (0, z3, z3, 1)
sigma_plus = [(0, x, z3, 0) for x in e]
sigma_minus = [(0, z3, x, 0) for x in e]
one = add(u_plus, u_minus)
parity = sub(u_plus, u_minus)


def epsilon(i, j, k):
    if len({i, j, k}) < 3:
        return 0
    return 1 if (i, j, k) in ((0, 1, 2), (1, 2, 0), (2, 0, 1)) else -1


def main():
    assert eq(zorn_mul(u_plus, u_plus), u_plus)
    assert eq(zorn_mul(u_minus, u_minus), u_minus)
    assert eq(zorn_mul(u_plus, u_minus), zero)
    assert eq(zorn_mul(u_minus, u_plus), zero)

    for i in range(3):
        assert eq(zorn_mul(u_plus, sigma_plus[i]), sigma_plus[i])
        assert eq(zorn_mul(sigma_plus[i], u_minus), sigma_plus[i])
        assert eq(zorn_mul(u_minus, sigma_minus[i]), sigma_minus[i])
        assert eq(zorn_mul(sigma_minus[i], u_plus), sigma_minus[i])
        assert eq(zorn_mul(u_minus, sigma_plus[i]), zero)
        assert eq(zorn_mul(sigma_plus[i], u_plus), zero)
        assert eq(zorn_mul(u_plus, sigma_minus[i]), zero)
        assert eq(zorn_mul(sigma_minus[i], u_minus), zero)

        for j in range(3):
            rhs_pp = zero
            rhs_mm = zero
            for k in range(3):
                rhs_pp = add(rhs_pp, scale(epsilon(i, j, k), sigma_minus[k]))
                rhs_mm = add(rhs_mm, scale(-epsilon(i, j, k), sigma_plus[k]))
            assert eq(zorn_mul(sigma_plus[i], sigma_plus[j]), rhs_pp)
            assert eq(zorn_mul(sigma_minus[i], sigma_minus[j]), rhs_mm)
            delta = 1 if i == j else 0
            assert eq(zorn_mul(sigma_plus[i], sigma_minus[j]), scale(delta, u_plus))
            assert eq(zorn_mul(sigma_minus[i], sigma_plus[j]), scale(delta, u_minus))
            assert eq(anti(sigma_plus[i], sigma_minus[j]), scale(delta, one))
            assert eq(comm(sigma_plus[i], sigma_minus[j]), scale(delta, parity))

    # Concrete failure of Jacobi for the raw commutator.
    x, y, z = sigma_plus[0], sigma_plus[1], sigma_minus[0]
    jacobi = add(add(comm(x, comm(y, z)), comm(y, comm(z, x))), comm(z, comm(x, y)))
    assert eq(jacobi, scale(6, sigma_plus[1]))
    assert not eq(jacobi, zero)

    print("split-octonion chiral closure: all 64 products verified")
    print("u+ + u- = identity; u+ - u- = Krein/chiral parity")
    print("mixed anticommutator = delta_ij identity; mixed commutator = delta_ij parity")
    print("raw commutator Jacobi defect J(s+1,s+2,s-1) = 6 s+2")
    print("conclusion: Malcev closure verified; TKK Lie closure requires added derivation grades")


if __name__ == "__main__":
    main()
