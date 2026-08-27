#!/usr/bin/env python3
"""CAS check of the STU quartic finite-difference polarization."""

from itertools import permutations
import sympy as sp


charges = [
    (sp.Symbol(f"a{k}"), sp.Symbol(f"b{k}"),
     tuple(sp.Symbol(f"x{k}{j}") for j in range(3)),
     tuple(sp.Symbol(f"y{k}{j}") for j in range(3)))
    for k in range(4)
]
perms = list(permutations(range(4)))


def quartic(alpha, beta, x, y):
    xy = sum(x[i] * y[i] for i in range(3))
    xa = (x[1] * x[2], x[0] * x[2], x[0] * x[1])
    ya = (y[1] * y[2], y[0] * y[2], y[0] * y[1])
    return (alpha * beta - xy) ** 2 - 4 * (
        alpha * x[0] * x[1] * x[2]
        + beta * y[0] * y[1] * y[2]
        - sum(xa[i] * ya[i] for i in range(3)))


def p4(values):
    return sum(sp.prod(values[p[i]][i] for i in range(4)) for p in perms) / 24


def subset_value(mask):
    ids = [i for i in range(4) if mask & (1 << i)]
    alpha = sum(charges[i][0] for i in ids)
    beta = sum(charges[i][1] for i in ids)
    x = tuple(sum(charges[i][2][j] for i in ids) for j in range(3))
    y = tuple(sum(charges[i][3][j] for i in ids) for j in range(3))
    return quartic(alpha, beta, x, y)


def explicit():
    alpha = [c[0] for c in charges]
    beta = [c[1] for c in charges]
    x = [[c[2][j] for c in charges] for j in range(3)]
    y = [[c[3][j] for c in charges] for j in range(3)]
    result = sum(
        sp.prod(v[p[i]] for i, v in enumerate((alpha, alpha, beta, beta)))
        for p in perms) / 24
    result -= 2 * sum(p4([alpha, beta, x[j], y[j]]) for j in range(3))
    result += sum(p4([x[j], y[j], x[k], y[k]]) for j in range(3) for k in range(3))
    result -= 4 * p4([alpha, x[0], x[1], x[2]])
    result -= 4 * p4([beta, y[0], y[1], y[2]])
    result += 4 * (p4([x[1], x[2], y[1], y[2]])
                   + p4([x[0], x[2], y[0], y[2]])
                   + p4([x[0], x[1], y[0], y[1]]))
    return result


def main():
    finite_difference = sum(
        (-1) ** (4 - bin(mask).count("1")) * subset_value(mask)
        for mask in range(16)) / 24
    variables = [v for c in charges for v in (c[0], c[1], *c[2], *c[3])]
    difference = sp.Poly(sp.expand(finite_difference - explicit()), *variables)
    if difference.is_zero:
        print("STU quartic polarization certificate: PASS")
    else:
        print("STU quartic polarization certificate: FAIL")
        print("nonzero terms:", len(difference.terms()))
        raise SystemExit(1)


if __name__ == "__main__":
    main()
