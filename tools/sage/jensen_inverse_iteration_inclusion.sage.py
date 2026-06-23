#!/usr/bin/env sage -python
"""Sage exact-rational certificate for Jensen inverse-iteration inclusion.

This lane keeps the Jensen data rational, evaluates the quadratic root in Sage's
exact algebraic-number layer, and checks the inclusion interval exactly there.
"""

from sage.all import QQ, QQbar, sqrt


def jensen_polynomial(b, j, z):
    return (-(b[j - 1] - b[j]) * z**2
            + b[j - 1] * (b[j - 2] - b[j]) * z
            - b[j - 1] * b[j] * (b[j - 2] - b[j - 1]))


def accelerated_radius_formula(b, j):
    radicand = ((b[j - 2] - b[j])**2
                - 4 * (b[j - 1] - b[j]) * (b[j - 2] - b[j - 1]) * (b[j] / b[j - 1]))
    return b[j - 1] * ((b[j - 2] - b[j]) - sqrt(QQbar(radicand))) / (2 * (b[j - 1] - b[j]))


def main():
    h = QQ(1) / QQ(5)
    q = QQ(1) / QQ(3)
    b = {j: QQ(h + q**j) for j in range(1, 8)}

    for j in range(3, 8):
        delta = QQbar(accelerated_radius_formula(b, j))
        poly_at_delta = QQbar(jensen_polynomial(b, j, delta))
        assert poly_at_delta == 0, (j, poly_at_delta)
        assert QQbar(h) <= delta <= QQbar(b[j]), (j, delta, b[j])
        mu = QQbar(QQ(7) / QQ(2))
        lam = mu + QQbar(h)
        assert mu - delta <= lam <= mu + delta, (j, lam, delta)

    print("jensen inverse-iteration inclusion sage certificate: ok")


if __name__ == "__main__":
    main()
