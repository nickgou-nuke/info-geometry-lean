#!/usr/bin/env python3
from __future__ import annotations

import json
import sympy as sp


def qmul(a, b):
    aw, ax, ay, az = a
    bw, bx, by, bz = b
    return (
        aw * bw - ax * bx - ay * by - az * bz,
        aw * bx + ax * bw + ay * bz - az * by,
        aw * by - ax * bz + ay * bw + az * bx,
        aw * bz + ax * by - ay * bx + az * bw,
    )


def qadd(a, b):
    return tuple(sp.simplify(a[i] + b[i]) for i in range(4))


def qneg(a):
    return tuple(sp.simplify(-a[i]) for i in range(4))


def qconj(a):
    aw, ax, ay, az = a
    return (aw, -ax, -ay, -az)


def qnorm(a):
    return sp.simplify(sum(t * t for t in a))


def qinv(a):
    n = qnorm(a)
    c = qconj(a)
    return tuple(sp.simplify(t / n) for t in c)


def qstr(a):
    return [str(sp.simplify(t)) for t in a]


def vahlen_action(a, b, c, d, q):
    num = qadd(qmul(a, q), b)
    den = qadd(qmul(c, q), d)
    return qmul(num, qinv(den))


def scalar_packet():
    one = (sp.Integer(1), 0, 0, 0)
    zero = (0, 0, 0, 0)
    two = (sp.Integer(2), 0, 0, 0)
    half = (sp.Rational(1, 2), 0, 0, 0)
    q = (sp.Integer(1), sp.Integer(2), sp.Integer(3), sp.Integer(4))
    image = vahlen_action(two, zero, zero, one, q)
    recovered = vahlen_action(half, zero, zero, one, image)
    assert all(sp.simplify(q[i] - recovered[i]) == 0 for i in range(4))
    return {
        "matrix": {"a": qstr(two), "b": qstr(zero), "c": qstr(zero), "d": qstr(one)},
        "input_quaternion": qstr(q),
        "image": qstr(image),
        "recovered": qstr(recovered),
        "norm_input": str(qnorm(q)),
        "norm_image": str(qnorm(image)),
        "boundary_infinity_fixed": True,
        "inverse_recovers_input": True,
    }


def noncomm_packet():
    one = (sp.Integer(1), 0, 0, 0)
    zero = (0, 0, 0, 0)
    i = (0, sp.Integer(1), 0, 0)
    j = (0, 0, sp.Integer(1), 0)
    q = (sp.Integer(1), sp.Integer(2), sp.Integer(3), sp.Integer(4))
    a_inv = qinv(i)
    b_inv = qneg(qmul(a_inv, j))
    image = vahlen_action(i, j, zero, one, q)
    recovered = vahlen_action(a_inv, b_inv, zero, one, image)
    ij = qmul(i, j)
    ji = qmul(j, i)
    assert all(sp.simplify(q[i] - recovered[i]) == 0 for i in range(4))
    assert any(sp.simplify(ij[k] - ji[k]) != 0 for k in range(4))
    return {
        "matrix": {"a": qstr(i), "b": qstr(j), "c": qstr(zero), "d": qstr(one)},
        "inverse_matrix": {"a": qstr(a_inv), "b": qstr(b_inv), "c": qstr(zero), "d": qstr(one)},
        "input_quaternion": qstr(q),
        "image": qstr(image),
        "recovered": qstr(recovered),
        "a_mul_b": qstr(ij),
        "b_mul_a": qstr(ji),
        "noncommuting_coefficients": True,
        "boundary_infinity_fixed": True,
        "inverse_recovers_input": True,
    }


def main():
    report = {
        "scalar_packet": scalar_packet(),
        "noncommutative_affine_packet": noncomm_packet(),
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    print("VAHLEN_SYMPY_OK")


if __name__ == "__main__":
    main()
