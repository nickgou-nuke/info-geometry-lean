#!/usr/bin/env python3
"""SymPy witness for the finite Hestenes/Pauli sheet dictionary."""

import sympy as sp

I = sp.I
one = sp.eye(2)
parity = sp.diag(1, -1)
exchange = sp.Matrix([[0, 1], [1, 0]])
phase = sp.Matrix([[0, -I], [I, 0]])
u_plus = (one + parity) / 2
u_minus = (one - parity) / 2
c_plus = (exchange + I * phase) / 2
c_minus = (exchange - I * phase) / 2


def assert_zero(a, name):
    assert a.applyfunc(sp.simplify) == sp.zeros(2), name


assert_zero(parity * parity - one, "parity²")
assert_zero(exchange * exchange - one, "exchange²")
assert_zero(phase * phase - one, "phase²")
assert_zero(parity * exchange + exchange * parity, "{parity,exchange}")
assert_zero(parity * phase + phase * parity, "{parity,phase}")
assert_zero(exchange * phase + phase * exchange, "{exchange,phase}")
assert_zero(u_plus * u_plus - u_plus, "u+²")
assert_zero(u_minus * u_minus - u_minus, "u-²")
assert_zero(u_plus * u_minus, "u+u-")
assert_zero(c_plus * c_plus, "c+²")
assert_zero(c_minus * c_minus, "c-²")
assert_zero(c_plus * c_minus - u_plus, "c+c-")
assert_zero(c_minus * c_plus - u_minus, "c-c+")
assert_zero(c_plus * c_minus + c_minus * c_plus - one, "CAR")

print("SYMPY_HESTENES_PAULI_SHEET=PASS")
