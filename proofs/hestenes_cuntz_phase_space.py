#!/usr/bin/env python3
"""
SymPy witnesses for proofs/HestenesCuntzPhaseSpace.lean.

Finite coordinate--momentum commutators are trace-obstructed for exact CCR,
so the finite kernel uses the exact Weyl/clock-shift relation P X = - X P.
The direct-colimit spine is represented in Lean by compatible finite-stage
families; here we check the finite cell algebra.
"""

import sympy as sp

I = sp.I
X00, X01, X10, X11 = sp.symbols("X00 X01 X10 X11")
P00, P01, P10, P11 = sp.symbols("P00 P01 P10 P11")

sigma1 = sp.Matrix([[0, 1], [1, 0]])
sigma3 = sp.Matrix([[1, 0], [0, -1]])
one2 = sp.eye(2)


def assert_zero(expr, name):
    if isinstance(expr, sp.MatrixBase):
        z = expr.applyfunc(sp.simplify)
        assert z == sp.zeros(*expr.shape), f"{name} failed:\n{z}"
    else:
        assert sp.simplify(expr) == 0, f"{name} failed: {sp.simplify(expr)}"


def comm(A, B):
    return A * B - B * A

# Trace obstruction: every finite matrix commutator has trace zero.
X = sp.Matrix([[X00, X01], [X10, X11]])
P = sp.Matrix([[P00, P01], [P10, P11]])
assert_zero(sp.trace(comm(X, P)), "trace([X,P]) = 0")
assert sp.trace(I * one2) == 2 * I
assert sp.trace(I * one2) != 0

# Finite Weyl/clock-shift phase cell.
coordinate = sigma3
momentum = sigma1
q = -1
assert_zero(momentum * coordinate - q * coordinate * momentum, "P X = - X P")
assert_zero(comm(coordinate, momentum) - 2 * coordinate * momentum, "[X,P] = 2 X P")
assert_zero(comm(momentum, coordinate) + 2 * coordinate * momentum, "[P,X] = -2 X P")
assert q**2 == 1

# General finite N clock/shift Weyl pair.
def clock_shift_pair(N: int):
    qN = sp.exp(2 * sp.pi * I / N)
    clock = sp.diag(*[qN**k for k in range(N)])
    shift = sp.zeros(N, N)
    for k in range(N):
        shift[(k + 1) % N, k] = 1
    return qN, clock, shift


def assert_numeric_zero(M, name, tol=1e-10):
    if isinstance(M, sp.MatrixBase):
        for entry in M:
            assert abs(complex(sp.N(entry))) < tol, f"{name} failed: {entry}"
    else:
        assert abs(complex(sp.N(M))) < tol, f"{name} failed: {M}"


# With this convention, shift * clock = q^{-1} clock * shift.
# Thus the finite structure constant is q_weyl = q^{-1}.
for N in range(2, 8):
    qN, clock, shift = clock_shift_pair(N)
    q_weyl = qN**-1
    assert_numeric_zero(shift * clock - q_weyl * clock * shift, f"N={N} Weyl relation")
    assert_numeric_zero(q_weyl**N - 1, f"N={N} root of unity")
    assert_numeric_zero(clock * shift - shift * clock - (1 - q_weyl) * clock * shift,
                        f"N={N} commutator factor 1-q")

# Direct-system witness: constant successor embedding preserves the N=2 relation.
for n in range(8):
    stage_coordinate = coordinate
    stage_momentum = momentum
    embedded_coordinate = stage_coordinate  # identity connecting map
    embedded_momentum = stage_momentum
    assert_zero(embedded_momentum * embedded_coordinate - q * embedded_coordinate * embedded_momentum,
                f"stage {n} Weyl relation")

print("hestenes_cuntz_phase_space.py: finite Weyl and direct-family witnesses passed")
