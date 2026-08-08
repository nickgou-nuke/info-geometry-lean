#!/usr/bin/env python3
"""SymPy witness for SUNQuantumBraidDuality.lean.

Checks finite SU(N)-style color-lane braid data for several N:

1. adjacent transposition Artin relation;
2. distant adjacent generators commute;
3. q-scaled braid windows carry the same scalar on both Artin sides;
4. Cantor-local diagonal gauge steps are braid-covariant;
5. invariant local weights commute with a braid generator;
6. |S_N| = N!;
7. q = exp(theta - beta*(E - mu*Q)) has the expected chemical-potential shift.
"""

from itertools import permutations
from math import factorial

import sympy as sp


def swap_matrix(n: int, i: int) -> sp.Matrix:
    """Permutation matrix for adjacent swap i <-> i+1 on n color lanes."""
    P = sp.eye(n)
    P[i, i] = 0
    P[i + 1, i + 1] = 0
    P[i, i + 1] = 1
    P[i + 1, i] = 1
    return P


def extend_singlet(P: sp.Matrix) -> sp.Matrix:
    """Extend an n-color permutation matrix by a singlet lane."""
    n = P.rows
    Q = sp.zeros(n + 1)
    Q[:n, :n] = P
    Q[n, n] = 1
    return Q


def check_n(n: int) -> None:
    assert n >= 2
    q = sp.symbols(f"q_{n}")
    psi_symbols = sp.symbols(f"psi0:{n}_N{n}")
    singlet = sp.symbols(f"singlet_N{n}")
    psi = sp.Matrix([*psi_symbols, singlet])

    # Adjacent Artin relation in every 3-strand window.
    for i in range(n - 2):
        s_i = swap_matrix(n, i)
        s_j = swap_matrix(n, i + 1)
        assert s_i * s_j * s_i == s_j * s_i * s_j

        s_i4 = extend_singlet(s_i)
        s_j4 = extend_singlet(s_j)
        lhs = q * s_i4 * (q * s_j4 * (q * s_i4 * psi))
        rhs = q * s_j4 * (q * s_i4 * (q * s_j4 * psi))
        assert sp.simplify(lhs - rhs) == sp.zeros(n + 1, 1)

    # Distant adjacent generators commute.
    for i in range(n - 1):
        for j in range(n - 1):
            if abs(i - j) > 1:
                s_i = swap_matrix(n, i)
                s_j = swap_matrix(n, j)
                assert s_i * s_j == s_j * s_i

    # Cantor-local gauge covariance for each adjacent generator.
    weights = sp.symbols(f"w0:{n}_N{n}")
    s = sp.symbols(f"s_N{n}")
    gauge = sp.diag(*weights, s)
    for i in range(n - 1):
        P = extend_singlet(swap_matrix(n, i))
        transported = list(weights)
        transported[i], transported[i + 1] = transported[i + 1], transported[i]
        transported_gauge = sp.diag(*transported, s)

        lhs = q * P * gauge * psi
        rhs = transported_gauge * (q * P * psi)
        assert sp.simplify(lhs - rhs) == sp.zeros(n + 1, 1)

        invariant = list(weights)
        invariant[i + 1] = invariant[i]
        invariant_gauge = sp.diag(*invariant, s)
        lhs_comm = q * P * invariant_gauge * psi
        rhs_comm = invariant_gauge * (q * P * psi)
        assert sp.simplify(lhs_comm - rhs_comm) == sp.zeros(n + 1, 1)

    assert len(set(permutations(range(n)))) == factorial(n)


for n in range(2, 8):
    check_n(n)
    print(f"SU({n}) finite braid/gauge witness: VERIFIED")


beta, E, mu, Q, theta, dmu = sp.symbols("beta E mu Q theta dmu", real=True)
rho = theta - beta * (E - mu * Q)
rho_shift = theta - beta * (E - (mu + dmu) * Q)
assert sp.simplify(rho_shift - rho) == beta * dmu * Q

a = sp.symbols("a", real=True)
T_U = a / (2 * sp.pi)
assert sp.simplify((2 * sp.pi) * T_U - a) == 0
assert T_U.subs(a, 0) == 0

print("q-clock/Unruh shift witness: VERIFIED")
print("sun_quantum_braid_duality.py: all witnesses passed")
