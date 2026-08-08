#!/usr/bin/env python3
"""SymPy witness for modular-parabolic time identification.

This is the finite symbolic audit matching the theorem naming layer:
`de Rham d log Q` contracts with the modular/parabolic clock vector field to a
constant tick.
"""

import sympy as sp


def verify_modular_parabolic_time() -> None:
    print("=== SYMPY: MODULAR PARABOLIC TIME WITNESS ===")

    # Quadric coordinates in Pauli/Minkowski chart
    E, px, py, pz = sp.symbols("E p_x p_y p_z", real=True)
    Q = E**2 - px**2 - py**2 - pz**2

    # Forbidden-cone de Rham generator d(log Q)
    omega = [sp.diff(sp.log(Q), z) for z in (E, px, py, pz)]

    # Parabolic scaling/modular vector field candidate
    X_mod = sp.Matrix([E, px, py, pz])
    clock_tick = sp.simplify(sum(X_mod[i] * omega[i] for i in range(4)))
    assert sp.simplify(clock_tick - 2) == 0

    # Flatness of the finite clock: d(clock_tick)=0 and Cartan-style invariance
    d_clock = [sp.simplify(sp.diff(clock_tick, z)) for z in (E, px, py, pz)]
    assert all(v == 0 for v in d_clock)

    # Optional scale check for scalar multiplication
    c = sp.symbols("c", real=True)
    X_scaled = sp.Matrix([c * v for v in X_mod])
    clock_scaled = sp.simplify(sum(X_scaled[i] * omega[i] for i in range(4)))
    assert sp.simplify(clock_scaled - 2 * c) == 0

    # Parabolic shear clock (unipotent): P(t)P(s)=P(t+s)
    N = sp.Matrix([[0, 1], [0, 0]])
    t, s = sp.symbols("t s", real=True)
    It = sp.eye(2) + t * N
    Is = sp.eye(2) + s * N
    ItIs = It * Is
    Its = sp.eye(2) + (t + s) * N
    assert N**2 == sp.zeros(2)
    assert sp.simplify(ItIs - Its) == sp.zeros(2)

    # Algebraic modular derivation shadow: δ(A) = [K, A]
    k1, k2 = sp.symbols("k1 k2")
    A00, A01, A10, A11 = sp.symbols("A00 A01 A10 A11")
    K = sp.diag(k1, k2)
    eps = sp.symbols("eps")
    A = sp.Matrix([[A00, A01], [A10, A11]])
    flow = sp.diag(sp.exp(eps * k1), sp.exp(eps * k2)) * A * sp.diag(sp.exp(-eps * k1), sp.exp(-eps * k2))
    delta = sp.simplify(flow.diff(eps).subs(eps, 0))
    assert sp.simplify(delta - (K * A - A * K)) == sp.zeros(2)

    print("Q =", Q)
    print("ω = d log Q =", omega)
    print("i_X ω =", clock_tick)
    print("d(clock_tick) =", d_clock)
    print("i_(cX) ω =", clock_scaled)
    print("parabolic shear check P(t)P(s)=P(t+s) holds")
    print("modular derivation shadow δ(A)=[K,A] holds")
    print("modular_parabolic_time_witness.py: finite audit passed")


if __name__ == "__main__":
    verify_modular_parabolic_time()
