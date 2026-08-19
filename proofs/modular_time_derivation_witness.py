#!/usr/bin/env python3
"""SymPy witness: dlog forbidden-cone generator as modular time derivation.

Audit only.  Lean remains the proof kernel; analytic TT/Connes/BW claims are
deferred_interface in Lean.
"""

import sympy as sp


def main() -> None:
    print("=== SYMPY: DE RHAM GENERATOR AS MODULAR DERIVATION CLOCK ===")

    E, px, py, pz, t, s = sp.symbols("E p_x p_y p_z t s", real=True)
    Q = E**2 - px**2 - py**2 - pz**2
    coords = [E, px, py, pz]

    # ω = d log Q around the forbidden cone Q=0.
    omega = [sp.diff(sp.log(Q), c) for c in coords]

    # Radial/parabolic log-scale vector field used as the local modular clock.
    X_modular = sp.Matrix(coords)
    clock_tick = sp.simplify(sum(X_modular[i] * omega[i] for i in range(4)))
    assert clock_tick == 2

    # Negative log-Jacobian clock for the same scale flow in dimension 4.
    # F_t(P)=exp(t)P, det DF_t = exp(4t).  The dlogQ tick is half the Q-scaling;
    # the volume clock differs by the dimension normalization.
    J = sp.exp(4 * t)
    neg_log_jacobian_rate = sp.diff(-sp.log(J), t).subs(t, 0)
    assert neg_log_jacobian_rate == -4
    assert sp.simplify(neg_log_jacobian_rate + 2 * clock_tick) == 0

    # Parabolic/unipotent shear matrix: exp(tN)=I+tN for N^2=0.
    N = sp.Matrix([[0, 1], [0, 0]])
    I2 = sp.eye(2)
    shear_t = I2 + t * N
    shear_s = I2 + s * N
    assert N**2 == sp.zeros(2)
    assert sp.simplify(shear_t.det() - 1) == 0
    assert sp.simplify(shear_s.det() - 1) == 0
    assert sp.simplify(shear_t * shear_s - (I2 + (t + s) * N)) == sp.zeros(2)

    # Finite matrix modular derivation δ(A)=[K,A], the algebraic TT shadow.
    k1, k2 = sp.symbols("k1 k2")
    A00, A01, A10, A11 = sp.symbols("A00 A01 A10 A11")
    eps = sp.symbols("eps")
    K = sp.diag(k1, k2)
    A = sp.Matrix([[A00, A01], [A10, A11]])
    expK = sp.diag(sp.exp(eps * k1), sp.exp(eps * k2))
    sigma = expK * A * expK.inv()
    delta = sigma.diff(eps).subs(eps, 0)
    assert sp.simplify(delta - (K * A - A * K)) == sp.zeros(2)

    print("Q =", Q)
    print("omega = dlog Q =", omega)
    print("X_modular =", list(X_modular))
    print("i_X omega =", clock_tick)
    print("d/dt|-0 (-log det DF_t) =", neg_log_jacobian_rate)
    print("parabolic shear det =", shear_t.det())
    print("shear_t * shear_s = I + (t+s)N verified")
    print("delta(A)=[K,A] verified")
    print("modular_time_derivation_witness.py: finite audit passed")


if __name__ == "__main__":
    main()
