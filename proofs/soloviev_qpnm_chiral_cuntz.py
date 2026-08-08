#!/usr/bin/env python3
"""
Finite audit witnesses for SolovievQPNMChiralCuntz.lean.

This is not a proof of the full Soloviev quasiparticle--phonon model, AFRODITE
calibration, Grothendieck motives, or Wigner--Dyson universality.  It mirrors the
finite 2x2 chiral matrix-unit kernel proved in Lean and checks the numerical
second-moment comparison quoted in the black-book narrative.
"""

from __future__ import annotations

import math
import numpy as np


def main() -> None:
    I = np.eye(2, dtype=complex)
    Np = np.array([[1, 0], [0, 0]], dtype=complex)
    Nm = np.array([[0, 0], [0, 1]], dtype=complex)
    Sp = np.array([[0, 1], [0, 0]], dtype=complex)
    Sm = np.array([[0, 0], [1, 0]], dtype=complex)
    h = Np - Nm

    assert np.allclose(Sp @ Sp, 0)
    assert np.allclose(Sm @ Sm, 0)
    assert np.allclose(Np @ Np, Np)
    assert np.allclose(Nm @ Nm, Nm)
    assert np.allclose(Sp @ Sm, Np)
    assert np.allclose(Sm @ Sp, Nm)
    assert np.allclose(Sp @ Sm + Sm @ Sp, I)

    # Partial-isometry/CAR-like finite shadow, not a literal O_2 isometry.
    assert np.allclose(Sp.conj().T @ Sp, Nm)
    assert np.allclose(Sm.conj().T @ Sm, Np)
    assert not np.allclose(Sp.conj().T @ Sp, I)

    comm_sp = h @ Sp - Sp @ h
    comm_sm = h @ Sm - Sm @ h
    assert np.allclose(comm_sp, 2 * Sp)
    assert np.allclose(comm_sm, -2 * Sm)

    E_plus, E_minus = 1.25, -0.75
    W = 0.3 + 0.4j
    H = E_plus * Np + E_minus * Nm + W * Sp + W.conjugate() * Sm
    assert np.allclose(H, np.array([[E_plus, W], [W.conjugate(), E_minus]], dtype=complex))
    H0 = E_plus * Np + E_minus * Nm
    assert np.allclose(E_plus * Np + E_minus * Nm + 0 * Sp + 0 * Sm, H0)

    # Coincidence matrix as Gram C = A^† A.
    A = np.array([[1 + 1j, 2 - 1j], [0.5, -0.25j]], dtype=complex)
    C = A.conj().T @ A
    eigvals = np.linalg.eigvalsh(C)
    assert np.all(eigvals > -1e-12), eigvals

    # Numerical witnesses quoted in the request.
    observed_second_moment = 1.1777
    gue_second_moment = 3 * math.pi / 8
    decimal_proxy = 1.1781
    assert abs(observed_second_moment - gue_second_moment) < 5e-4
    assert abs(gue_second_moment - decimal_proxy) < 5e-4
    assert abs(decimal_proxy - observed_second_moment - 0.0004) < 1e-12

    poisson_var = 0.57
    gue_var = 0.178
    assert poisson_var > gue_var

    print("soloviev_qpnm_chiral_cuntz.py: finite witnesses passed")
    print(f"  <s^2> witness: {observed_second_moment:.4f}")
    print(f"  3*pi/8:        {gue_second_moment:.6f}")
    print(f"  Var Poisson/GUE proxy: {poisson_var} > {gue_var}")


if __name__ == "__main__":
    main()
