#!/usr/bin/env python3
"""CMT + TMM simulation for the hyperbolic photonic braid chip.

The local CMT block is
    S(alpha) = [[cosh(alpha), sinh(alpha)], [sinh(alpha), cosh(alpha)]],
with alpha = kappa_im * L.

The 3-port TMM embeddings are
    T1 = S on ports (1,2), identity on port 3,
    T2 = identity on port 1, S on ports (2,3).

Important theorem-honest caveat: these raw nearest-neighbour hyperbolic transfer
matrices are an engineering cascade.  They do not by themselves replace the
separate 4x4 R-matrix/Majorana Yang--Baxter witness for true Artin invariance.
"""

from __future__ import annotations

import numpy as np


def local_s(alpha: float) -> np.ndarray:
    return np.array(
        [[np.cosh(alpha), np.sinh(alpha)], [np.sinh(alpha), np.cosh(alpha)]],
        dtype=float,
    )


def t1(alpha: float) -> np.ndarray:
    c, s = np.cosh(alpha), np.sinh(alpha)
    return np.array([[c, s, 0.0], [s, c, 0.0], [0.0, 0.0, 1.0]], dtype=float)


def t2(alpha: float) -> np.ndarray:
    c, s = np.cosh(alpha), np.sinh(alpha)
    return np.array([[1.0, 0.0, 0.0], [0.0, c, s], [0.0, s, c]], dtype=float)


def intensities(vec: np.ndarray) -> np.ndarray:
    return np.abs(vec) ** 2


def main() -> int:
    wavelength_nm = 1550.0
    length_um = 100.0
    target_alpha = 1.0
    length_cm = length_um * 1e-4
    kappa_im_cm_inv = target_alpha / length_cm

    print("Photonic braid chip CMT+TMM simulation")
    print(f"lambda              = {wavelength_nm:.1f} nm")
    print(f"coupling length L   = {length_um:.1f} um = {length_cm:.5f} cm")
    print(f"target alpha        = {target_alpha:.3f}")
    print(f"required kappa_im   = {kappa_im_cm_inv:.3f} cm^-1")

    S = local_s(target_alpha)
    J2 = np.diag([1.0, -1.0])
    print("\nLocal S(alpha):")
    print(S)
    print("S.T J S - J residual norm:", np.linalg.norm(S.T @ J2 @ S - J2))

    T1, T2 = t1(target_alpha), t2(target_alpha)
    left = T1 @ T2 @ T1
    right = T2 @ T1 @ T2
    print("\nTMM cascades:")
    print("||T1*T2*T1 - T2*T1*T2||_F =", np.linalg.norm(left - right))

    a_in = np.array([1.0, 0.0, 0.0])
    b_left = left @ a_in
    b_right = right @ a_in
    print("\nInput [1,0,0]")
    print("left output amplitudes :", b_left)
    print("right output amplitudes:", b_right)
    print("left output intensities:", intensities(b_left))
    print("right output intensities:", intensities(b_right))

    # At alpha=0 both cascades reduce to identity, matching the Lean theorem.
    zero_residual = np.linalg.norm(t1(0.0) @ t2(0.0) @ t1(0.0) - t2(0.0) @ t1(0.0) @ t2(0.0))
    print("\nzero-coupling cascade residual:", zero_residual)
    if zero_residual > 1e-12:
        raise SystemExit("FAIL zero-coupling TMM identity check")

    print("OK photonic braid chip CMT+TMM simulation completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
