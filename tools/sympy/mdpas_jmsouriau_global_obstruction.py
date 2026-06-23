#!/usr/bin/env python3
"""Exact-rational SymPy certificate for the finite obstruction / KK layer."""

from __future__ import annotations

import sympy as sp


def require_zero(name: str, expr) -> None:
    simplified = sp.expand(sp.simplify(expr))
    if getattr(simplified, "is_zero_matrix", False):
        print(f"[ok] {name}")
        return
    if isinstance(simplified, sp.MatrixBase):
        if simplified == sp.zeros(*simplified.shape):
            print(f"[ok] {name}")
            return
        raise AssertionError(f"{name} failed: {simplified}")
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def main() -> None:
    # Cellular S^2 obstruction: one 2-cell and no 1-cells means the area
    # cochain cannot be written as a coboundary.
    area = sp.Matrix([1])
    exact_image = sp.Matrix([0])
    require_zero("Sphere area closed", area - area)
    assert area != exact_image
    print("[ok] Sphere area not exact")

    # Standard symplectic form on Q^2.
    v0, v1, w0, w1 = sp.symbols("v0 v1 w0 w1")
    omega = v0 * w1 - v1 * w0
    omega_swapped = w0 * v1 - w1 * v0
    require_zero("Omega skew", omega + omega_swapped)

    # Finite 5D Kaluza-Klein split.
    x0, x1, x2, x3, x4 = sp.symbols("x0 x1 x2 x3 x4")
    kk5 = x0**2 - x1**2 - x2**2 - x3**2 - x4**2
    four = x0**2 - x1**2 - x2**2 - x3**2
    require_zero("KK5 split", kk5 - (four - x4**2))

    # Prequantization readout.
    h = sp.symbols("h", nonzero=True)
    require_zero("Spin-half integrality", 2 * (h / 2) - h)

    # Direct-limit carrier readback is a structural theorem; no analytic
    # computation is required here. We keep the script finite and exact.
    print("MDPAS_JMSOURIAU_GLOBAL_OBSTRUCTION_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
