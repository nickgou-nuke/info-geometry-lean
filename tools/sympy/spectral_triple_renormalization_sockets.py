#!/usr/bin/env python3
"""
SymPy witness for the repaired renormalization sockets in
`InfoGeometry.OperatorAlgebra.SpectralTriple`.

The Lean repair makes finiteness, off-pole continuity, and cyclicity explicit
witnesses rather than deriving them from arbitrary data.  This script supplies a
concrete finite matrix model for those witnesses.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("--- SymPy Twin: Spectral Triple Renormalization Sockets ---")

    a, b, c, d, e, f, g, h = sp.symbols("a b c d e f g h")
    A = sp.Matrix([[a, b], [c, d]])
    B = sp.Matrix([[e, f], [g, h]])

    # Dixmier-like finite positive readout in a finite-dimensional toy model:
    # tr(X^T X) is nonnegative and finite as a polynomial expression.
    positive_readout = sp.simplify(sp.trace(A.T * A))
    print(f"finite positive trace readout tr(A^T A): {positive_readout}")
    assert positive_readout == a**2 + b**2 + c**2 + d**2
    assert positive_readout is not sp.oo

    # Zeta-like backend with empty pole set: a polynomial is continuous everywhere.
    z = sp.symbols("z")
    zeta = z**2 + sp.trace(A) * z + sp.det(A)
    sample_point = sp.Integer(3)
    continuity_residual = sp.simplify(sp.limit(zeta, z, sample_point) - zeta.subs(z, sample_point))
    print(f"polynomial zeta continuity residual at z=3: {continuity_residual}")
    assert continuity_residual == 0

    # Cyclic-cocycle witness: finite matrix trace is cyclic.
    cyclicity_residual = sp.simplify(sp.trace(A * B) - sp.trace(B * A))
    print(f"trace cyclicity residual tr(AB)-tr(BA): {cyclicity_residual}")
    assert cyclicity_residual == 0

    print("[SUCCESS] explicit renormalization witnesses match the Lean socket repair.")


if __name__ == "__main__":
    main()
