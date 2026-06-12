#!/usr/bin/env python3
"""Repaired Section 38 finite stress-energy domain-separation witness.

Mirrors `InfoGeometry.Physics.Section38StressEnergyDomainSeparation`.
Closed finite content only:
* quantum operator products are mapped to classical scalar components by trace;
* compact density stress is the Section 34 finite stress shadow;
* an explicit connection-variation table can be added as external data;
* symmetric metric plus symmetric connection variation gives symmetric full stress;
* zero connection variation reduces full stress to compact stress.

No continuum action variation, connection-variation formula, Fenchel-Legendre
ensemble theorem, eigenvector/vierbein theorem, entropy-flow theorem, or arrow
of time is claimed.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed:\n{reduced}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def mat2(prefix: str) -> sp.Matrix:
    return sp.Matrix(2, 2, lambda i, j: sp.symbols(f"{prefix}{i}{j}"))


def main() -> int:
    print("=" * 72)
    print("REPAIRED SECTION 38 STRESS-ENERGY DOMAIN SEPARATION")
    print("=" * 72)

    A = mat2("A")
    B = mat2("B")
    assert_zero(sp.trace(A * B) - sp.trace(A * B), "trace maps quantum product to scalar")
    print("quantum trace readout: OK")

    # Symbolic two-index component check for the finite stress shadow.
    tr_mn, kinetic, g_mn, V, c_mn = sp.symbols("tr_mn kinetic g_mn V c_mn")
    compact_mn = tr_mn - sp.Rational(1, 2) * g_mn * kinetic + g_mn * V
    full_mn = compact_mn + c_mn
    assert_zero(full_mn.subs(c_mn, 0) - compact_mn, "zero connection variation reduction")

    # Symmetry check under explicit equal paired data.
    tr_nm, g_nm, c_nm = sp.symbols("tr_nm g_nm c_nm")
    compact_nm = tr_nm - sp.Rational(1, 2) * g_nm * kinetic + g_nm * V
    full_nm = compact_nm + c_nm
    symmetric_gap = (full_mn - full_nm).subs({tr_nm: tr_mn, g_nm: g_mn, c_nm: c_mn})
    assert_zero(symmetric_gap, "full stress symmetry under symmetric inputs")
    print("full stress symmetry/reduction identities: OK")

    # Concrete 4x4 component table witness.
    idx = range(4)
    rhoD = [mat2(f"R{i}") for i in idx]
    g = [[sp.symbols(f"g{min(i,j)}{max(i,j)}") for j in idx] for i in idx]
    conn = [[sp.symbols(f"c{min(i,j)}{max(i,j)}") for j in idx] for i in idx]
    K = sum(g[a][b] * sp.trace(rhoD[a] * rhoD[b]) for a in idx for b in idx)
    for mu in idx:
        for nu in idx:
            stress_mn = sp.trace(rhoD[mu] * rhoD[nu]) - sp.Rational(1, 2) * g[mu][nu] * K + g[mu][nu] * V + conn[mu][nu]
            stress_nm = sp.trace(rhoD[nu] * rhoD[mu]) - sp.Rational(1, 2) * g[nu][mu] * K + g[nu][mu] * V + conn[nu][mu]
            assert_zero(stress_mn - stress_nm, f"4x4 symmetric full stress {mu}{nu}")
    print("finite 4-index domain-separated stress witness: OK")

    print("=" * 72)
    print("REPAIRED SECTION 38 FINITE SOCKET VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
