# KR Duality Cascade Index

> Status: finite algebraic T-duality witness
> Audited: 2026-06-11
> Scope: Real-involution carrier, balanced two-charge KR shadow, Buscher sign
> flip, and first-cell `O(5,5)` split-pairing swap
> Boundary: this document does not claim constructed Atiyah `KR^{-n}` groups,
> Real vector bundles, analytic Buscher geometry, Cuntz-Krieger dynamics, or
> Katz-Sarnak monodromy.

This index records the theorem-owned finite corridor for the proposed
K-theoretic T-duality cascade.

## Active Owner Files

- [lean/InfoGeometry/Canonical/KRDualityCascade.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KRDualityCascade.lean)
- [tools/sympy/kr_duality_cascade.py](/home/goutev/repos/info-geometry-lean/tools/sympy/kr_duality_cascade.py)

## Proof Strength

| Surface | Closed content | Conditional content | Not proved |
|---|---|---|---|
| `KRDualityCascade.lean` | Proves the finite Buscher shadow is involutive; proves the first-cell swap squares to identity; proves it preserves the standard split-pairing `O(5,5)` metric; proves local parity anticommutation. | The `KRShadowClass` balance is supplied as explicit finite data and preserved by the Buscher sign flip. | Atiyah `KR^{-n}(X)`, Real vector bundles, Fredholm cycles, analytic T-duality, Cuntz-Krieger maps, global non-orientable orbifold quotient, Katz-Sarnak monodromy. |
| `kr_duality_cascade.py` | Verifies the same finite matrix identities in SymPy and records that the raw swap does not preserve `diag(+1^5,-1^5)`. | None. | Symbolic or analytic KR-theory. |

## Readout

The theorem-owned finite story is:

1. A Real-involution carrier is represented as data, not as a derived global
   quotient.
2. The finite `KRShadowClass` stores a degree index and two balanced chiral
   charges.
3. `buscher_shift` negates the degree and both charges, preserves balance, and
   is an involution.
4. The first-cell Buscher matrix preserves the standard split-pairing
   `O(5,5)` metric `[[0,I],[I,0]]`.
5. The same swap anticommutes with the local first-cell parity operator.

## Verification

```bash
lake env lean lean/InfoGeometry/Canonical/KRDualityCascade.lean
lake build InfoGeometry.Canonical.KRDualityCascade
lake env lean lean/InfoGeometry/Canonical/All.lean
lake env lean lean/InfoGeometry/All.lean
python3 tools/sympy/kr_duality_cascade.py
```
