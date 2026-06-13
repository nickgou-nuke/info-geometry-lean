# Möbius Witten Weyl Denominator Index

> Status: finite arithmetic owner bridge
> Audited: 2026-06-11
> Scope: finite Möbius polynomial, finite Witten/fermionic supertrace, finite
> Weyl/Euler denominator, and finite boson-denominator cancellation
> Boundary: this document does not claim analytic convergence,
> `1 / ζ(s)` as an infinite Dirichlet series, McKean-Singer theory,
> Weyl-Kac denominator identities, zero localization, or the Riemann Hypothesis.

This index records the theorem-owned finite core behind the slogan:

```text
Mobius parity supertrace = finite Weyl denominator.
```

## Active Owner Files

- [lean/InfoGeometry/Arithmetic/MobiusDirichletInverseBridge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic/MobiusDirichletInverseBridge.lean)
- [lean/InfoGeometry/Arithmetic/PrimeWeylDenominatorBridge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic/PrimeWeylDenominatorBridge.lean)
- [lean/InfoGeometry/Arithmetic/MobiusWittenWeylDenominator.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic/MobiusWittenWeylDenominator.lean)
- [tools/sympy/mobius_witten_weyl_denominator.py](/home/goutev/repos/info-geometry-lean/tools/sympy/mobius_witten_weyl_denominator.py)

## Proof Strength

| Surface | Closed content | Conditional content | Not proved |
|---|---|---|---|
| `MobiusDirichletInverseBridge.lean` | Proves the finite Möbius Dirichlet polynomial over a prime register equals the finite fermionic Euler product. | Uses finite prime-register data. | Infinite Dirichlet series, convergence, reciprocal zeta identity. |
| `PrimeWeylDenominatorBridge.lean` | Proves the finite Weyl/Euler denominator equals the finite signed fermion supertrace `STrF`; proves finite boson × denominator cancellation under nonzero local factors. | Cancellation requires `1 - q p ≠ 0` on the finite support. | Infinite Weyl-Kac denominator, global Weyl group, analytic zeta. |
| `MobiusWittenWeylDenominator.lean` | Directly identifies the finite Möbius polynomial with the finite Weyl denominator and finite Witten supertrace; packages the finite boson × Möbius cancellation. | Requires the same explicit nonzero local factors for the cancellation theorem. | McKean-Singer index theorem, Witten index on a manifold, Riemann-zero localization, RH. |
| `mobius_witten_weyl_denominator.py` | Verifies the same finite subset expansion/product identity in SymPy for a small prime register. | None. | Analytic number theory. |

## Readout

The theorem-owned finite story is:

1. `Σ_{S ⊆ P} μ(∏S) ∏_{p∈S} q p = ∏_{p∈P} (1 - q p)`.
2. `∏_{p∈P} (1 - q p)` is the finite Weyl/Euler denominator.
3. The same product is the finite signed fermionic supertrace `STrF`.
4. The finite bosonic inverse denominator cancels the finite Möbius/Weyl
   denominator when all local factors are nonzero.

## Verification

```bash
lake env lean lean/InfoGeometry/Arithmetic/MobiusWittenWeylDenominator.lean
lake build InfoGeometry.Arithmetic.MobiusWittenWeylDenominator
lake env lean lean/InfoGeometry/All.lean
python3 tools/sympy/mobius_witten_weyl_denominator.py
```
