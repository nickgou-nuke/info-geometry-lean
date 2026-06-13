# Inverse Zeta / Weyl / Witten Master Key API

> Status: finite master-key index
> Audited: 2026-06-11
> Boundary: this page records the finite prime/Witten/Weyl packet and the
> analytic inverse-zeta witness surface. It does not claim the full analytic
> Riemann Hypothesis or the full infinite Weyl character formula.

## Primary Lean Owner

- `lean/InfoGeometry/Canonical/InverseZetaWeylMasterKey.lean`

## What The Owner Actually Packages

- prime-bit Möbius parity on a finite prime register
- finite Boolean Witten cancellation
- finite prime Weyl denominator identity
- finite Weyl denominator = finite parity supertrace
- graded partition supertrace = inverse-zeta witness

## Companion Owners

- `lean/InfoGeometry/Arithmetic/MobiusWittenWeylDenominator.lean`
- `lean/InfoGeometry/Arithmetic/PrimeBitWittenIndex.lean`
- `lean/InfoGeometry/Arithmetic/PrimeSuperalgebra.lean`
- `lean/InfoGeometry/Arithmetic/KudinoorWittenIndexBridge.lean`
- `lean/InfoGeometry/Arithmetic/MoebiusSignature.lean`
- `lean/InfoGeometry/Canonical/WeylSignum.lean`
- `lean/InfoGeometry/Canonical/PrimonSupersymmetry.lean`
- `lean/InfoGeometry/Canonical/WeylSupertraceOwner.lean`
- `lean/InfoGeometry/Canonical/WeylCharacterEquivalence.lean`

## Proof Boundary

This is the finite theorem surface only.
It does not prove:

- analytic continuation of `ζ(s)` or `1/ζ(s)`;
- the infinite Dirichlet-series identity `1 / ζ(s) = Σ μ(n)n^{-s}`;
- McKean-Singer on a global manifold;
- the continuum Hilbert-Pólya conjecture;
- the full Weyl character formula in the infinite-dimensional setting.
