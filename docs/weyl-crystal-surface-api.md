# Weyl / Crystal Surface API

> Status: finite shadow index
> Audited: 2026-06-11
> Boundary: this index records the repo-owned finite Weyl-character and crystal
> packets. It does not claim the full Weyl character formula, a general crystal
> basis theorem, or an affine/Weyl-group classification theorem.

This page is the short practical map for the finite Weyl/crystal corridor.

## Primary Lean Owners

- `lean/InfoGeometry/Canonical/WeylAlternatingNumeratorShadow.lean`
- `lean/InfoGeometry/Canonical/WeylCharacterVandermondeShadow.lean`
- `lean/InfoGeometry/Canonical/WeylLocalCancellationShadow.lean`
- `lean/InfoGeometry/Canonical/BinaryCrystalWeylBlochBridge.lean`

## What These Owners Actually Prove

- `WeylAlternatingNumeratorShadow`
  - finite alternating Gibbs numerator
  - pointwise `±1` sign shadow
  - no quotient regularity claim

- `WeylCharacterVandermondeShadow`
  - finite D4 character packet
  - finite Vandermonde denominator witness
  - denominator zero iff collision
  - nonzero denominator iff injective nodes

- `WeylLocalCancellationShadow`
  - local finite cancellation packet
  - numerator vanishes on the collision locus
  - quotient is only defined on the noncollision domain

- `BinaryCrystalWeylBlochBridge`
  - binary lattice addresses as finite words
  - crystal-cell split by Cantor cylinders
  - parity toggles under one refinement
  - observables transform by contragredient action
  - Bloch-wave readout on the symbolic crystal

## Interpretation Boundary

The repo uses the word "Weyl" in several distinct ways:

- finite alternating sign shadow,
- finite Vandermonde exclusion,
- symbolic crystal/Bloch readout,
- later bridge layers that may mention Weyl-like gauge transport.

Those are not interchangeable. This index records the theorem-safe surfaces only.

## Suggested Entry Points

- If you need the finite numerator lane, start with
  `WeylAlternatingNumeratorShadow`.
- If you need denominator exclusion, start with
  `WeylCharacterVandermondeShadow`.
- If you need a quotient on the noncollision domain, use
  `WeylLocalCancellationShadow`.
- If you need the symbolic crystal packet, use
  `BinaryCrystalWeylBlochBridge`.
