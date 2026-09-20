# Bounded Krein Drazin boundary realization

## Native owner integration

`HodgeCohomology/KreinDrazinGreen.lean` specializes the bilinear Green-adjunction
theorem to the existing bounded `InfoGeometry.Krein.KreinSpace` owner. Its
named `[metric : KreinSpace Space]` parameter supplies the fundamental symmetry
and the indefinite `kreinBilin`. It uses the existing
`kreinAdjoint = J A† J`, not a replacement star operation.

The proof chain is:

1. Map the Drazin equations through Mathlib's
   `ContinuousLinearMap.toLinearMapRingHom`.
2. Apply `DrazinPairingAdjunction.inverse_adjoint` to the supplied indefinite
   form.
3. Use uniqueness of the adjoint pairing to identify the result with the
   existing bounded `kreinAdjoint`.
4. Derive Krein self-adjointness of `A G` and `1 - A G` from that of `A`.

No commutation with the fundamental symmetry, positive energy, or
finite-dimensionality is assumed. The analytic owner's reference inner
product supports boundedness and the continuous-adjoint API; it does not
replace the indefinite pairing in the adjunction theorem. This is a theorem
about supplied bounded operators, not an unbounded Dirac-domain construction.

## Filling the existing boundary packets

`HodgeCohomology/KreinDrazinBoundaryRealization.lean` constructs the existing
`Canonical.KreinDrazinBoundarySupport` structures rather than introducing
parallel boundary definitions:

- `algebraicSplit` derives the regular/defect projector laws from Drazin data
  in an arbitrary ring.
- `carrier`, `adjointData`, and `carrierAdjointData` instantiate the existing
  carrier and adjoint interfaces with actual bounded operators and
  `kreinInner`.
- `boundarySupport` derives all support fields, including both Krein
  self-adjoint projector laws and inversion on the regular sector, from a
  Drazin inverse and Krein self-adjointness of the original operator.
- `compatibleComplement` fills the existing
  `KreinCompatibleDrazinComplement` field from the same sufficient condition.

Neither constructor assumes its projector-adjoint conclusion. These packets
do not construct a projective quotient, a conformal group action, or a Tomita
cyclic separating state. The separate realified Tomita polarization interface
is not automatically supplied by this Krein construction.

The subsequent [native projective boundary](KREIN_PROJECTIVE_BOUNDARY.md)
constructs the actual ray subtype in Mathlib's `Projectivization` and fills
the existing `DrazinKreinNullBoundary` packet, with representative recovery
and symmetry-preservation theorems.

## Indefinite regressions

The bounded regression uses the existing doubled real carrier with
`B(x,y) = x₁y₁ - x₂y₂` and the previously verified nonzero operator
`N(x₁,x₂) = (x₁+x₂,-x₁-x₂)`, where `N♯ = N` and `N² = 0`.

For `A = 1 + N` and `G = 1 - N`, the tests prove the Drazin equations at
index zero and derive `G♯ = G`. They also show that `G` does not commute with
the existing metric involution `spectral_epsilon`. Thus the result does not
depend on the additional symmetry-commutation condition used in the positive
kernel-comparison theorem. The distinct realified mirror `modular_j` satisfies
`modular_j * G * modular_j = A` in this example.

For the nilpotent operator `N` with Green operator zero and index two,
the boundary regression constructs the existing support packet and proves
that `(1,-1)` is a nonzero defect-supported null representative. The
defect-supported vector `(1,0)` is not null and is rejected. Hence the null
boundary is not silently identified with the whole generalized zero sector.

## Verification boundary

The two production modules and both regression modules pass isolated Lean
4.28.x compilation. The eleven axiom audits in `KreinDrazinGreenTests.lean`
and `KreinDrazinBoundaryRealizationTests.lean` contain only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx` or added axiom.
The new files compile without warnings. Rebuilding the existing boundary
owner's dependencies also succeeds, with unrelated pre-existing simplifier
warnings in `Volume/ConnesCocycle.lean` and
`Canonical/PhaseAxisCartanSymmetricLie.lean` left unchanged.

These modules use the same isolated Lean 4.28.x validation lane documented in
[the Green decomposition notes](KREIN_GREEN_DECOMPOSITION.md). The repository's
pinned Lean 4.28.1 build is not verified: its compiler rejects the available
4.28.x Mathlib cache. No dependency source, pins, or toolchain metadata are
changed by this construction.
