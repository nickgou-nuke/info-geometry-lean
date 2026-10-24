# Completed complex GNS covariance — G-A contract

Status: uncompiled sandbox proposal, not independent AA/QA acceptance.
No live edits, dependency changes, tests or builds authorized here.

## Source-confirmed reuse and actual gap

`Canonical/FilteredGNSRepresentation.lean`, namespace
`CStarStateColimit.Native.FilteredGNS`, already constructs `preGNSMap`,
`preGNSLinearIsometry`, `gnsMap`, `gnsMapCLM`, `gnsMap_isometry`,
`gnsMap_toPreGNS`, and `gnsMap_intertwines`. Its input is the normalized
`CStarStateColimit.Native.State` restricted along a star algebra homomorphism.
Thus completed transport and whole-space intertwining are not new concepts
missing from the repository. Searches of native `PreGNS`/`gnsStarAlgHom`
consumers found this substantive existing implementation.

The narrow addition is an equivalence for arbitrary positive maps (including
zero and unnormalized maps), with an invertible star algebra map and explicit
pullback equality. Do not force arbitrary positive maps into normalized State.

Mathlib `Analysis/CStarAlgebra/GelfandNaimarkSegal` owns `φ.PreGNS`,
`toPreGNS`, `ofPreGNS`, `preGNS_norm_def`, `φ.GNS`, `leftMulMapPreGNS`,
and `gnsStarAlgHom`. Native `GNSMathlibBridge.cyclicVector` and
`PositiveLinearMapGNSVacuum.gnsVacuum` are the image of one.

## Contract and orientation

Assume `[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]`, positive maps
`φ ψ : A →ₚ[ℂ] ℂ`, `e : A ≃⋆ₐ[ℂ] A`, and `h : ∀ a, ψ a = φ (e a)`.
This is equality of functionals, not an assumed isometry or intertwiner.
The existing `InfoGeometry.Modular.PositiveStatePullback.pullback` supplies
the actual positive pullback along `e.toStarAlgHom`; its `pullback_apply`
gives the compatibility by `rfl`. No duplicate pullback definition is added.

Construct `ψ.PreGNS ≃ₗᵢ[ℂ] φ.PreGNS`, taking `ψ.toPreGNS a` to
`φ.toPreGNS (e a)`. Norm equality follows from the GNS quadratic form and h.
Construct `U : ψ.GNS ≃ₗᵢ[ℂ] φ.GNS` on the existing mathlib completions.
Expose representative and inverse-representative equations, vacuum preservation,
and `U (ψ.gnsStarAlgHom a x) = φ.gnsStarAlgHom (e a) (U x)` for every x.

## Completion constraint

PreGNS is only seminormed: never install a fake NormedAddCommGroup instance.
In the pinned `Analysis/Normed/Operator/Extend`, `LinearIsometry.completion`
requires a normed target before completion and is unsuitable directly here.
Instead compose the pre-isometry with `Completion.toComplₗᵢ` into φ.GNS,
then use `LinearIsometry.fromCompletion`. Do the same with the inverse into
ψ.GNS. Prove both inverse laws by `Completion.induction_on`; continuity
extends equality from representatives. Use the same density argument for
whole-space representation intertwining. No replacement Hilbert carrier,
no structure containing the desired conclusions, no new analytic hypothesis.

## Scope and acceptance

No normalization, faithfulness, or state invariance is required. The vacuum
need not have unit norm. This transports between two GNS spaces, not a
same-state implementation without an invariance hypothesis. Inner-unitary
specialization uses native `Unitary.conjStarAlgAut`; it needs no new carrier.
No KMS or Tomita conclusions are claimed.

Candidate import surface: `InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum`,
`InfoGeometry.Modular.PositiveStatePullback`, and
`Mathlib.Analysis.Normed.Operator.Extend`.
Parent owns promotion, independent AA, and locked kernel/axiom/warning checks.

Candidate declarations: `preEquiv`, its forward/inverse representative rules,
`forward`, `backward`, `forward_coe`, `backward_coe`, `backward_forward`,
`forward_backward`, `completedEquiv`, its forward/inverse representative rules,
`completedEquiv_vacuum`, and `completedEquiv_intertwines`, all in
`InfoGeometry.OperatorAlgebra.CompletedGNSCovariance`. The bundled equivalence
is a standard mathlib map with inverse laws proved from density, not a new
carrier or a record assuming the target theorem.

## V2 compatibility delta

V2 is a standalone copy of v1 plus the import
`InfoGeometry.Canonical.FilteredGNSRepresentation` and exactly one theorem,
`completedEquiv_eq_filteredGNSMap`. V1 is preserved for its active QA run.
The two candidates declare the same earlier names and are alternative versions;
do not import or concatenate both into one Lean environment.

For `ω : CStarStateColimit.Native.State A`, specialize ψ to
`(ω.restrict e.toStarAlgHom).functional`. The compatibility hypothesis is
`fun a => State.restrict_apply e.toStarAlgHom ω a`. The new theorem equates
`completedEquiv ... x` with `FilteredGNS.gnsMap e.toStarAlgHom ω x` for EVERY
completed vector x, not merely representatives. Its proof uses closed equality
of continuous maps and completion induction, reducing on representatives to
`completedEquiv_toPreGNS` and `FilteredGNS.gnsMap_toPreGNS`.

No new carrier, pullback, normalization assumption on the general construction,
or changes to v1 statements/proofs. Existing normalized-state clients keep their
native map; the theorem identifies this proposed invertible generalization with
that map. V2 has not been compiled. At creation no v1 QA diagnostics had been
forwarded; parent retains responsibility for applying those before promotion.
