# Finite Gibbs centralizer contract

Status: v2 independently source-reviewed; locked v2 QA pending. V1 compiled,
but is superseded by the generic-identity reuse revision.
Imports the existing Canonical.FiniteMatrixGibbsFunctional owner; does not rebuild
its positive exponential density, normalized functional, or unit KMS equivalence.

Reuse: Mathlib Matrix.ext_iff_trace_mul_left/right supplies exact matrix
trace separation. Bounded native searches found no matching centralizer or
unit-defect equivalence. TracialCARDensity supplies the related commutator
defect identity for general tracial functionals, reused directly in v2 with
the native matrix trace; Mathlib supplies matrix separation.

Three heads in v2, all in InfoGeometry.Canonical.FiniteMatrixGibbsFunctional:
- trace_unit_right_annihilation_iff: arbitrary CommRing, finite matrix index; invertible weight only.
- weightedTrace_commutator_zero_iff: native complex weightedTrace, any density.
- weightedTrace_unit_defect_zero_iff: native unitImaginaryTimeAlgEquiv and weight.

No Nonempty, positivity, normalization, characteristic restriction, or assumed
separation field is required. No new carrier or conclusion bundle.

Boundary: External.Auto.KreinVacuumKMSBridge.DeltaRegularizedKMSContext assumes
regularized_defect_vanishes for all A and B, not merely selected observables.
In this finite invertible-density realization that assumption forces every
tested A to be a modular fixed point. The native KMS identity alone does not
imply that assumption. These statements neither reject other degenerate
functionals nor establish analytic strip or infinite-dimensional assertions.

For an actual Gibbs specialization use gibbsDensityUnit with the existing
Hermitian/Nonempty hypotheses. A named forwarding specialization is omitted.
The normalized functional is a nonzero scalar multiple by the partition
function; gibbsPartition_ne_zero is already native. No new normalization
construction or redundant corollary is included.
