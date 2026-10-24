# Reviewed existing constructive replacements

This batch classifies three actual counterexample families from the all-folder
inventory. No duplicate production theorem or replacement carrier is needed.
The records below distinguish the failed claim from the existing proved
canonical alternative. Independent semantic review passed for these three
families and the precise hypotheses recorded below.

## Oblique idempotents and Gramian cross terms

Owner: `Canonical/GramianInverseContracts.lean`, namespace
`InfoGeometry.Canonical.GramianInverseContracts`.

`oblique_idempotent_counterexample` uses the actual real matrix [[1,1],[0,0]]:
operator cross-Gramians vanish although the spectral projector is not symmetric.
The exact replacement is `projector_cross_zero_iff`: for an idempotent e in a
star ring, e(1-star e)=0 iff star e=e. It tests the projector before multiplication
by A loses information. `orthogonal_split_cross_zero` supplies the forward
operator consequence when the idempotent is self-adjoint and commutes with A.
`mp_from_left_gramian_drazin_one` separately constructs a Moore-Penrose inverse
from a symmetric index-one Drazin witness of the left Gramian. It does not prove
existence of that witness, or a general reverse-order inverse law.

## Normalization and pooling

Owner: `Probability/GromovPermutationNormalization.lean`, namespace
`InfoGeometry.Probability.GromovPermutationNormalization`.

`normalization_non_additive_counterexample` disproves unweighted additivity.
`normalization_sum_eq_mass_mixture` proves the exact mass-weighted identity for
finite real families, provided zero mass implies zero numerator.
`normalization_pooled_nonnegative_weights` derives that compatibility for
nonnegative component weights. `mass_mixture_weights_probability` additionally
requires nonnegative masses and positive total mass to make the mixture weights
sum to one. The pooling identity itself does not require positive total mass;
it uses Lean's totalized division. These are finite algebraic statements, not
measure-theoretic limit or concentration results.

## Attention coordinate identifiability

Owner: `Routing/AttentionInteriorFiber.lean`, namespace
`InfoGeometry.Routing.AttentionInteriorFiber`.

`collinear_counterexample` gives distinct strictly positive normalized rows
with the same fixed-value readout. `unique_probability_coords_at_positive_iff`
characterizes uniqueness at a strictly positive normalized row exactly by
AffineIndependent of the full indexed value family.
`vectorSpan_probabilityFiber_eq_ker` identifies the fiber direction space with
the homogeneous decoder kernel; `fiber_finrank_eq_card_sub_rank` adds the finite
output-index hypothesis and computes its dimension. This is a fixed-value
coordinate theorem, not identifiability of all neural-network parameters.
The strict-positive-row hypothesis is essential to the stated characterization;
no boundary-simplex converse is claimed.

## Scoped kernel verification

`Canonical.CounterexamplePositiveBatchAudit` imports the three existing owners
and prints the transitive axioms of twelve selected declarations. The parent
locked build completed successfully (8941 jobs, exit 0); evidence is in
`/tmp/counterexample-positive-batch-audit.log`. The independent replay log
`/tmp/counterexample-positive-batch-qa.log` also records successful completion
and lock release (QA session 52901, terminal exit 0). Independent acceptance
passed with limited scope: all twelve axiom reports are allowlisted, with union
`propext`, `Classical.choice`, `Quot.sound`. There are no audit-file warnings
and the strict screen reports zero traps. Existing owners and dependencies
still emit warnings.
These logs are session-local evidence. This batch neither modifies the three
production owners nor certifies the complete counterexample inventory.
