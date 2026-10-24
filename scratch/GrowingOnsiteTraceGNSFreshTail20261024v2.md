# Completed geometric onsite norm bound — v2 contract

Candidate: `GrowingOnsiteTraceGNSFreshTail20261024v2.lean`.
Source-only, uncompiled; independent AA and serialized QA required.
Pending family dependency: `InfoGeometry.Canonical.GrowingOnsiteTraceGNSFamily`
(the frozen family v2 is awaiting QA). Norm extension imports the promoted
`InfoGeometry.Canonical.FilteredCompatibleOperatorNorm`.

All v1 faithfulness, fresh-tail action, geometric-weight, and stage-norm proofs
are retained unchanged. No new carrier, operator, or assumed norm bound is added.

Two added declarations:

- `onsiteCompletedOperator_norm_le`: for actual weights w with summable absolute
  values, the existing completed onsite operator has norm at most
  `2 * ∑' j, |w j|`. The family bound is definitionally this quantity.
  Nonnegativity follows from `tsum_nonneg` and `abs_nonneg`; the inequality
  uses native `FilteredCompatibleOperatorColimit.completedOperator_norm_le`,
  whose proof extends the actual algebraic bound by completion density.
- `geometric_completedOperator_norm_le_two`: specialize that inequality to
  the existing weights `(1/2)^(n+1)`, using the proved absolute sum equality 1.

This is the SAME completed operator as `geometric_completed_fresh_ne_zero`:
nonzero fresh-tail action at every stage and norm at most two coexist for one
concrete nonterminating family. No claim of coupled interaction, independent
fresh images, or unboundedness is made. No live edits, builds, tests, or budget
changes. Frozen v1 is preserved.
