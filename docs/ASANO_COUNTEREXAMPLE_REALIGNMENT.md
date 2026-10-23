# Asano–Ruelle counterexample realignment

## Ground-truth contract

The carrier is `ℂ`, with separately affine polynomial
`Φ(z₁,z₂) = A + B*z₁ + C*z₂ + D*z₁*z₂`, contraction `A + D*z`,
and forbidden set `{z | ∃ u ∈ K₁, ∃ v ∈ K₂, z = -(u*v)}`.
This is the actual complex-polynomial problem, not an operator-algebra proxy.

Two different failures of the unrestricted statement occur in maintained source:

- `AsanoRuelle/UnrestrictedFalse.lean`,
  `InfoGeometry.AsanoRuelle.unrestricted_asano_contraction_statement_false`,
  uses `K₁ = univ`, `K₂ = {0}` and a vacuous zero-freeness premise.
  `Analysis/AsanoRuelleObstruction.lean` gives the corresponding sign-variant
  example. `AsanoRuelle/AsanoRuelleCounterexample.lean` re-exports the first result.
- `Canonical/AsanoRuelleCounterexample.lean` uses
  `K₁ = {z | z ≠ 0}`, `K₂ = ∅`, `Φ = z₁*z₂ - 1`.
  The zero-free domain contains `(0,0)`, both sets exclude zero, and the
  contraction has a root at `1` outside the empty forbidden product.
  This example does not satisfy closedness of `K₁`.

## Existing constructive alternative

`InfoGeometry.Canonical.LeeYangAsanoNativeCore.asano_contraction_full_of_topological_combined`
in `Canonical/LeeYangAsanoFullReduction.lean` proves:

If both forbidden sets are closed and exclude zero, at least one is bounded,
and `Φ` is zero-free on their complementary product, then `A + D*z ≠ 0`
whenever `z ∉ -(K₁K₂)`.

Its proof handles `D = 0` and `AD - BC = 0` algebraically. The remaining
branch uses `AsanoRuelleSymmetricEndpoint.asano_endpoint_disjunction_combined`
and the existing endpoint-to-root localization. It does not assume the
contraction theorem, a source-claim proof, or an endpoint certificate.
`LeeYangAsanoClosedBoundedNative.source_claim_closed_bounded_native` is the
corresponding both-bounded theorem in the digest's polynomial carrier.
These proofs are reused rather than copied into new theorem wrappers.

## Remaining scope

`InfoGeometry.AsanoRuelle.CorrectedAsanoRuelleClaim` is a proposition definition,
not a proof. It asks for contraction with closed, origin-excluding sets without
boundedness. The full-reduction owner's
`asanoNondegenerateTopological_iff_asanoRuelleClosed` proves an equivalence
between two remaining statement surfaces; it does not supply either side.
The explicit-scale route also requires boundedness of the second forbidden set.
The inspected routes do not close the case where both sets are unbounded.
This record therefore classifies the unrestricted counterexamples and records
an established positive replacement, while retaining that broader proof debt.

## Verification

`Canonical/AsanoCounterexampleRealignmentAudit.lean` requests axiom reports for
the two counterexample owners, the proved combined-bounded contraction,
the both-bounded source theorem, and the conditional equivalence.
The parent locked build passed (8970 jobs); all five reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. Strict screening found zero
traps and `git diff --check` passed. The log is
`/tmp/asano-realignment-build.log` (28 dependency warning lines).
Independent A-A Poincare passed both files against their owners.
Independent QA-A Popper returned `ACCEPTED_WITH_LIMITED_SCOPE` after a second
locked build (8970 jobs), five standard-axiom reports, zero-trap screening,
diff checks, and owner inspection. Its log is `/tmp/asano-realignment-qa.log`.
No warnings occurred in the new audit file. Neither this targeted audit nor
the existing bounded-set theorem establishes repository-wide completion.
