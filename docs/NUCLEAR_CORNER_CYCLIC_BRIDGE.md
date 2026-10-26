# Nuclear corner and additive cyclic quotient: theorem contract

Intake: user-supplied `NuclearCornerCyclicBridgeDraft`, 2026-10-26, following
PR #220 at `677dc484eb8d23b7d00ff1924f7bc8fab50fb831`. The draft explicitly
said it was source-reviewed but not kernel-checked. Its three proposed claims
were: nonunital multiplicative descent through an additive commutator quotient;
centrality within P A P versus off-corner noncentrality; and the M3(Z) compressed
trace counterexample with P=diag(1,1,0), X=E02, Y=E20.

Source search at this commit did not locate the referenced imports
`Algebra.CyclicMatrixCurvature` or `TriZornTraceBoundary`, nor their named
CyclicModule/commutatorSpan API. No dependency on those unavailable owners is
asserted. The generic quotient is implemented directly with Mathlib Submodule
span/quotient and native NonUnitalRingHom, in Algebra/CyclicQuotient.

Existing owners: NuclearConfigurationOperatorLift supplies cornerLift,
cornerLift_mul and cornerLift_one; NuclearFiveGradeSolovievCommonCompression
supplies modelEmbed, modelReadout and idempotent modelProjection. The carrier
is the existing countable product, not a new finite replacement. PeirceDecomposition
and PeirceCompressionDefect already own decomposition and product-defect laws.
The added general two-off-block criterion requires no star or positivity.

Causal order: additive/multiplicative map -> commutator preservation -> span
inclusion -> quotient descent and uniqueness -> concrete nuclear specialization.
Idempotent -> unit in corner -> two-off-block commutation criterion -> scalar
commutator formula. Explicit finite matrices -> compressed commutator trace 1
-> failure of cyclicity for that compression functional -> impossibility of
factoring that functional through the additive cyclic quotient.

Boundaries: nonzero scalar noncentrality requires a nonzero scalar over a field
(or an explicit no-zero-smul-divisor hypothesis); the draft prose omitted it.
The generic cyclic map need not be injective even when the algebra map is.
The M3(Z) counterexample disproves the compression formula, not all extensions
of the 2D trace: ordinary full matrix trace does extend the corner trace there.
No global trace, full-carrier Born rule, or TriZorn identification follows.
The finite counterexample is exactly the user's requested algebraic obstruction,
not a surrogate for the infinite nuclear carrier.

## Validation

`[kernel_verified]`: 21 new theorem declarations across four modules.

* Lean 4.34.1, pinned mathlib
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
* The repository-root prescribed locked build was retried and stops at the
  absent `external_refs/atlas-lean` package before compiling the target.
* An isolated Lake project uses this repository's actual Lean source and the
  exact pinned mathlib. Under `/tmp/info-geometry-build.lock`,
  `lake build InfoGeometry.Physics.NuclearCornerCyclicBridge InfoGeometry.Algebra.CornerCompressionTraceCounterexample`
  succeeds (8952 jobs). No new-module warnings; inherited-owner warnings remain.
* A separate locked `lake env lean` import/axiom check covers all 32 new
  declarations, including definitions and abbreviations. The axiom union is
  exactly `propext`, `Classical.choice`, `Quot.sound`.
* `proof_proxy_staged_gate.py`, placeholder scan and `git diff --cached --check`
  pass. The semantic-vacuity gate exits successfully with five `trivial_surface`
  warnings: `map_class`, `desc_class`, `scalar_commutator`,
  `scalar_central_in_corner`, `cornerCyclicMap_class`. These expose native
  quotient evaluation or scalar algebra laws, rather than assuming conclusions.
* Generation, semantic audit and acceptance use separate roles. No dependency
  pins or pre-existing theorem owners were changed. This is targeted validation,
  not whole-repository build or CI certification.

Checked source SHA-256:


* `CyclicQuotient.lean`: `e0a5eaa8ff2e9364e6d8682eee96498b6a6e5c490167f8c8a77901278ff284c0`.

* `CornerCentrality.lean`: `2b058785cf1a1f25562311531faa2014d7055e0c888417331346b7d8765fa8a6`.

* `NuclearCornerCyclicBridge.lean`: `5f4c9fec5ea5cbc7fc77d4070b99d0651bac641ba617f07091ae4987f77228a8`.

* `CornerCompressionTraceCounterexample.lean`: `0d061453eb0985484bc1092067dc560641bbe51ac0bab0dd996b611ba484b5b6`.
