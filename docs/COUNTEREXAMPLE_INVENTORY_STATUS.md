# Counterexample inventory status

The active objective remains repository-wide discovery, semantic review, and
constructive mathematical replacement of counterexamples. No completion claim
is supported by the present lexical inventory or by individual passing builds.

## Creation-only vacuum contract: accepted (2026-10-24)

Removed the contradictory Witt pairing interface and the misleading Cartan
impurity predicate from WittPureSpinorVacuum. The replacement proves the
creation-sheet vacuum kernel is zero over an arbitrary field; positive rank
implies failure of full creation-sheet annihilation. Audit examples distinguish
this from genuine full Chevalley purity at rank five. Parent session 9349
passed (3,121 jobs), five axiom reports, three examples, zero own warnings and
traps. Final semantic review passed. Independent QA8153 passed (3,228 combined
jobs, nine axiom reports, five examples, zero own warnings).
See `WITT_VACUUM_CONTRACT_REPAIR.md`.

## Drazin shell self-adjointness: accepted (2026-10-24)

The native finite and all-index shell families are simultaneously self-adjoint
exactly when the complementary projection is self-adjoint. Parent session
42077 passed (3,182 jobs, exit 0); semantic review passed, strict screening
found zero traps. Independent QA8153 passed alongside the vacuum audit,
including four Drazin axiom reports and two examples, zero own warnings.
Final semantic review passed.
See `DRAZIN_SHELL_SELFADJOINT_CRITERION.md`.

## Fixed-pairing torsion and reflection boundaries: accepted (2026-10-24)

The exact two-torsion cancellation criterion has a native rank-one bilinear
converse and ZMod6 counterexample. Independent QA46921 passed (8,926 jobs,
exit 0), five axiom reports and two examples. The separate matrix reflection
boundary QA32658 passed (8,925 jobs, exit 0), five axiom reports and two
examples. Both have zero own warnings/traps; semantic review passed and the
NullEigenspace prose corrections are closed. See `PEIRCE_REFLECTION_INTAKE.md`.

## Quadratic Arnold numerator: accepted (2026-10-24)

The full ambient polynomial numerator now retains the original coefficient
counterexample and proves vanishing displacement minors from full vanishing
under the nonzero second-quadric hypothesis. Parent session 54949 passed
(3,097 jobs, exit 0). Necessity QA session 97998 passed (3,098 jobs, exit 0). The converse and
exact iff now compile in `QuadraticArnoldVanishing`, parent session 54056
(3,098 jobs, exit 0). Independent semantic review passed; full-classification QA session 50995
passed (3,099 jobs, exit 0), ten standard-axiom reports, three examples,
zero own warnings and traps.
See `QUADRATIC_ARNOLD_NUMERATOR.md`.

## Hyperbolic parameter and generator boundary: accepted (2026-10-24)

The integral hyperbola has only trivial boost parameters. Actual rational
matrix witnesses verify the corrected split-generator inverse, a nontrivial
moving idempotent and negative displacement square, and refute the proposed
elliptic-generator inverse. Independent QA session 64735 passed (8,925 jobs,
exit 0), eight axiom reports, two examples, zero source warnings and traps.
See `HYPERBOLIC_PEIRCE_INTAKE.md`.

## Finite GNS quotient reconstruction: accepted (2026-10-24)

`OperatorAlgebra/FiniteGNSQuotientReconstruction.lean` identifies the actual
first-column quotient with the existing two-component complex vector model,
intertwines the action, preserves its pairing, and recovers matrix entries
from the action. The resulting representation is injective even though the
class map is not. Semantic review and strict screening passed. The repaired owner and companion audit passed combined build session 32686
(3,198 jobs, exit 0). Independent kernel QA session 25438 passed (3,198 jobs, exit 0); across both batches, eleven axiom reports, six examples, and both noncommuting witnesses passed with zero own-module warnings and zero traps.
See `FINITE_GNS_QUOTIENT_RECONSTRUCTION.md`.

## Normalized MP Dirac self-adjointness: accepted (2026-10-24)

`Core/NormalizedDiracSelfAdjoint.lean` proves the exact criterion
`IsSelfAdjoint (normalizedDirac a m) ↔ m = star a` for a square-zero MP pair,
reusing native support-compression theorems. Semantic review passed and strict
screening is clean. The companion audit preserves the existing scaled-step
counterexample. The owner compiled in session 17727. The corrected companion audit passed combined session 32686
(3,198 jobs, exit 0). Independent kernel QA session 25438 passed (3,198 jobs, exit 0); across both batches, eleven axiom reports, six examples, and both noncommuting witnesses passed with zero own-module warnings and zero traps.
See `NORMALIZED_DIRAC_SELFADJOINT.md`.

## Cole–Fury aggregate readout fibers: accepted (2026-10-24)

`OperatorAlgebra/ColeFuryReadoutFibers.lean` classifies the exact fibers of
`quadrantReadout`, parameterizes its kernel by four contrasts, and reconstructs
the input from its aggregate representative plus those contrasts. The native
32×32 matrix readout and original noninjectivity witness are retained.
Parent session 50772 passed (3,097 jobs, exit 0); semantic review passed.
Independent kernel QA session 95012 passed (3,098 jobs, exit 0), with seven
standard-axiom reports, two examples and zero traps.
See `COLE_FURY_READOUT_FIBERS.md`.

## Incoming double-shear square: correction accepted (2026-10-24)

`Canonical/ReflexiveDoubleShear.lean` corrects the false Stream 4 square law
and characterizes when the old law holds. Native integer matrices refute it.
Both owner and audit compiled in session 64079, whose combined command failed
on an unrelated Jones bridge. Independent targeted QA session 42099 passed:
8,954 jobs, exit 0, three standard-axiom reports, two examples and zero traps.
See `REFLEXIVE_DOUBLE_SHEAR_CORRECTION.md`.

## Jones phase/permutation replacement: accepted (2026-10-24)

The existing nonfactorization counterexample is grounded in the actual
presented B3, Jones GL8 representation, and permutation shadow. The new modules construct a phase character and signed permutation action.
The full factorization and exact phase criterion on permutation fibers compiled
in parent session 35628 (9,298 jobs, exit 0). Independent semantic review
passed; independent kernel QA session 37195 passed (9,278 jobs, exit 0,
six standard-axiom reports, two examples and zero traps). The header-only
CAPA was independently closed. See `JONES_PHASE_PERMUTATION_WORK.md`.

## Two-probe fibers and reconstruction: accepted (2026-10-24)

`Synthesis/ThreeProbeReconstruction.lean` classifies every invisible matrix
for the existing two probes, gives exact fibers, and reconstructs the full
matrix from the owner's three probes. Semantic AA and strict screening passed.
Parent audit session 76349 passed (3,136 jobs, exit 0, three examples and
seven standard-axiom reports). Independent QA session 33650 passed with
the same job/example/axiom counts and exit 0 (`/tmp/three-probe-qa.log`).
See `THREE_PROBE_RECONSTRUCTION.md`.

## Ordered Pauli factorization: accepted (2026-10-24)

`Bridge/OperatorPauliFactorizationCriterion.lean` gives an exact four-condition
commutation criterion for the existing ordered channel, strengthening its
pairwise-commuting sufficient case. Parent audit session 56200 passed:
3,095 jobs, exit 0, three examples and three standard-axiom reports.
Semantic AA and strict screening passed; independent kernel QA session 17128
passed with 3,095 jobs and exit 0 (`/tmp/pauli-criterion-qa.log`).
See `OPERATOR_PAULI_FACTORIZATION_CRITERION.md`.

## Chiral adjugate factorization: accepted (2026-10-24)

`Canonical/OperatorChiralFactorizationCriterion.lean` replaces sufficient-only
commutation assumptions by an exact iff, allowing diagonal commutators to
cancel. It includes the native associative OperatorZorn specialization.
Parent locked audit passed (session 38884, 8,930 jobs, exit 0; three examples,
three standard-axiom reports). Semantic AA and strict screening passed.
Independent combined QA session 10916 passed: 8,941 jobs, exit 0; fourteen
standard-axiom reports and nine examples across this and the next two batches.
See `OPERATOR_CHIRAL_FACTORIZATION_CRITERION.md`.

## Scalar–bivector plane classification: accepted (2026-10-24)

`Clifford/BivectorPlaneIdempotents.lean` strengthens the native bivector
half-projector obstruction to a full classification of real combinations
`a • 1 + b • J`, using Mathlib's explicit complex algebra embedding for
`J*J=-1`. Semantic AA and strict screening passed. Parent locked audit passed
(session 60716, 3,131 jobs, exit 0; five standard-axiom reports and three
examples). Independent QA session 10916 passed as recorded above.
See `BIVECTOR_PLANE_IDEMPOTENTS.md`.

## Graph-chart kernel fibers: accepted (2026-10-24)

`SuperGrassmannian/GraphChartReductionFibers.lean` classifies the exact
information loss illustrated by `GraphChartOddRegression.reduction_not_injective`.
Two extended graph submodules agree iff each coefficient difference maps to
zero. For nonempty ungraded frames, faithfulness is equivalent to injectivity
of the ring map; the graded corollary concerns the actual homogeneous chart
points without asserting this stronger faithfulness equivalence.
Parent owner/audit builds passed (1404/1853 jobs), with six standard-axiom
reports and three examples. Semantic AA and strict screening passed;
independent kernel QA session 10916 passed as recorded above.
See `GRAPH_CHART_REDUCTION_FIBERS.md`.

## Accepted positivity-domain completion (2026-10-24)

`Physics/CobaltPositivityCriteria.lean` classifies global nonnegativity of
the existing beta and gamma angular models. This completes sufficient
conditions around the existing anisotropy/reflection counterexample and
negative-intensity witness; it does not refute those sufficient conditions.
The companion audit supplies four examples and three axiom requests.
Semantic AA passed; repository license headers were corrected as requested.
Parent kernel verification passed (1960 jobs, exit 0; three standard-axiom
reports and four examples). Independent kernel QA passed in combined session
38772 (3195 jobs, exit 0; `/tmp/cobalt-projection-final-qa.log`).
See `COBALT_POSITIVITY_CRITERIA.md` for the precise contract.

## Accepted projection-difference classification (2026-10-24)

`Singular/ProjectionDifferenceTripotence.lean` proves the exact ring criterion
`(p-q)^3 = p-q ↔ p*q*p = q*p*q` for idempotents, and its equivalence to
commutation for C-star projections. It specializes to native Moore–Penrose
supports and preserves the original rational MP counterexample. Parent and
independent kernel audits passed; combined QA session 38772 exited 0.
See `PROJECTION_DIFFERENCE_TRIPOTENCE.md` for scope and evidence.

## Completed traversal evidence (2026-10-23)

The long-running inventory command completed with exit code 0. Its JSON result
was inspected after termination, not inferred from a running process or plan.
The result is a navigation artifact, not a Lean parser or semantic audit.

- Result path: `/tmp/counterexample-inventory-v2.json` (ephemeral, not committed).
- SHA-256: `91d7354afe6c8cbf64e0aa563e75f87be7196438e684932c07823f41b18abe2c`.
- Physical Lean files recorded: 479,009.
- Lexical candidate rows: 340,316.
- Read/decode errors recorded: 0.
- Recorded provenance `dependency-or-build`: 151,826 files.
- Recorded provenance `external-ref`: 255,701 files.
- Recorded provenance `generated-artifact`: 9,434 files.
- Recorded provenance `other-review-required`: 8,753 files.
- Recorded provenance `repo-owned`: 50,765 files.
- Recorded provenance `runtime-state`: 2,530 files.

Exclusions reported: symlink: 4,692, git-metadata: 254.

This run included hidden/ignored physical folders, dependency/build trees,
and external references. Symlinks were not followed and Git metadata was
excluded. Copies, historical trees, and dependency sources are separate
records; the file total is not a count of unique maintained theorem owners.
The scanner source-at-launch hash was not recorded, so the result is not a
reproducible immutable source snapshot. Concurrent edits mean recorded file
hashes must be compared against current owners before each review.

## Limits and next work

Negative hypotheses can produce false positives. Indirect counterexamples,
unnamed declarations, and declarations without negative lexical markers can
be missed. Binder defaults can truncate the lexical header scan. Therefore
this traversal does not establish that every counterexample has been found.
The maintained all-folder entrypoint is
`tools/quality/counterexample_inventory_all_folders.py`.

Each selected candidate still requires reading the actual definition, theorem,
imports, and consumers. Record an existing positive replacement when one is
already proved; do not duplicate it. Otherwise formulate a carrier-preserving
canonical alternative, prove it, and run independent review and locked checks.

Recent completed replacements have separate source-backed records:
`BOUNDARY_FIBONACCI_SYLVESTER_REALIGNMENT.md`,
`REFLECTION_ZERO_COUNT_REALIGNMENT.md`, `BINARY_CHART_CURVATURE_REALIGNMENT.md`,
and `CAUSAL_BALANCE_REALIGNMENT.md`. These are local results, not evidence that
the remaining candidate rows have been classified or discharged.

Further source-backed local replacements (2026-10-24):

- `CUNTZ_POSITIVE_GNS_CONTRACT.md`: the positive functional on the corrected
  conjugate-star carrier yields a GNS state, a native complex radical pairing,
  and compatible quotient actions. This does not provide positivity for the
  legacy scalar-fixing complex involution.
- `ZORN_OPERATOR_DEFECT_CONTRACT.md`: left multiplication has an exact
  associator defect, replacing the false general multiplicativity claim.
- `ZORN_TERNARY_DERIVATION_REALIGNMENT.md`: the existing standard-derivation
  bracket satisfies the ternary derivation identity. The raw associator's
  Filippov obstruction remains valid; no total alternation is claimed for
  the corrected operation.

These records reuse inspected owners and have scoped kernel and independent
verification evidence. They do not classify the other inventory rows.

`FINITE_CUNTZ_REFINEMENT_REALIGNMENT.md` further records the finite-stage
replacement: existing rectangular branches determine a unique amplification
of each operator. The exact two-branch intertwining characterization is
kernel checked and independently reviewed; it does not assert finite square
Cuntz isometries or infer a continuum representation from finite dimensions.

Additional reviewed families (2026-10-24):

- `ZORN_MAJORANA_COLOR_CONTRACT.md`: corrected native left grading, signed CAR,
  Majorana parity/rotations and collective squares. Forty theorem heads were
  independently kernel audited. The central CAR bracket does not establish
  the proposed gl(3|1) classification.
- `CYCLOTOMIC_PEIRCE_IMAGE_REALIGNMENT.md`: the conditional ambient-unit
  obstruction is retained. Existing native corner reconstruction yields an
  exact unique-preimage iff entrywise-support theorem for the same Fourier
  projector family. Five new/existing declaration audits passed independently.

These are source-reviewed entries, not evidence of exhaustive semantic coverage.
The broad staged-source gate returned failure on unrelated staged sources and
a changed index snapshot; no whole-worktree release claim is made.

Further existing-owner review:

- `COUNTEREXAMPLE_EXISTING_POSITIVE_BATCH.md`: three families accepted after
  independent source review and a twelve-declaration kernel/axiom audit:
  projector-level obliqueness criteria, mass-weighted finite normalization,
  and affine-independent identifiability at positive attention rows.
- `FREUDENTHAL_CONTACT_REALIGNMENT.md`: the mixed-triple obstruction has an
  existing symplectic-triple replacement and corrected contact Lie bracket
  on the existing carriers. Parent locked compilation of the twelve-head
  audit passed; independent acceptance is recorded in that family document.

These dispositions preserve the valid counterexamples and identify their
constructive replacements. They do not count lexical candidates as resolved
without source review, or establish that the inventory is exhaustive.

`KREIN_SPIN_EXISTING_REPLACEMENTS.md` records the next source-reviewed batch:
indefinite kernel conditions and explicit null contraction, exact Krein-trace
correction, and fixed-Cartan phase classification with unitary realization.
The parent audit build and independent semantic review passed. Final independent
QA replay is pending behind another live build; do not mark this batch fully
accepted until the recorded verification finishes.

`SCALED_EULER_NN_REALIGNMENT.md` records a new constructive replacement for
the convex Euler-mode NN obstruction: an exact scale criterion and a sharp
uniform cutoff threshold. Four new theorems, two original obstruction heads,
and two exact numeric examples passed the parent kernel audit. A final
independent replay after removing one unreachable tactic remains outstanding.
The result concerns the existing algebraic derivative slots, not analytic
self-concordance of zeta or an infinite Euler product.

`DOUBLED_SHEAR_SYMPLECTIC_REALIGNMENT.md` records a new carrier-preserving
alternative for the non-Krein-isometric shear: the same native matrix action
scales the existing chiral alternating form by its determinant. Four new
theorems include determinant-one preservation, the shear specialization, and
the converse on a nontrivial coefficient space. Parent kernel/axiom audit and
independent semantic review passed; final QA acceptance remains pending.

Update: independent combined QA session 69457 accepted the shear, scaled Euler,
and Krein/spin batches with limited scope (terminal exit 0, 8980 jobs). All
37 printed axiom reports have the standard three-axiom union; there are no
scoped-source warnings. Earlier pending statements above are superseded for
these three batches. The Euler strict-screen unused-hypothesis flags were
reviewed as implicit `positivity` uses, documented in its family record.
Repository-wide discovery and semantic coverage are still incomplete.

`IS_BARRIER_DERIVATIVE_BRIDGE.md` closes the adjacent scalar calculus gap:
three actual `HasDerivAt` slot identities and three trajectory-dissipation
theorems reuse the existing logarithmic barrier. Independent semantic review
and final QA session 70798 passed (3772 jobs, six standard-axiom reports,
zero own-source warnings). This does not strengthen the Euler cutoff result
into a zeta or infinite-product theorem.

Next source-reviewed candidate: the nonmultiplicative weak functional in
`Streaming/WeakPropertySeparation.lean`, consumed by `TwoBoundaryWeakPristineChain`.
The existing `TwoBoundaryDyadCompression` provides the native normalized dyad
and compression identity. Proposed replacement: the multiplication defect is
exactly the weak value of `A * (1 - boundaryDyad p) * B`; characterize vanishing
for all left factors by preservation of the preselected line. These new
statements are pending proof, not accepted results. The old comment inferring
nonpositivity from nonmultiplicativity alone also needs a separate precise
positivity argument or wording correction.

Update: `WEAK_VALUE_MULTIPLICATION_REALIGNMENT.md` now records the completed
constructive repair. The exact complementary-dyad defect and all-left-factor
multiplicativity criterion are proved; the native preselected-line stabilizer
is a `Subalgebra` carrying a weak-value `AlgHom`. The original witness has
defect `-4` in the new regression example. Independent A-A and QA passed
(session 53912, 8944 jobs, eleven standard-axiom reports, zero new-module
warnings). The old unsupported positivity inference was removed from its
comment; no theorem was weakened. The earlier pending status is superseded
for this family. Broader inventory discovery remains incomplete.

`ANHARMONIC_SIX_PERMUTATIONS.md` records the constructive extension of the
puncture-translation obstruction: the existing exchange and inversion
permutations generate exactly six elements on the native punctured carrier.
Independent A-A and QA accepted the membership/cardinality proof and three
examples (session 86692, 3194 jobs, nine standard-axiom reports, zero own-source
warnings). This is not a modular action or a claim that all point orbits have
size six.

The new historical-synthesis intake is source-aligned in
`HISTORICAL_SYNTHESIS_SOURCE_ALIGNMENT.md`. It reuses existing constructive
owners while correcting the Jordan commutator sign and recording Drazin,
PowerMPFamily, associative-envelope, and algebraic-KMS scope. Independent
source-level review passed; no historical novelty or exceptional-algebra
classification is certified by that document. Exhaustive inventory coverage
remains outstanding.

`POSITIVE_ZERO_COLUMN_DEFORMATION.md` records a constructive extension of the
zero-column strict-positivity obstruction. For a strictly positive real
`2 × (n+2)` source matrix, appending a positive multiple of the last column
minus the first produces a strictly positive larger matrix; its zero-parameter
limit proves frontier membership in the ambient matrix chart. Parent audit
passed (session 50225, 8928 jobs, eight standard-axiom reports, three examples),
with independent semantic review accepted. Final independent kernel QA session
49681 also passed: eight standard-axiom reports, three examples, zero own-source
warnings, zero strict-screen traps, and clean scoped diffs. No assertion is made
about arbitrary nonnegative sources or quotient Grassmannians. Exhaustive
counterexample inventory and constructive realignment remain in progress.

`DIKIN_BARRIER_DERIVATIVE_BRIDGE.md` closes a consumer integration gap for the
already repaired nonlinear binary-barrier counterexample. The existing Dikin
metric is now proved to be the actual second derivative of its potential;
the global generalized curvature bound and exact standard squared-bound
region transport from the chart owner through an additive constant.
Independent A-A and QA accepted six new lemmas and three examples (QA session
53169, 8981 jobs, seven standard-axiom reports, zero own-source warnings).
This does not assert global standard self-concordance or construct a
Blahut–Arimoto contraction.

Next source-read residual: `Canonical.SplitCliffordSuperVirasoroModes`
already proves the shifted current nonzero and square-zero, repairing its
non-idempotence obstruction. Its `LG_defect` remains a defined residual;
the candidate exact evaluations are `[L0,G1] = -G1` and
`LG_defect = (-3/2) • G1`. The same current's existing `Hdiag_comm_Jplus`
suggests `Hdiag/4` for positive half-weight scaling. These candidate
evaluations are not yet kernel-checked; no super-Virasoro representation
claim follows merely from such finite scaling identities.

The finite scaling residual above is now implemented in
`Canonical.TwoModeCurrentScaling`: all diagonal generators are classified by
weight `d 2 - d 1`, the original `L0` has weight `-1`, the residual is exactly
`(-3/2) • G1`, and `Hdiag/4` gives opposite half-weights. Parent audit session
56044 passed (3100 jobs, nine standard-axiom reports, two examples), as did
independent semantic review and strict screening. Final independent kernel
QA session 68389 passed with nine standard-axiom reports, both examples,
zero own-source warnings, and clean scoped diffs; see
`TWO_MODE_CURRENT_SCALING_REALIGNMENT.md`.

Next source-read candidate: strengthen `CayleyHestenesGradedIntertwinerBridge`
from commutator-image annihilation to exact sector kernels. For its existing
datum, the proposed commutator kernel is `M.eigenspace (-1)` and the
anticommutator kernel is `M.eigenspace 1`. The native `wittGradedDatum`
has `M = diag(1,-1,-1,-1,1,-1,-1,-1)` acting on `Fin 8 → ℝ`;
`Pi.single 0 1` and `Pi.single 1 1` provide candidate nonzero sector witnesses.
The existing filtered-colimit datum uses the same generic structure.
These kernel and witness propositions remain unchecked, not accepted results.

Update: the preceding kernel candidate is now verified in
`Canonical.CayleyHestenesSectorKernels`, superseding its unchecked status.
The commutator and anticommutator kernels equal the native minus/plus
eigenspaces, and the original plain-intertwiner obstruction yields range
containment in the minus sector. Concrete eigenvector examples establish
both sectors nonzero. Independent A-A and QA passed (session 41717, 8933 jobs,
nine standard-axiom reports, four examples, zero own-source warnings and
strict-screen traps). See `CAYLEY_HESTENES_SECTOR_KERNELS.md` for exact scope.
No converse asserting existence of intertwiners was added. The broader
counterexample inventory remains incomplete.

The next source audit found three families already covered by constructive
owner results: Moore–Penrose similarity has the exact two-support Gram
commutation criterion; Dirac soldering has metric-twisted spinor exchange;
and incidence isotropy yields unitarity, with Hermiticity characterized by
a separate frame-skew identity. `Canonical.AdjointCovarianceRealignmentAudit`
checks seventeen existing declaration heads and two derived examples without
duplicating owner proofs. Parent locked session 3534 passed (3188 jobs,
standard foundational axiom union, zero new audit warnings). Independent
semantic and artifact review passed, as did independent kernel QA session
92533 (3188 jobs, all seventeen reports and both examples, zero audit-source
warnings, zero strict-screen traps, clean scoped diffs).
See `ADJOINT_COVARIANCE_REALIGNMENT_AUDIT.md` for hypotheses and scope.
Markov–Petz positivity was inspected but excluded from this batch because its
exact positivity-preservation iff and dedicated audit already exist.

`EmergentGeometry.HarmonicQuadraticRectangle` extends the existing rectangular
mean counterexample's correction to every field `Re(a*z²+b*z+c)`. Its average
on a centered rectangle with positive half-sides `w,h` is
`c.re+a.re*(w²-h²)/3`, and equals its center value iff `a.re=0 ∨ w=h`.
The owner proves harmonicity and uses the existing iterated interval integral.
Parent locked session 66904 passed (3547 jobs, eight standard-axiom reports,
three examples, zero new-source warnings); semantic review and strict
screening passed. Independent kernel QA session 11264 also passed with the
same eight reports and three examples, zero own-source warnings and traps.
This is a classification
within the specified polynomial family, not a square mean-value law for all
harmonic functions. See `HARMONIC_QUADRATIC_RECTANGLE_CONTRACT.md`.

Next source-read candidate: `Physics.BostConnesThermalTime` already proves
the circular `modularFlowCl11` additive and invertible, and proves its failure
of multiplication at `pi/4`. The proposed exact multiplicative-time criterion
is `Real.sin (2*t)=0`. It would classify the existing coordinate map, not
identify it with a C*-algebra modular flow. This candidate remains unchecked.

Update: the preceding circular-flow criterion is implemented in
`Physics.Cl11CircularFlowMultiplicativity`. Parent session 62346 verified
the sine-zero iff, integer-half-period iff, native `RingEquiv`, and explicit
identity-or-`e1Basis`-conjugation description. Seven axiom reports and four
examples passed. Two redundant tactics were then removed to clear four
linter warnings; final rebuild session 32032 is pending, followed by
independent kernel QA. Independent semantic review has passed. The earlier
unchecked status is superseded only to this stated verification extent.

Final update: cleanup parent session 32032 and independent QA session 50780
both passed (3096 jobs, seven standard-axiom reports, four examples, zero
source warnings). Strict screening and scoped diff checks passed. This
completes the scoped circular-flow classification; see
`CL11_CIRCULAR_FLOW_MULTIPLICATIVITY.md`.

Next source-read candidate: the positive sandwich `quantumShearSandwich`
in `Quantum.RelativeEntropyFlow` has a native maximally-mixed trace
counterexample at shear one, while similarity trace preservation is already
proved. Candidate constructive extension: exact maximally-mixed trace
`1+normSq(delta)/2`, and universal sandwich trace preservation iff `delta=0`.
These statements remain unchecked and do not assert that normalized
postselection is a linear trace-preserving channel.

Update: `Quantum.ShearSandwichTrace` now proves that candidate plus the exact
arbitrary-input trace correction and its vanishing iff. Parent session 85996
passed (8949 jobs, six standard-axiom reports, three examples, zero own-source
warnings). Independent semantic review and strict screening passed;
independent kernel QA session 61967 also passed (8949 jobs, six reports,
three examples, zero own-source warnings and traps, clean scoped diffs).
The examples include the preserved first
coordinate pure state at arbitrary shear, so no claim is made that nonzero
parameters change every input trace. See `QUANTUM_SHEAR_TRACE_CONTRACT.md`.
# Metric radical and positive trace-zero restriction

`QuantumContext/MetriplecticMetricRadical` extends the existing indefinite
coordinate form with five positive classification results: its exact radical
over a commutative ring, trace-zero bilinear and quadratic formulas, real
nonnegativity on that restriction, and self-nullity iff full radical membership.
The original ambient indefiniteness remains valid. Parent audit 74055 and
independent QA 32625 both exited 0 (865 jobs); six axiom reports and three
examples passed, with standard foundational axiom union and no source warnings.
See `METRIPLECTIC_METRIC_RADICAL_CONTRACT.md`. This scoped result does not
complete the repository-wide counterexample inventory.

# Weighted derivation exact criterion

The Euler Leibniz defect now has an exact native `OpDerivation` classification:
left weighting by K preserves Leibniz iff `[K,x]` annihilates every `D y`.
A right-invertible value of D makes this equivalent to centrality. The native
weighted derivation is constructed from the exact condition, and the existing
complex Euler owner is connected by its existing derivation equivalence.
Parent 44590 and QA 80708 exited 0 (8932 jobs), six axiom reports and three
matrix examples passed; standard foundational axiom union, zero own warnings.
See `WEIGHTED_DERIVATION_CRITERION.md`. Whole-repository completeness remains open.
