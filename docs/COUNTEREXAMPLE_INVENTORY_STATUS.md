# Counterexample inventory status

The active objective remains repository-wide discovery, semantic review, and
constructive mathematical replacement of counterexamples. No completion claim
is supported by the present lexical inventory or by individual passing builds.

## NCG intake correction: Cuntz, stabilizer, and Lax claims (2026-10-28)

Three newly added NCG modules were checked against their current owners. Their
initial source did not compile and several docstrings overstated the formal
content. The modules now use narrower owner-aligned statements:

- `InfoGeometry.NCG.CuntzHoppingCantorLattice` reuses
  `InfoGeometry.NCG.CuntzSystem` and its `canonicalShift` rather than defining
  a second Cuntz-family record. It proves shift unitality, multiplicativity,
  star preservation, the generator intertwining identity, and orthogonality
  directly from the Cuntz relations. Finite binary-address prefixing is a
  separate `List Bool` operation; the module does not claim a Cuntz
  representation on the Cantor boundary. The completeness equation is an
  explicit Cuntz-system field, not an independently derived partition model.
- `InfoGeometry.NCG.GunaydinGurseySU3Stabilizer` now calls its predicate
  `FixesChosenImaginaryUnit`. The inspected carrier is the existing
  14-parameter family `Params = Fin 14 → ℝ` with the owner derivation map
  `zornG2Derivation`. The predicate is only the equation `D(e)=0`; the former
  “8-dimensional SU(3)” description and color triplet/antitriplet claims had no
  corresponding subalgebra, dimension, or representation theorem and have
  been removed. The remaining derivation and conjugation laws are inherited
  from the general owner theorems, while the scalar-coordinate statement is
  explicitly not described as pointwise fixation.
- `InfoGeometry.NCG.LaxPairIsospectralMassGap` no longer defines a residual
  using `L` in place of `dL/dt`, calls a reflexive equality an isospectrality
  theorem, or defines a gap as the difference of two identical maxima. It now
  proves `trace([P,L]) = 0`, the exact cyclic trace-power commutator
  cancellation `trace(L^k [P,L]) = 0`, and the finite-matrix equivalence
  `det L = 0 ↔ ∃ v ≠ 0, L v = 0` from Mathlib. No differentiable Lax flow,
  singular-value gap, or Yang–Mills mass-gap result is claimed.

The first locked build exposed missing/incorrect namespace and address-carrier
references in the Cuntz and stabilizer modules, plus a parser/proof issue in the
initial Lax module. After correction, the three owner targets built: the
Cuntz module passed in the 4,003-job run, the stabilizer module passed in the
same batch (its unrelated linter warnings remain), and the Lax module passed in
the 3,092-job run. The umbrella `InfoGeometry` build then passed all 28,117
jobs. That umbrella emitted the repository's existing warnings and a broad
audit report; it is not a warning-free build or a fresh exhaustive axiom audit.

The corresponding epistemic-compilation, anomaly-resolution, and Darwinian
codebase-epistemology skills already exist under `skills/`; this entry applies
their source-grounding rules. The broader counterexample inventory and
independent semantic QA remain open.

## Source-grounded candidate batch (2026-10-27)

A fresh run of `tools/quality/counterexample_inventory.py --json` scanned
47,911 Lean files and emitted 19,798 lexical candidate rows, with zero read
errors. The repo-owned rows comprise 31 countermodels, 353 obstructions,
64 identifiability boundaries, and 5,651 negative-boundary candidates. These
counts are lexical navigation data only:
declaration headers can extend across proof text to the next declaration, so
candidate labels require manual owner review.

The current scan was compared with the prior saved scan: it introduced no new
repo-owned candidate keys `(file, name, line)`. This is a delta observation,
not evidence that the existing rows have all been semantically reconciled.

Three concrete families were source-reviewed and replayed through the locked
Lake build. No replacement APIs were added because each owner already contains
the precise constructive statement:

- `Omega.CircleDimension.MultiPrimeSpectrum`: for distinct `p,q`, the support
  families `{{p},{q}}` and `{{p,q},∅}` have the same every-singleton spectrum,
  while their `{p,q}` values are respectively `0` and `1`. The owner also
  proves the exact piecewise formula for the second family. This `Finset`
  carrier counts distinct support types; the separate `Omega.Folding.Window6`
  `List` carrier retains repeated occurrences, so the two encodings have
  different multiplicity semantics. `Omega.CircleDimension.MultiPrimeSpectrum`
  and `Omega.CircleDimension.MultiprimeDivisibleSpectrumExplicit` built
  successfully (3,093 jobs, exit 0).
- `Omega.POM.A4TCyclotomicAdjacencyInjection`: the target expression with
  signs `1 - 2v - tv² - 2v⁴ + 2v⁵` is nonzero at the order-four cosine
  specialization. The owner proves the corrected identity
  `1 + 2v - tv² - 2v⁴ - 2v⁵ = 0` for every nonzero real `v`, and derives its
  paper specialization for natural `h ≥ 4`. The module built successfully in
  the combined 3,095-job POM build.
- `Omega.POM.A4TNewmanLinearResponseConstant`: the formula alone does not imply
  the recorded octic for `cStar`; `zStar = 2` is a concrete refutation. The
  owner proves the corrected conditional statement under `1 < zStar` and the
  Newman octic hypothesis, using an explicit elimination identity and a
  nonzero-denominator proof. Both POM modules built successfully (3,095 jobs,
  exit 0); this module emitted a deprecated-import warning and two
  unnecessary-sequence-focus warnings, so warning-free closure is not claimed.

These are kernel replay results, not independent semantic QA. The broad
inventory and independent review of these three families remain open.

## Additional source-grounded batch (2026-10-27)

Four more lexical candidates were traced to their owner statements and
consumers, then replayed in one locked build (8,985 jobs, exit 0):

- `Omega.RecursiveAddressing.PrefixSiteMinVisibleQuotient`: the counterexample
  refutes factoring through an arbitrary surjection merely because listed
  generators are killed (`pi = Prod.fst`, `phi = Prod.snd`, and `alpha = 0`).
  The owner’s canonical alternative is the quotient by the additive subgroup
  generated by the visible cocycle values; it proves pointwise vanishing and
  unique factorization for every homomorphism that kills those values. The
  file also contains a second, pointwise formulation in a nested namespace;
  the two formulations are not asserted here to be definitionally identical.
- `Omega.Conclusion.RanktwoSmithBlindclassBooleanPrimeblockTorsor`: the
  unqualified divisor-count formula fails at `(a,b)=(0,0)` because
  `Nat.gcd 0 0 = Nat.lcm 0 0 = 0`, so `h=0` and the two sides are `0` and `1`.
  The owner proves the corrected formula for positive `a,b`, reducing it to
  the count of unitary divisors of a nonzero natural number.
- `Omega.CircleDimension.ResidualEntropyLowerBound`: the finite-injection
  hypothesis alone does not imply the paper’s logarithmic bound when `k > r`;
  the concrete parameters are `(b,r,k,t,R)=(1,1,2,4,2)`. The corrected bound
  includes `k ≤ r` and `0 < t`, and derives the residual register capacity
  before applying `Nat.log`.
- `InfoGeometry.Convex.BinaryBarrierCoordinateHessian`: the nonlinear log-odds
  chart violates the squared standard self-concordance inequality at the
  explicit point whose trajectory value is `15/16`. The source proves the
  exact second-derivative defect
  `-4 * (2 * trajectory 1 0 ξ - 1)^2`, a chart-specific Hessian comparison,
  and the concrete violation. Its audit reports only the standard Lean
  axioms. The locked target was
  `InfoGeometry.Convex.BinaryBarrierCoordinateHessianAudit`.

This batch has kernel/build evidence only. It is not an independent semantic
audit, and it does not establish that the lexical inventory is complete.

## Jordan associator sign refutation (2026-10-27)

`InfoGeometry.Canonical.PeirceWeylExamples.source_jordan_sign_counterexample`
was traced to the actual unnormalized Jordan product `X ∘ Y = X*Y + Y*X`.
The rejected orientation is the reversed inner Lie bracket. The canonical
owner `InfoGeometry.Core.JordanMultiplicationClosure` proves the general
commutator action
`[L_s,L_t](x) = (s*t - t*s)*x - x*(s*t - t*s)`, and
`InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance` connects the
Jordan associator to the correctly ordered nested commutators. Its concrete
integer-matrix audit verifies both the equality and the sign refutation.
`InfoGeometry.Canonical.PeirceWeylExamples` and
`InfoGeometry.Canonical.UnifiedGeometryOperatorSignificanceAudit` built in a
locked run (9,296 jobs, exit 0); the build emitted warnings in imported files,
so this is not a warning-free claim. This sign family overlaps the earlier
Peirce–Weyl intake audit and is recorded as a cross-owner candidate, not as a
new theorem API.

## Fixed-metric projector covariance boundary (2026-10-27)

`InfoGeometry.Canonical.ConformalProjectorAgreement.moorePenrose_not_generic_similarity_equivariant_under_fixed_metric`
is a concrete shear counterexample for arbitrary similarity covariance when
the Euclidean metric is kept fixed. The actual Moore–Penrose replacement is
already proved in
`InfoGeometry.Canonical.MetricTransport.penrose_projectors_similarity_iff`:
under the actual source and target Moore–Penrose inverse hypotheses and an
invertible similarity, both support projectors transport exactly iff the
source range and co-range projections commute with the Gram element
`star g * g`. The five `shearCounterexample_*` declarations in the witness
file are supporting matrix equalities/inequalities (the shear image, inverse
identities, Drazin-vs-Euclidean-MP mismatch, and failed fixed-metric transport),
not five independent general counterclaims. The existing
`mismatch_transport_decomposition` separately isolates the fixed-metric tear
term. The exact criterion applies when both sides are actual Penrose
projectors. Both owner modules built successfully in the locked 3,180-job run;
a fresh replay also passed (3,180 jobs), with warnings from the imported
Moore–Penrose owner. No new bridge or duplicate theorem was needed.
The five lexical countermodel rows are the owner support declarations
`shearCounterexample_Aprime_eq`, `shearCounterexample_G_mul_GInv`,
`shearCounterexample_GInv_mul_G`,
`shearCounterexample_drazin_ne_euclideanMP`, and
`shearCounterexample_fixedMetric_MP_transport_fails`. The first three verify
the similarity witness and inverse, while the latter two establish the
Drazin/Euclidean-Moore–Penrose mismatch and failed fixed-metric transport; they
are evidence for one family, not five independent universal counterclaims.

## Split-octonion ordinary-matrix representation obstruction (2026-10-27)

The inventory's obstruction candidate
`InfoGeometry.Algebra.OctonionMatrixObstruction.no_injective_matrix_representation_of_zornMatrix`
is grounded in the actual custom `ZornMatrix ℝ` multiplication. Its proof uses
the generic theorem
`associative_of_injective_mul_map_to_semigroup`: any injective
multiplication-preserving map into an associative semigroup forces the source
multiplication to be associative. `ZornMatrix.nonassociative_witness` then
refutes the forced associativity. This rules out faithful multiplicative
embeddings into ordinary associative matrices; it does not rule out a linear
operator representation, a non-faithful map, or matrices carrying a transported
nonassociative product. The locked owner build passed (3,095 jobs, exit 0), with
pre-existing linter warnings in `ZornMatrix.lean`. The generic implication and
its concrete specialization already provide the canonical alternative, so no
duplicate theorem was added.

## WL multiplicity and inversion-orbit boundaries (2026-10-27)

Two further boundaries were checked against their owner definitions. In
`Canonical/InfoTreeColorRefinement`, the old “1-WL equivalence” profile used
existence of a neighbor of each color and discarded multiplicity. The finite
four-node witness in `InfoTreeColorRefinementCounterexamples` shows two sources
with the same support profile but outgoing color counts 1 and 2. The owner now
names this weaker relation `SameColoredNeighborSupport`; the separate
`DAG/DirectedLabeledWL` module gives a multiset-based structural refinement
and proves isomorphism invariance. Its graph record is explicitly only an
abstract finite-list model: adjacency consistency, acyclicity, actual Lean
InfoTree extraction, WL completeness, and hash collision-freedom are not
claimed.

`Analysis/MobiusRadialTime` records the exact reciprocal-orbit criterion:
`{z, z⁻¹}` is contained in the unit circle iff `‖z‖ = 1`. The orbit of `2`
is invariant under inversion but is not contained in the unit circle, refuting
the stronger localization inference. The locked build of
`DAG.DirectedLabeledWL`, the InfoTree counterexample, Möbius audit, and Peirce
tangent audit passed (4,238 jobs, exit 0). After removing two warnings in the
Möbius owner, its audit rebuilt separately (3,094 jobs, exit 0); its three
reported declarations depend only on `[propext, Classical.choice, Quot.sound]`.

The multiset refinement's stated non-completeness boundary now has a concrete
finite witness in `DAG/DirectedLabeledWLCounterexamples`: a two-vertex graph
with one self-loop per vertex and a two-cycle have equal WL colors at every
depth and equal graph color multisets, but admit no `GraphIso`. The companion
theorem `oneWL_not_complete_for_labeled_digraphs` packages the equal multiset
and non-isomorphism into one counterexample statement for every depth. Its
audit built in four jobs; the color equality uses no axioms, multiset equality
uses `Quot.sound`, and non-isomorphism uses `propext`.

## Abelian Klein-bottle braid constraint (2026-10-27)

`Topology/NonorientableExceptionalBraids` corrects the overstrong conclusion
that the abelian Klein-bottle relation forces `B_p = 1`. The exact statement is
`B_p² = 1`, and the relation is equivalent to that condition in a commutative
group. `Multiplicative (ZMod 2)` supplies a nontrivial order-two witness. The
corrected topology bridge and cyclotomic operator audit built in a locked run
(9,182 jobs, exit 0); unrelated imported modules emitted existing warnings.
The new `NonorientableExceptionalBraidsAudit` target then built separately
(3,094 jobs, exit 0); the two algebraic classification theorems report only
`[propext]`, and the concrete witness reports only standard Lean axioms. These
checks verify the source batch, not the completeness of the repository
inventory or independent semantic QA.

## Andreev perturbation and kernel-square boundaries (2026-10-26)

The existing doubled-space Andreev rotation is injective, so its output on
`x + e` equals its output on `x` iff `e = 0`. This refutes unconditional
perturbation erasure by the reversible operation alone; it says nothing against
error correction using encoding or additional measurements. Separately,
`kernel_square_eq_iff` states for an arbitrary native linear endomorphism that
`ker (f ∘ f) = ker f` iff `range f` and `ker f` are disjoint. Under `f² = 0`,
kernel stability is equivalent to `f = 0`. The audit derives failure of
range/kernel disjointness for the repository's actual Krein `nullDirac`.
Locked build 58126 passed (3,294 jobs, exit 0); five declarations report only
standard Lean axioms, with one concrete nonzero-perturbation example and the
existing Krein counterexample. Strict screening found zero traps. Independent
QA was later recorded as accepted in `KREIN_SPIN_EXISTING_REPLACEMENTS.md`
(session 69457). A fresh locked replay of
`InfoGeometry.HodgeCohomology.KernelSquareCriterionAudit` passed on 2026-10-27
(3,291 jobs); the audit reports only standard foundational axioms for the
general criterion, square-zero criterion, and actual Krein witness. This
fresh replay verifies the current owner source, not the historical independent
QA process. See `PHASE_CONJUGATE_AI_INTAKE.md` and
`KERNEL_SQUARE_CRITERION.md`.

The lexical candidates `KreinHodgeDiracTests.nullOperator_kernel_counterexample`,
`KreinHodgeDiracTests.hodge_counterexample`, and
`KreinHodgeObstruction.nullDirac_kernel_counterexample` are now reconciled by
source: the first gives unequal kernels for a nonzero square-zero operator;
the second gives a nonzero doubled null operator with square zero; the third
is the corresponding actual Krein-space witness. The exact criterion above
applies to the first and third, while the production energy theorem gives
kernel stability only with image anisotropy or positive symmetry-weighted
pairing and commutation. Exactness of the separate null complex is proved, but
indefinite harmonic vectors are not thereby identified with homology.

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
zero own warnings and traps. A current replay of both audit targets also
passed (3,100 jobs, exit 0); the witness and exact equivalence report only
standard Lean axioms. This family was already resolved and is not a new
counterexample in the current inventory pass.
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

## Idempotent charts are split data, not a metric Grassmannian (2026-10-30)

The recent A23/A24 synthesis is valid only after separating its algebraic
identities from its geometric interpretation. In an endomorphism ring, an
idempotent determines a split pair (its image and kernel); the image alone
does not determine the idempotent. The repo-owned theorem
`SuperGrassmannian.ProjectorGraphChart.graphProjector_mul` proves that graph
projectors satisfy `e_f * e_g = e_f`, while
`graphProjector_commute_iff` characterizes exactly when two such projectors
commute. `range_complement_graphProjector` and
`complement_graphProjector_eq_iff` make explicit that complementary graph
projectors can share a range while remaining distinct. The graph-chart owners
therefore retain the chosen complement as part of the data.

The current algebraic Grassmannian owner is
`Core.IdempotentGraphGrassmannian`: it proves the linearized equation
`p*x + x*p = x`, the off-diagonal Peirce decomposition, graph idempotence,
absorption, chord identities, and the transition operator
`1 - (q-r)^2`. Its module contract explicitly makes no manifold, positivity,
angle, or geodesic claim. Accordingly, the draft's “principal-angle” and
“Kähler/geodesic reflection” language is not a theorem over an arbitrary
associative ring; those interpretations require additional *-algebra,
positivity, topology, and metric hypotheses. Keep the exact ring identities,
but do not promote those interpretations.

The separate `GraphChartOddRegression` witness proves that coefficient
reduction can identify distinct graph points; `GraphChartReductionFibers`
replaces injectivity claims with the exact coefficient-kernel criterion.
These are related but distinct issues: the former concerns information lost
under base change, while the latter correction concerns what an idempotent
encodes before base change. No new owner theorem was needed in this pass; the
existing graph-chart and idempotent owners already prove the corrected
statements. The finite CCR trace file under `Experimental/Sandbox` is likewise
a duplicate of the canonical finite-dimensional CCR obstruction recorded
above, not an additional counterexample family.

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

Follow-up exactness upgrade: `CayleyHestenesGradedIntertwinerBridge` now also
states `plain_intertwiner_commutator_naturality` without assuming that the
source commutator vanishes, and
`plain_intertwiner_commutes_iff_target_commutator_kills_image` characterizes
source commutation exactly for an injective intertwiner. The source edit is
staged. A fresh locked build of the bridge, sector-kernel owner, its axiom
audit, and both concrete/filtered-colimit consumers passed (8,934 jobs, exit
0). The audit printed only Lean's standard foundational axioms for the
selected declarations. Existing linter warnings remain; this does not claim
an independent semantic review of every downstream module.
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

# Finite matrix Cuntz obstruction and rectangular replacement

`Canonical.FiniteMatrixCuntzObstruction.no_cuntz2_matrix` refutes a
stagewise Cuntz-2 isometry family in every nonzero square complex matrix
algebra: the two isometry traces and orthogonal range-sum identity force
`2 * n = n`. This is a finite-dimensional no-go result, not an obstruction
to the inductive-limit Cuntz algebra. The source module documents the existing
constructive replacement, `FiniteCantorCuntzBranches.amplify`, whose
rectangular branch system preserves the stated refinement/intertwining laws.
`Canonical.MatrixCuntzStarTower.matrixStage_cuntz_obstruction` is only a
forwarding wrapper, so no duplicate theorem or audit was added. The candidate
is source-confirmed; no new build or independent audit was run in this pass.

# Set-valued neighbor profile versus multiplicity-sensitive 1-WL

`Canonical.InfoTreeColorRefinement` previously called its relation
`Is1WLEquivalent`, although the relation compared only existence of a neighbor
of each color. `Canonical.InfoTreeColorRefinementCounterexamples` proves that
two sources can satisfy this support relation while having respectively one
and two outgoing neighbors of the same color. The owner now names the relation
`SameColoredNeighborSupport`, documents that it forgets multiplicity, and
removes two color-fiber wrapper theorems whose conclusions followed directly
from existing conductive-path results without any profile hypothesis.

The canonical multiplicity-aware alternative already exists in
`DAG.DirectedLabeledWL.wlColor`: it stores role-tagged outgoing and incoming
neighbor colors as quotient multisets and proves graph-isomorphism invariance.
Its scope is the abstract list-presented graph model; this does not claim an
InfoTree exporter or that 1-WL is a complete graph-isomorphism invariant. The
three targeted modules built successfully in a locked Lake run (4221 jobs,
exit 0); warnings were from pre-existing dependencies/other owners. Independent
semantic review and the broader gates remain outstanding.

The semantic-vacuity scanner reports zero findings in the concrete
counterexample module. It flags the equality/specification fields in the two
abstract graph records as proof-like carrier fields; those fields define the
graph-isomorphism and conductive-edge models and are not theorem conclusions
or fake proof placeholders. This is a scanner warning, not a passed clean gate.

## Associator criterion for the left-regular commutator defect (2026-10-27)

`Algebra.AkivisLeftRegularBridge` already gives the exact defect formula under
the first-two-slot alternative law:
`leftRegularCommutatorObstruction x y = -associatorOperator x y`. I added
`leftRegular_commutator_obstruction_eq_zero_iff`, making the canonical
vanishing criterion explicit: the operator defect is zero iff the carrier
associator vanishes for every third argument. This separates the always-Lie
operator commutator from the carrier commutator without asserting that the
left-regular map is a Lie representation on a nonassociative carrier.
The owner and its axiom audit built in a locked run (3,103 jobs, exit 0); the
three printed declarations use only `[propext, Classical.choice, Quot.sound]`.
Existing warnings are in imported alternative-algebra sources and an older
owner theorem. Repository-wide discovery remains incomplete.

## Cyclotomic Peirce ambient-unit boundary (source reconciliation)

The inventory candidate `Algebra.CyclotomicPeirceMatrix.ambient_unit_obstruction`
is conditional: if some spectral projector is not the ambient unit, the
corner-valued block image does not send `1` to the full ambient matrix unit.
The canonical target is already characterized by
`CyclotomicPeirceMatrix.existsUnique_blocks_iff_supported`: a matrix has a
unique preimage exactly when each entry is supported by its two Peirce
projectors. The constructive assembly reuses
`Core.FinitePeirceMatrix.blocks_assemble`; the image unit is
`Matrix.diagonal F.projector`. The existing `CyclotomicPeirceImageAudit`
records the focused kernel audit. This source review found no missing theorem
to add and makes no claim about unrestricted matrix surjectivity.

# Characteristic-two reflection/tangency boundary

`Core.PeirceTangentCounterexample.matrix_reflection_anticommutation_not_tangent`
is a noncommuting `M₂(ZMod 2)` refutation: reflection anticommutation holds,
but the first-order idempotent tangent equation fails. The canonical
all-characteristic replacement is already
`Core.PeirceTangent.reflection_anticommutes_iff_diagonal_corners_two_torsion`;
the injective-doubling hypothesis gives the separate tangent/reflection iff.
The counterexample now also proves that both doubled diagonal corners vanish
while the first diagonal corner is nonzero, explicitly instantiating the exact
criterion. `PeirceTangent`, its counterexample, the axiom audit, and the
Grassmannian source built successfully in locked Lake runs (3194 jobs, exit 0).
The audit reports only `[propext, Classical.choice, Quot.sound]` for the new
matrix witness. Imported-owner warnings remain; repository-wide discovery and
independent semantic QA remain open.

# Klein-bottle topology scope boundaries

`Topology.BrillouinKleinExceptionalTopology.klein_boundary_charge_doubles`
proves the additive-homomorphism identity for the formal word `a + b + a - b`;
it does not prove a fermion-doubling result or a Brillouin-zone classification.
The wallpaper/Weyl bridge now refers to this accurately named theorem.

In `Topology.NonorientableExceptionalBraids`, the abelian Klein-bottle relation
is equivalent to `B_p^2 = 1`, not `B_p = 1`. A `Multiplicative (ZMod 2)` witness
exhibits a nontrivial solution. The existing RP² theorem appropriately asks for
the separate hypothesis that elements with square one are trivial.

## Refreshed source scan and Gramian counterexample review (2026-10-27)

The repository-owned inventory scanner was rerun against the current worktree:
47,870 Lean files scanned, 31,085 lexical candidate rows, 11,568 rows tagged
`repo-owned`, and zero read errors. This is lexical navigation data, not a
semantic census; candidate header extraction can extend across declarations.

The scanner was then revised to separate a declaration's result type from its
balanced binder groups before looking for `≠`, `¬`, or `False`. This prevents a
negative hypothesis such as `(h : x ≠ y)` from independently classifying an
otherwise positive theorem. The revised run scanned 47,871 Lean files and
returned 19,755 candidates (6,431 tagged `repo-owned`), with zero read errors.
All 30 repo-owned declarations whose names contain `counterexample` remained
visible. The change improves lexical precision but is still not a Lean parser:
negative conclusions can be implicit, declaration modifiers/syntax may evade
the delimiter scan, and semantically false positive theorems without these
markers remain outside its recall. Result artifact:
`/tmp/counterexample-inventory-resulttype.json` (ephemeral).

The next reviewed family was
`Canonical.GramianInverseContracts.oblique_idempotent_counterexample`. Its
real `2 × 2` idempotent has a non-self-adjoint support, while both tested
operator cross-Gramians vanish. The canonical replacement is the projector
criterion `projector_cross_zero_iff` (and its adjoint-side version), which
characterizes self-adjointness using the actual projector cross-product rather
than the A-sandwiched Gramians. The owner and both existing axiom-audit modules
built successfully in a locked Lake run (8,942 jobs, exit 0); the audit output
for the reviewed declarations reports only `[propext, Classical.choice,
Quot.sound]`. Warnings came from imported Moore–Penrose sources. No duplicate
statement was added. The repo-wide inventory remains incomplete.

## Residue reflection and cancellation boundary (2026-10-27)

`Analysis.SimplePoleReflection.signed_reflection_counterexample` refutes the
proposed sign for the reflected one-form using the concrete coefficient `1/z`.
The canonical rule is already proved: `coefficient_reflection` changes the
coefficient sign for `f(-z)`, while `coefficient_oneForm_pullback` includes the
Jacobian and preserves the residue. The neighboring
`balanced_residues_do_not_imply_removability` theorem separately shows that
opposite residues can sum to zero while a local pole remains. This is scoped to
the repository's `HasSimplePoleCoefficientAt` predicate; it is not a global
residue theorem. Added a focused axiom-audit module for these four declarations;
the locked build passed (3,498 jobs, exit 0), and all four `#print axioms`
reports contained only `[propext, Classical.choice, Quot.sound]`. Existing
warnings were emitted by imported coordinate/logarithm owners.

## Reflection symmetry does not locate zeros (2026-10-27)

`Arithmetic.SarnakLocalCertification.counterexample_is_symmetric` uses
`z * (z - 1)` to show that invariance of the zero predicate under
`z ↦ 1 - conj(z)` alone does not force every zero onto the fixed line. The
native replacement has two appropriately scoped forms: a `CertifiedRegion`
with reflection invariance and at most one zero proves that any zero in it is
on the line; independently, `ReflectionZeroCount` proves that an odd finite
reflection-invariant set (or zero-filter) contains a fixed point. Neither
supplies coverage or an odd count for actual xi zeros. Current locked build of
`SarnakLocalCertificationTests` passed (8,937 jobs, exit 0); its axiom output
reports only `[propext, Classical.choice, Quot.sound]` for the counterexample,
finite-count theorem, and conditional certificate statements. Existing linter
warnings occur in the tests and imported arithmetic source. No duplicate
replacement was added; the inventory remains incomplete.

## Freudenthal mixed-triple/Jacobi boundary (2026-10-27)

`Exceptional.Freudenthal.symplecticRankTwo_mixedTriple_counterexample` refutes
the outer-slot identity required by the legacy mixed TKK socket on the actual
`FreudenthalCharge` carrier. The alternative does not force that identity:
`freudenthalSymplecticTripleSystem` proves the correctly ordered symplectic
triple-system laws, while `tkk_mixed_jacobi_on_iff_pairing_zero` states the
precise orthogonality condition for the relevant mixed component. The separate
`symplecticContactBracket` has a faithful representation into endomorphisms,
which proves its native Lie structure. These results do not identify it with
the exceptional quartic-derived algebra or validate `tkkTotalBracket`. The
dedicated audit rebuilt successfully (8,942 jobs, exit 0); all twelve audited
declarations report only `[propext, Classical.choice, Quot.sound]`. Existing
warnings were in imported Freudenthal owners; details and prior independent
review are in `FREUDENTHAL_CONTACT_REALIGNMENT.md`.

## Metriplectic attention obstruction trace correction (source repair, 2026-10-30)

`Attention.MetriplecticAttentionDynamics.chiral_obstruction_eq_diagonal_leak`
computes the obstruction as `diag(M₀₀, -M₁₁)`. Its introductory claim that
positive diagonal entries yield a strictly positive trace for this obstruction
was false: the trace is `M₀₀ - M₁₁`, which vanishes for the identity matrix.
The source now states the exact trace identity and gives a positive-diagonal,
zero-trace witness whose input matrix has nonzero off-diagonal entries,
together with the valid
replacement that a positive first diagonal entry makes the obstruction matrix
nonzero. The separate theorem
`softmax_trace_strictly_positive` remains scoped to the diagonal core, whose
trace is `M₀₀ + M₁₁`. The owner passed a locked build (3,093 jobs, exit 0);
the only owner warning is a deprecated Mathlib import.

Follow-up correction: the source docstring for `softmax_trace_strictly_positive`
had continued to describe that diagonal-core result as an obstruction-trace
theorem. I corrected the docstring and added
`chiral_obstruction_trace_pos_iff`, the exact criterion
`0 < trace (chiral_obstruction M) ↔ M 00 > M 11`. The existing equal-positive-
diagonal witness shows strict positivity cannot be inferred from positivity of
both entries. This follow-up source edit is staged; its focused build is pending
the shared Lake build lock.

The adjacent
`FreudenthalFiveGradedLegacyJacobiCounterexample` (with the corresponding
`FreudenthalLegacyFiveGradedJacobiCounterexample` readback) records a
separate failure: the legacy five-graded bracket's Jacobiator on the
extreme/charge triple is the nonzero element `injChargeMinus D (2 • alphaCharge)`.
This is not the mixed-triple obstruction above. The canonical replacement is
the existing `symplecticContactBracket`, whose faithful endomorphism
representation transports the native Lie laws; no identification with the
legacy bracket or an exceptional quartic-derived algebra is claimed. The
owner and consumer repair, including the sequential build and independent QA
record, are documented in `FREUDENTHAL_CONTACT_REALIGNMENT.md`.

## Idempotent compression does not preserve cyclicity (2026-10-27)

`Algebra.CornerCompressionTraceCounterexample.compression_not_cyclic` and
`compression_no_cyclic_factor` use the actual idempotent
`diag(1,1,0)` in `M₃(ℤ)` to refute cyclicity and factorization through the
additive cyclic quotient for the functional `X ↦ Tr(P X P)`. This does not
refute extension of the corner trace: ordinary full matrix trace is such an
extension in this example. The generic alternative is
`Algebra.CyclicQuotient.map`/`desc`, which proves functorial descent for
nonunital multiplicative maps and factorization for additive cyclic
functionals; the nuclear specialization reuses the existing corner lift.
The centrality owner gives the exact two off-block criterion, while separately
proving centrality inside `P A P`. The four relevant Lean source hashes match
the kernel-evidence packet in `NUCLEAR_CORNER_CYCLIC_BRIDGE.md`; that packet
records an isolated locked build (8,952 jobs), a 32-declaration axiom check
with only standard axioms, and the reason the prescribed root build could not
start (missing `external_refs/atlas-lean`). This is source-hash corroboration
of the recorded verification, not a fresh root build. No universal trace
extension claim is made; the repository-wide inventory remains incomplete.

## Cubic companion is not Euclidean-orthogonal (2026-10-27)

`Algebra.CubicCompanionFlow.thirdRoot_not_orthogonal` is a genuine
counterexample to orthogonality in the standard Euclidean coordinates. The
owner now states the stronger exact witness
`thirdRoot.transpose * thirdRoot = !![(1 : ℝ), -1; -1, 2]`, from which
nonorthogonality follows by the `(1,1)` entry. This does not contradict the
separate exact order-three and exponential-generator results: the corrected
square-negative generator exponentiates to the companion, but that companion
is not the standard orthogonal rotation matrix. The existing corrections test
module audits both Gramian and nonorthogonality declarations. Its locked build
passed (8,939 jobs, exit 0); the audited exponential theorem reports only
`[propext, Classical.choice, Quot.sound]`. Imported owners emit pre-existing
warnings. No broader orthogonality classification is claimed.

## Hyperbolic ladder mixing does not preserve the fixed Cartan (2026-10-27)

`Physics.SpinAffineCasimirRigidity.hyperbolic_counterexample` gives the
explicit coefficients `(u,v) = (5/4, 3/4)`: their indefinite norm preserves
the ladder-ladder bracket, while the independent fixed-Cartan relation fails.
The canonical statement is `mixed_cartan_iff`, which says that the Cartan
relation holds exactly when the lowering coefficient `v` vanishes; combining
it with `mixed_ladder_bracket` yields
`fixed_cartan_spin_relations_iff`, characterizing the simultaneous relations
as `v = 0 ∧ Complex.normSq u = 1`. Thus the accepted transformations in this
ansatz are phase rotations, not nontrivial hyperbolic squeezes. This scope is
only the stated `ℂ`-linear combination of the existing spin raising/lowering
matrices, not a general automorphism classification. The existing
`Canonical.KreinSpinPositiveAudit` audits the counterexample and equivalence;
its locked build passed (8,952 jobs, exit 0), and the axiom reports for both
declarations contained only `[propext, Classical.choice, Quot.sound]`. A new
focused locked build of `InfoGeometry.Physics.SpinAffineCasimirRigidity` also
passed (8,937 jobs, exit 0), checking the exact counterexample and its
canonical equivalence together; imported linter warnings remain.
Pre-existing warnings arise in imported Hodge and spin owners. No general
Bogoliubov transformation or physical particle-production claim is inferred.

## Signed-radius contour counterexample (2026-10-27)

`Analysis.BipolarCircleEnclosurePeriods.negative_radius_exterior_counterexample`
shows why the exterior-pole lemma cannot drop its nonnegative-radius hypothesis:
for radius `-1`, the closed ball is empty but the parametrized circle integral
of `(z - 0)⁻¹` is `2πI`. The canonical generalization is the signed-radius
family in `Analysis.BipolarSignedRadiusPeriods`: `circleIntegral_neg_radius`
proves invariance under `r ↦ -r`, `circleIntegral_abs_radius` reduces all
radii to `|r|`, and `circleIntegral_pole_eq_abs_enclosure` gives the exact
pole-enclosure formula. Its audit includes the original witness and the
radius-zero case. These are facts about Mathlib's parametrized circle integral;
they do not establish arbitrary-loop homotopy classification.
The dedicated audit target passed a locked build (4,345 jobs, exit 0); all
four audited signed-radius declarations report only `[propext, Classical.choice,
Quot.sound]`. Existing warnings come from imported analysis owners.

## Reciprocal-orbit unit-circle criterion (2026-10-27)

The counterexample `Analysis.MobiusRadialTime.inversion_invariance_does_not_force_unitCircle`
shows setwise inversion invariance alone does not localize every point to the
unit circle: inversion can exchange `2` with `1/2`. I added the exact
orbit-level alternative `reciprocalOrbit_subset_unitCircle_iff`, proving that
the two-point orbit `{z, z⁻¹}` lies on the unit circle exactly when its seed
has norm one. This does not infer localization for arbitrary invariant sets;
additional hypotheses must control the modulus of orbit representatives.
The new focused audit and owner passed a locked build (3,094 jobs, exit 0);
all three audited declarations report only `[propext, Classical.choice,
Quot.sound]`. Two pre-existing `simpa` style warnings remain in the owner.

## Harmonic rectangle mean-value boundary (2026-10-27)

`EmergentGeometry.HarmonicRectangle.harmonic_rectangle_counterexample` uses
`Re(z²)` on the `2 × 1` centered rectangle to refute an unrestricted rectangle
mean-value claim for harmonic functions. The canonical family-level alternative
is `HarmonicQuadraticRectangle.harmonicQuadratic_center_mean_iff`: for
`Re(a z² + b z + c)` and positive half-widths `w,h`, the rectangle average
matches the center exactly iff `a.re = 0 ∨ w = h`. The formula also shows the
full average is `c.re + a.re * (w²-h²)/3`; affine and mixed terms cancel.
This is a classification only for real parts of complex quadratics, not all
harmonic functions. The dedicated audit's locked build passed (3,547 jobs,
exit 0); every declaration printed by
the audit, including the exact criterion and counterexample, reports only
`[propext, Classical.choice, Quot.sound]`. Existing deprecation warnings are
from the imported harmonic mean-value owner.

## A4T cyclotomic adjacency sign correction (2026-10-27)

`Omega.POM.a4t_cyclotomic_adjacency_injection_target_counterexample` refutes
the displayed sign variant
`1 - 2v - tv² - 2v⁴ + 2v⁵ = 0` at the specified `π/4` parameter. The same
owner proves the corrected core identity
`1 + 2v - tv² - 2v⁴ - 2v⁵ = 0` for every `v ≠ 0`, then proves the paper-labeled
cyclotomic statement for natural `h ≥ 4` by establishing its parameter is
nonzero. These are scalar polynomial statements with the exact definitions in
`A4TCyclotomicAdjacencyInjection.lean`; they do not certify a larger POM
adjacency-injection construction. A focused axiom audit was added and the
locked build passed (3,093 jobs, exit 0); all three declarations report only
`[propext, Classical.choice, Quot.sound]`.

## Newman linear-response polynomial needs its root hypothesis (2026-10-27)

`Omega.POM.pom_a4t_newman_linear_response_constant_counterexample` shows that
the displayed rational formula does not yield a root of the recorded degree-8
polynomial for arbitrary `zStar > 1` (the witness uses `zStar = 2`). The
canonical corrected theorem explicitly assumes both `1 < zStar` and the
Newman-octic equation. Under those hypotheses, the owner proves denominator
nonvanishing, an exact elimination identity, the polynomial root statement,
and then the paper-facing package. This is a conditional polynomial result;
it does not establish that an arbitrary parameter satisfies the Newman root
equation. The focused audit's locked build passed (3,095 jobs, exit 0); all
five declarations report only `[propext, Classical.choice, Quot.sound]`.
Pre-existing deprecation and sequencing warnings occur in the owner.

A source audit found that the former `A4TE8TwoResolutionLayerNonembedding`
theorem did not formalize field carriers or maps: “embedding” was represented
only by the numerical proposition `8 ≤ 4`, and the claimed totally-real
obstruction by a signature tuple's second coordinate being zero. Its E₈,
ADE, and cyclotomic dependencies were destructured and discarded. I replaced
that overclaim with `paper_pom_a4t_e8_two_resolution_layer_recorded_data`,
which states only the recorded degree ratio and recorded signature, plus the
generic theorem `no_injective_linearMap_finrank_eight_to_four`. That theorem
proves the actual dimension obstruction when genuine finite-dimensional
carriers of dimensions 8 and 4 are supplied; it does not identify the
repository's records with constructed number fields. The module now depends
only on the Newman signature owner. The focused target and full `Omega.POM`
aggregate rebuilt successfully (10,495 jobs, exit 0); pre-existing warnings
remain in the aggregate's dependencies.

## G₂ cell-two raw residual collision and paired replacement (2026-10-27)

`G2ResidualCoordinateCellTwoBoundary.residualWord_cell_two_collision`
exhibits distinct indices `170` and `185` in `orbitCells 2` with equal raw
left-factor residual words. Its companion
`residualWord_injective_on_cell_two_is_false` turns that witness into the
explicit negation of injectivity on the cell. Thus raw `residualWord` is not
injective on that cell. The corrected statistic is the two-sided
`residualPair`, whose existing
`residualPair_injective_on_cell_two` proves injectivity across the entire cell;
`G2GAPFlagWitnessAssembly.quotientRepresentative_injective_on_cell_two_of_pair_alignment`
states the corresponding quotient-representative consequence under the
explicit pair-alignment hypothesis. I added a focused audit that prints the
counterexample and replacement axiom dependencies and checks that the pair
separates the same indices. The locked build passed (8,996 jobs); all three
printed declarations use only the standard foundational axioms. No cross-cell
alignment or full Bruhat classification is inferred from this cellwise result.

## G₂ quotient collision and alignment-package refutation (2026-10-30)

Ground-truth contract: the map is `Fin 189 → CarrierQuotient`, where
`CarrierQuotient = SplitOctF2Aut ⧸ unipotentSubgroup`; its exact equality
criterion is `(flagRepresentative i)⁻¹ * flagRepresentative j ∈
unipotentSubgroup` in `G2NativeQuotientRepresentative.quotientRepresentative_eq_iff`.
The lexical candidate `G2QuotientCollisionAudit.quotientRepresentative_not_injective`
is a genuine refutation of global injectivity, witnessed by the concrete
24/45 collision; it is not a defect to “repair” by asserting injectivity.
The canonical positive replacement is scoped classification:
`cell_one_quotient_eq_iff_same_pair` gives the exact equality relation on
Cell 1, and `cell_one_quotient_image_eq_two_values` identifies its image.
The current cell-one owner proves `[24] = [45]` and `[73] = [178]`, proves
the two cross-pairs are unequal, and classifies the full cell-one quotient
fiber relation and image cardinality as exactly two (`G2CellOneQuotientRelation`).
The 24/45 collision has different raw residual words, so it contradicts the
`residual_alignment` field in both `FactorizationAlignmentSystem` and
`ConcreteFactorizationAlignmentSystem`. The smallest remaining source gap is
now closed by
`G2CellOneQuotientRelation.no_factorizationAlignmentSystem` and
`no_concreteFactorizationAlignmentSystem`, each deriving `False` from the
collision, cell membership, and the proved residual-word inequality. The
focused locked build of `InfoGeometry.Algebra.Zorn.G2CellOneQuotientRelation`
passed (9,023 jobs, exit 0). Such a refutation does not classify all 189
quotient fibers or rule out a replacement package using a quotient-compatible
invariant.

## Projector covariance does not imply nilpotency (2026-10-27)

`InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.covariance_without_nilpotency`
is a concrete counterexample on the nonempty native carrier `Fin 4 → ℂ`: the
Fourier projectors of `coordinateClock` are covariant under the cyclic shift,
but `cycle ^ 4 = 1`, hence is nonzero. The owner proves the corrected
distinction on the same carrier and with the same projectors: `truncatedShift`
has the same covariance, `truncatedShift ^ 4 = 0`, and
`truncatedShift ^ 3 ≠ 0`. Thus covariance alone supplies no nilpotency law;
the zero boundary at the end of the truncated chain is the additional
structure. Source review found no direct theorem applications outside this
owner (the listed reconstruction file is import-only); the exhaustive import
and axiom-audit file are not evidence of further applications. A-A and QA-A
independently reviewed the scope; A-A reported a successful locked build of
the owner (9,351 jobs). The repository-wide counterexample audit remains open.

## Cuntz isometry block square and non-involution boundary (2026-10-27)

`AlgebraicCuntzNPresentation.raw_isometry_block_not_involution` is valid under
its explicit `[Nontrivial A]` condition, not an unrestricted counterexample:
the owner first proves the exact square
`!![0, S 0; T 0, 0]^2 = !![S 0 * T 0, 0; 0, 1]` from the presentation's
isometry relation. It then uses
`matrixUnit_zero_zero_ne_one` to rule out the identity matrix. The canonical
replacement for a mistaken involution claim is the exact square formula with
its proper range idempotent; no stronger claim about arbitrary off-diagonal
blocks follows. I added a focused axiom-audit module for the square, proper
corner fact, and non-involution theorem. The repository-wide lexical candidate
inventory remains incomplete.

## Commuting outer-inverse residual nilpotence boundary (2026-10-27)

`Core.NilpotentCartanRegression.oblique_zero_residual_not_isNilpotent`
refutes the implication from commutation and the outer-inverse law alone to
nilpotence of `a * (1 - a * b)`: the regression takes the nonzero idempotent
oblique matrix for `a` and `b = 0`, so both weak hypotheses hold while the
residual is the same nonnilpotent matrix. The canonical replacement is
`Canonical.Drazin.residual_isNilpotent_iff_exists_drazinIndex`: under exactly
those two weak hypotheses, residual nilpotence is equivalent to existence of
an index satisfying all three Drazin laws. The proof uses the exact power law
`commuting_outer_residual_pow_succ` and does not assert a nilpotence bound
without the Drazin-index hypothesis. The focused audit
`InfoGeometry.Core.DrazinPowerBoundaryRegressionAudit` built successfully in a
locked 3,193-job run. The general criterion reports `[propext]`; the concrete
matrix witnesses report only `[propext, Classical.choice, Quot.sound]`. The
lexical inventory remains incomplete.

## Cuntz Hamiltonian readout scope correction (2026-10-27)

The declaration `Algebra.CuntzChiralSuperchargeRepresentation.spontaneous_susy_breaking`
is valid as an algebraic contradiction, but its old name and prose overstate
what is proved: `E : R → ℝ` is an arbitrary function, not a state, and no
positivity, linearity, representation, spectrum, or ground-state structure is
present. The stated isometry and completeness hypotheses prove the
anticommutator Hamiltonian equals `1`; therefore the exact result is simply
`E H ≠ 0` from `E 1 = 1` and `H = 1`. I added the reusable theorem
`normalized_readout_ne_zero_of_eq_one`, its Cuntz specialization
`normalized_readout_cannot_annihilate_complete_hamiltonian`, and retained the
old theorem name as a documented compatibility result. The architecture note
now states this boundary explicitly. The focused axiom audit built in a locked
3,094-job run; the Hamiltonian identity reports `[propext]`, and the readout
theorems use only `[propext, Classical.choice, Quot.sound]`. No physical SUSY
breaking conclusion follows from this package.

## Current lexical inventory checkpoint (2026-10-27)

The refreshed `counterexample_inventory.py --json` run scanned 47,881 Lean
files, emitted 19,759 lexical candidates (6,435 tagged `repo-owned`), and had
zero read errors. The 30 repo-owned declaration names containing
`counterexample` are review seeds, not a complete census: semantic
counterexamples can have positive names or no negative result syntax, while
many negative-boundary theorems are intentional correct results. The latest
report is `/tmp/counterexample-inventory-current.json` and is ephemeral.

## Twistor isotropy versus Hermiticity candidate (2026-10-27)

The repo-owned candidate `Twistor.TwoTwistorIncidenceIsotropy.isotropy_does_not_imply_hermitian`
is already paired with its canonical replacement in the owner: for invertible
`P`, reconstructed-node Hermiticity is equivalent to the additional frame-skew
condition `Pᴴ * Ω + Ωᴴ * P = 0`; isotropy alone only yields the separately
stated unitary conclusion. The concrete witness is `X = i I`, `P = I`, and
`Ω = -I`, satisfying the incidence/isotropy and unitary equations while
`Xᴴ ≠ X`. `frameSpacetimeNode_isotropy_and_frame_skew_implies_hermitian`
states the corrected implication. This candidate therefore needs no duplicate
replacement theorem. Its current audit is
`Canonical.AdjointCovarianceRealignmentAudit`, which reports the owner theorem
axioms and includes a derived example; the existing evidence in
`docs/ADJOINT_COVARIANCE_REALIGNMENT_AUDIT.md` records the locked build and QA
scope. This reconciles one lexical candidate only and does not establish
inventory completeness.

## Co-mutation association does not identify causal epistasis (2026-10-27)

The proposed `commit_decl_edges` interpretation treats asymmetric conditional
co-mutation rates as evidence that one declaration causally drives another.
This inference is not identified by observational data. In
`Graph.CoMutationCausalityCounterexample`, two structural causal models have
identical observations in all four exogenous states. Their observed events
nevertheless have `P(B | A) = 1` and `P(A | B) = 1/4` under the uniform finite
population, while the models disagree on `B` under `do(A := false)` at state
zero. The canonical replacement is to report these values as conditional
co-mutation associations; a causal/epistatic claim needs an explicit causal
model or intervention evidence. The focused audit
`Graph.CoMutationCausalityCounterexampleAudit` records the Lean axiom reports.
A fresh locked build of that audit passed (8,925 jobs, exit 0); the six
counterexample declarations use only `[propext, Classical.choice, Quot.sound]`.
This is kernel/build evidence, not an independent causal-model review.

## Scalar-fixing star obstructs complex-positive GNS packets (2026-10-27)

Source tracing confirmed that `Algebra.CuntzTensorQuotient.daggerFree` is
`ℂ`-linear and the descended `StarRing` therefore fixes the image of every
complex scalar. In `Algebra.CuntzGNSTensorQuotient`, `CuntzGNSStateLaws`
combines that star with a normalized `ℂ`-linear functional and positivity of
`φ (star x * x)`. The existing no-state theorem is valid for this explicitly
defined package: the scalar `x = i` makes the readout of `star x * x` equal to
`-1`. I generalized this obstruction to any complex algebra with a
scalar-fixing `StarRing`, and made the Cuntz-specific theorem an application
of that canonical criterion. This does not refute GNS for the conventional
conjugate-linear involution or establish a result about the analytic Cuntz
`C*`-algebra. The focused axiom audit prints the generic criterion and its
specialization.

## Cuntz clock, block-square, and cyclic-trace boundaries (2026-10-27)

`Algebra.CuntzClockObstructions` supplies three exact corrections to stronger
clock/Clifford claims. First, if invertible `X` and `Z` commute and satisfy
`Z * X = q • (X * Z)` in a nontrivial complex algebra, cancellation by their
inverses forces `q = 1`; thus a nontrivial Weyl scalar cannot occur for a
commuting pair. Second, the block made from one Cuntz isometry squares to a
diagonal block with its range projection, not to the identity when that range
is proper. Third, on the specified two-generator quotient, additivity and
cyclicity imply `τ 1 ≠ 1`; this is not an obstruction to KMS states or traces
on subalgebras. The canonical replacements are the exact scalar criterion,
the range-projection square identity, and the narrowly scoped unnormalized
cyclic-trace theorem. Existing `CuntzClifford22Audit` prints the corresponding
kernel dependencies; the claims are limited to these algebraic carriers.

## Conflicting displayed Zitterbewegung periods (2026-10-27)

`InfoGeometry.Canonical.ZbwDarwinDemodulation.DecimalAudit` encodes the two
displayed period values exactly as rationals:
`shortPeriodClaim = 64 / 10^23` seconds and
`gapPeriodClaim = 405 / 10^23` seconds. The kernel-checked
`displayed_period_claims_conflict` proves they are unequal. With the same
encoded central lifetime `363 / 10^14` seconds, the first period gives exactly
`5,671,875,000` cycles, whereas the second gives a value between
`896,296,296` and `896,296,297`; including the stated lifetime uncertainty
gives the owner’s separate interval bounds. The canonical correction is to
keep the period/lifetime arithmetic tied to the explicitly selected displayed
period and report the resulting count as conditional on that choice. This
finite rational audit does not decide which displayed physical value is
empirically correct and does not derive a Zitterbewegung trajectory or Darwin
term. The owner source also explicitly limits its detector and physical
interpretations.

## Asano–Ruelle unrestricted contraction claim (2026-10-27)

The lexical candidates in `Analysis.AsanoContractionNative` are mostly
conditional localization lemmas; the actual unrestricted-claim refutation is
`Canonical.AsanoRuelleCounterexample.unrestricted_AsanoRuelle_contraction_statement_false`.
Its carrier is the separately affine polynomial over `ℂ`, with
`K₁ = {z | z ≠ 0}`, `K₂ = ∅`, `Φ(z₁,z₂) = z₁*z₂ - 1`, and contraction
`Q(z) = -1 + z`. The input zero-freeness condition holds, while `Q(1) = 0`
and `1` is outside the forbidden product; the coefficients satisfy
`D ≠ 0` and `AD - BC ≠ 0`. The counterexample relies on `K₁` not being closed.
The existing canonical positive replacement is
`LeeYangAsanoNativeCore.asano_contraction_full_of_topological_combined`,
under closed zero-excluding sets, one bounded set, and complementary-product
zero-freeness. The related both-unbounded closed-set case remains open debt;
see `docs/ASANO_COUNTEREXAMPLE_REALIGNMENT.md` for the owner trace, additional
vacuous countermodel, and verification record. This entry records a candidate
family already repaired by existing owners and adds no duplicate theorem API.
`Canonical.AsanoCounterexampleRealignmentAudit` is the companion `#print axioms`
audit of those existing counterexample and bounded-set declarations; it adds
no new witness or theorem-level instantiation.

## Nilpotency index three does not force a support Jordan associator (2026-10-27)

`Singular.MoorePenroseSectorExamples.chain3` is the real `3 × 3` shift. Its
transpose is a Moore–Penrose inverse, `chain3^3 = 0`, and `chain3^2 ≠ 0`; yet
the two supports are `diag(1,1,0)` and `diag(0,1,1)`, which commute. Hence
`HigherNilpotentAssociatorCounterexample.chain3_support_associator_zero`
proves that their unnormalized Jordan associator vanishes for every middle
matrix. This refutes the inference from a nonzero square alone to a nonzero
support associator. The exact replacement is already native to
`Core.JordanAssociatorRing`: the associator is a double commutator, and for an
idempotent endpoint vanishing for every middle input is equivalent to endpoint
commutation (`idempotent_all_associators_zero_iff`). In characteristic two,
the distinct `Singular.CharacteristicTwoOverlapCounterexample` shows even the
symmetric support overlap can vanish; the scope distinctions and older
countermodels are recorded in `docs/DRAZIN_MP_PARTITION_AUDIT.md`.

## Characteristic-two symmetric support overlap can vanish without orthogonality (2026-10-27)

`Singular.CharacteristicTwoOverlapCounterexample` uses the shift `A` and its
transpose `M` on `Fin 3 → ZMod 2`. They satisfy the four Moore–Penrose
equations and do not commute. Their support idempotents are
`p = diag(1,1,0)` and `q = diag(0,1,1)`: `p*q = q*p = diag(0,1,0) ≠ 0`,
while `p*q + q*p = 0` in characteristic two. Thus zero symmetric overlap does
not imply orthogonality, and noncommutation of `A,M` is not the same as
noncommutation of their supports. The canonical arbitrary-ring criterion is
`Core.IdempotentSymmetricOverlap.symmetric_overlap_zero_iff`: for idempotent
`p`, vanishing is equivalent to support commutation together with
`p*q + p*q = 0`. A cancellation hypothesis excluding additive 2-torsion
then recovers orthogonality; without it, the characteristic-two example is a
real boundary. The construction and criterion are also covered in
`docs/DRAZIN_MP_PARTITION_AUDIT.md`. A fresh combined locked build of the
counterexample and `MoorePenroseChiralDefectsAudit` passed (8,940 jobs, exit
0); the audited generic criterion reports `[propext]`, and the concrete MP
pair and overlap report only standard Lean axioms.

## Oblique Drazin shells do not localize the MP inverse in the reverse corner (2026-10-27)

`Canonical.ObliqueShellCounterexample` uses the actual native Drazin shells
for `obliqueA` and `obliqueD`, with nilpotent part `N` and a powerwise MP
family. Its inter-shell corner `(1,0)` is exactly `N` and has Moore–Penrose
inverse `M`, but the reverse-corner product `S₀ * M * S₁` differs from `M`
(the `(2,0)` entries are `0` and `-1/2`). Thus an MP inverse of a forward
inter-shell block need not lie in the reverse oblique corner. The canonical
replacement is conditional: `Canonical.DrazinInterShellHodge` proves that
under a self-adjoint Drazin projector and self-adjoint ambient operator,
involution reverses the shell corner and `star B` transports the local
square-zero Hodge package to that reversed corner. The example does not claim
minimality of the Drazin index or a general reverse-corner MP rule. Owner
definitions and verification boundaries are recorded in
`docs/DRAZIN_SHELL_RESOLUTION.md`. A fresh locked build of
`Canonical.ObliqueShellCounterexampleAudit` passed (3,201 jobs, exit 0); all
six printed declarations report only `[propext, Classical.choice, Quot.sound]`.

## Ordinary trace is not the graded supertrace on a Krein square (2026-10-27)

`Modular.Graded.trace_superTrace_counterexample` evaluates the identity on the
actual doubled `Fin 1 ⊕ Fin 1` complex matrix carrier: its supertrace is zero,
while its ordinary trace is two. The owner’s correction is exact, not merely
an example: `trace_krein_square_correction` expresses the ordinary trace as
the supertrace plus `2 * (tr(DᴴD) - tr(BᴴB))` for a block operator
`[[A,B],[C,D]]`; `trace_eq_superTrace_krein_square_iff` proves equality iff
the two indicated Gram traces agree. Thus the two readouts coincide only
under a balance condition on these blocks. This does not identify an
associative matrix product with the nonassociative Zorn product. The fresh
locked build of `Canonical.KreinSpinPositiveAudit` passed (8,952 jobs, exit
0); the counterexample, correction, and equivalence reports use only
`[propext, Classical.choice, Quot.sound]`. Independent semantic acceptance is
recorded in `docs/KREIN_SPIN_EXISTING_REPLACEMENTS.md`; repository-wide
discovery remains incomplete.

## Split-octonion left multiplication is not multiplicative (2026-10-27)

`Lie.SplitOctonionNonmultiplicativity.nonmultiplicativity_obstruction` gives
imaginary split-octonions `X,Y` with imaginary product for which
`L_X * L_Y ≠ L_(X*Y)`; applying the presumed equality to the concrete `ex_Z`
would force the nonzero associator to vanish. The pointwise
`explicit_counterexample` records the same failure on that test vector. This
does not refute the native algebra homomorphism from the Clifford algebra:
`SplitOctonionImaginaryAction.splitOctonionLeftCliffordRepresentation`
preserves the quadratic relation and lifts `X ↦ L_X`, but does not encode
split-octonion multiplication as an associative product. The exact
composition-defect criterion is already proved in
`OperatorAlgebra.SplitOctonionLeftMultiplicationBridge.leftMulCompDefect_eq_zero_iff`;
the broader nonassociative-to-associative obstruction is recorded above under
ordinary-matrix representations. Existing verification and scope review are
in `docs/SPLIT_OCTONION_OPERATOR_REALIGNMENT.md` (locked audit: 4,334 jobs,
exit 0; six axiom reports use only standard foundational axioms). No duplicate
Lean theorem was added; repository-wide discovery remains incomplete.

## A nontrivial real parabolic shear is not diagonalizable (2026-10-27)

`Algebra.ParabolicJordanZorn.not_similar_to_diagonal` proves that for every
nonzero real parameter `t`, the matrix `NPart t` admits no invertible basis
matrix in which it is diagonal. This is not a failure of spectral existence:
`eigenspace_one` and `eigenspace_one_finrank` prove that its only eigenspace
is the one-dimensional eigenspace at eigenvalue `1`. The canonical
replacement is its nontrivial Jordan structure:
`shear_exact_index_two` proves `(NPart t - 1)^2 = 0` while `NPart t - 1 ≠ 0`;
`ParabolicAdditiveGroupBridge.parabolic_exact_index_two` and
`parabolic_not_similar_to_diagonal` transport the claims to the parabolic
criterion. Thus the obstruction is precisely the nonzero nilpotent part, not
a missing eigenbasis theorem. This source family has related discussion in
`docs/KREIN_STAR_TRANSPORT_AUDIT.md` and
`docs/CYCLOTOMIC_OPERATOR_CORRECTIONS.md`. A fresh locked build of
`InfoGeometry.Algebra.ParabolicAdditiveGroupBridge` passed (3,137 jobs, exit
0); Lean reported existing linter warnings in `ParabolicJordanZorn.lean` and
its dependencies. Repository-wide discovery remains incomplete.

## Concrete G₂ cell factorization fails at `(k,i) = (6,2)` (2026-10-27)

`Algebra.Zorn.G2FlagFactorizationRecursion.legacy_cell6_2_factorization_false`
refutes the proposed equality between the evaluated representative at index
`2` and the selected left-Weyl-right factorization in cell `6`; the proof
checks the actual `autMatrix` image and closes the finite matrix inequality
with `decide`. The local word table instead proves a right-appended suffix
step in `G2FlagWordCertificateEval.flagRepresentative_2_eq_right_step_1`,
whereas `factorized_cell6_2_left_step` records a left-action step for the
factorized target. This orientation mismatch is a concrete obstruction to
the unqualified factorization theorem. The canonical theorem presently
available is conditional: `flagRepresentative_factorization_of_cell_certificate`
derives the global in-cell equality from an explicit
`G2CellPredecessorCertificate` carrying membership, depth, anchor, and both
carrier-aligned step equations. The certificate is a data requirement, not a
proof that such data has been constructed for all cells. Independent source
review confirmed that the cell-6 certificate is impossible, since it would
imply the refuted equality at index 2; `no_cell6_predecessor_certificate`
now proves this in Lean. The word-level right-suffix equation is not presented
as a factorization of the proposed Bruhat target. Full concrete factorization
remains open debt. A fresh locked build of
`InfoGeometry.Algebra.Zorn.G2FlagFactorizationRecursion` passed (8,985 jobs,
exit 0); existing linter/deprecation warnings were emitted in this owner and
its G₂ dependencies. A separate `lake env lean` axiom query reports only
`[propext, Classical.choice, Quot.sound]` for the counterexample, corrected
local step, and conditional recursion theorem. The new audit module and owner
passed a locked build (8,986 jobs); the new impossibility theorem reports only
`[propext, Classical.choice, Quot.sound]`. Repository-wide discovery remains
incomplete.

## The integral chiral order is proper in `M₂(ℤ)` but spans `M₂(ℚ)` (2026-10-27)

`Algebra.chiral_order_is_not_full_matrix_ring` gives an explicit integral
matrix outside the parity-constrained chiral order, so the four integral
chiral generators do not generate all of `M₂(ℤ)`. The canonical replacement
is exact: `Canonical.integerChiralOrder_eq_paritySubring` proves that their
integer span consists precisely of matrices with equal diagonal parities and
equal off-diagonal parities. The quotient is additively `ZMod 2 × ZMod 2`
(`integerChiralOrder_quotient_equiv`), hence the order has index four; after
scalar extension to `ℚ`, `integerChiralOrder_scalarExtension_rat` proves the
span is all of `M₂(ℚ)`. Thus the obstruction is integral-lattice index, not a
failure to span the rational matrix algebra. The locked build of
`InfoGeometry.Canonical.IntegralChiralCliffordOrder` passed (8,925 jobs, exit
0). A separate axiom query for the parity equality, rational span, quotient
equivalence, index, and explicit nonmembership witness reports only
`[propext, Classical.choice, Quot.sound]`. No independent semantic review was
run in this pass; repository-wide discovery remains incomplete.

## Bosonic CCR has no finite-dimensional complex matrix realization (2026-10-27)

The canonical boundary theorem is
`CARCCRFockCuntzBridge.finite_matrix_ccr_impossible`: for `0 < n`, no pair
`a, astar : Matrix (Fin n) (Fin n) ℂ` satisfies the bosonic relation
`a * astar - astar * a = 1`. Its proof applies matrix trace: the commutator
trace is zero, but the identity trace is `n ≠ 0`. The arbitrary-field
counterexample-alternative lemma
`CounterexampleAlternatives.finite_matrix_ccr_impossible` isolates the same
obstruction under `[Field K] [CharZero K]`; the characteristic-zero condition
matters because the dimension scalar could vanish in positive characteristic.
The correct finite/infinite boundary is therefore not to search for a larger
finite matrix witness: the repository keeps finite CAR and finite q-CCR
specializations separate from its actual Fock/colimit constructions. The
locked build of `InfoGeometry.Canonical.CARCCRFockCuntzBridge` passed (9,204
jobs, exit 0); an independent axiom query for both impossibility statements
and the trace identity reports only `[propext, Classical.choice, Quot.sound]`.
No independent semantic audit was run in this pass; repository-wide discovery
remains incomplete.

## Square-zero endomorphisms: range/kernel alternative to injectivity (2026-10-30)

The identifiability candidate
`Canonical.CounterexampleAlternatives.nonzero_square_zero_endomorphism_not_injective`
is a valid general theorem: over any ring and module, a nonzero endomorphism
`N` with `N * N = 0` cannot be injective. Its structural replacement is the
stronger preceding statement `square_zero_endomorphism_range_le_kernel`, which
proves `range N ≤ ker N` directly from `N² = 0`; the noninjectivity conclusion
then follows when `N` is nonzero. This is not restricted to a finite matrix
toy or to a field. The declarations are source-checked, but no fresh locked
build was available in this pass; kernel verification for this owner remains
unclaimed.

## The concrete Zorn element commutator fails Jacobi (2026-10-27)

`Algebra.Zorn.ConcreteComposition.ZornCell.Basis8.not_jacobi_commutator_concrete_zorn`
refutes the universal Jacobi identity for the commutator on the concrete
integer `ZornCell` carrier: the upper basis triple has Jacobiator
`⟨6, -6, 0, 0, 0, 0, 0, 0⟩ ≠ 0`, and the lower basis triple gives the same
readout. Thus this element commutator cannot define a `LieRing` on that full
carrier. The canonical finite alternative is the owner's exact all-basis
Akivis identity `akivis_all_basis`, which identifies the commutator Jacobiator
with the alternating associator sum; the actual standard-basis Jacobiator
remains nonzero. The companion parameterized `ZornVectorMatrix` owner proves
`commutatorJacobiator_eq_associator_alternating` and the generic witness
`commutator_jacobi_U_zero_U_one_U_two_ne_zero` under `(6 : R) ≠ 0`. These are
separate carriers; this review does not claim a proved equivalence between
the integer `ZornCell` model and `ZornVectorMatrix`.

The locked builds of `InfoGeometry.Algebra.Zorn.AssociatorObstruction` and
`InfoGeometry.Algebra.ZornVectorMatrix` passed (3,099 jobs, exit 0). A direct
axiom query reports `[propext]` for the two concrete nonassociativity/Jacobi
refutations and only standard Lean axioms for the parameterized Akivis and
Jacobiator theorems. This is kernel/build evidence, not independent semantic
QA; the repository-wide inventory remains open.

## Exact fibers of the quadratic simplex response (2026-10-27)

For `response C B x = C*x - B*x^2`, the existing reflection identity shows
non-injectivity when `C` and `B` are nonzero. The owner now proves the stronger
fiber classification `response_eq_iff_eq_or_reflection`: for `B ≠ 0`, equal
responses occur exactly when `x = y` or `x + y = C/B`. The second branch is
reflection about the parabola vertex `C/(2*B)`. The proof factors the output
difference as `(x-y) * (C-B*(x+y))`; it makes no claim about a different
response function or about causal/dynamical interpretations. This supplies a
canonical exact alternative to the bare non-injectivity witness without
adding a duplicate response API.

The locked build of `InfoGeometry.Probability.SimplexQuadraticResponseAudit`
passed (3,447 jobs, exit 0). The new declaration uses only standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`); the semantic-vacuity
gate reported zero findings, and the touched Lean files contain no
`sorry`/`admit`/custom-axiom markers. The build emitted warnings in imported
modules, so warning-free closure is not claimed. Repository-wide discovery
remains open.

## Epistemic archetype preservation field is vacuous (2026-10-27)

The proposed field
`law_of_preservation : latentEvolutionFunctor.obj = latentEvolutionFunctor.obj`
is reflexivity: it asserts no preservation property, and `Functor.obj` is a
function on objects rather than a specified law about an invariant. Any
endofunctor satisfies this field. It therefore cannot certify a graph-derived
archetype. A meaningful contract must name the preserved predicate or
structure, for example `P : C → Prop` together with
`∀ X, P X → P (F.obj X)`, or name the actual morphism-level property and prove
it for the selected functor. The repository's native category owner should be
used rather than introducing a second category interface.

Source review also narrows what is already implemented. In
`InfoGeometry.Meta.EpistemicCompiler`, `Solve` converts a heuristic string to a
Lean `Name`, while `Coagula` creates predecessor edges from input order; that
module alone does not ingest Arango graphs or infer category-theoretic laws.
However, the neighboring owners provide substantive pieces: `TypedArchetype`
in `Meta/ArchetypePipeline` indexes evidence by lifecycle status and requires
`∀ x, claim x` at `.proved`; `Meta/EpistemicCompilerIntegration` connects
typed promotion to a finite prerequisite scheduler; and
`Meta/EpistemicCompilerChain` explicitly documents itself as workflow state,
not mathematical content. These are proof gates and scheduling machinery,
not an automatic semantic translation from graph motifs to a proved invariant.
The honest architecture boundary is therefore: graph analysis proposes a
candidate with provenance; a human/owner-grounded contract fixes its carrier
and law; Lean code supplies the proof; only the kernel-checked declaration is
promoted. No new Lean abstraction is justified by the vacuous sample law.

This is a source-level counterexample review only. No source or theorem was
changed, no build was run, and the repository-wide counterexample inventory
remains open.

## A surjective projection and selected vanishing generators do not force factorization

`Omega.RecursiveAddressing.paper_recursive_addressing_prefix_site_min_visible_quotient_counterexample`
refutes the implication from surjectivity of `pi` and pointwise vanishing on a
selected family `alpha` to factorization through `pi`. The witness is
`pi = Prod.fst : ℕ × ℕ → ℕ`, `alpha = 0`, and `phi = Prod.snd`: `phi` kills
the selected generator, but varies on the fiber over zero, so no `phiVis`
satisfies `phi = phiVis ∘ pi`.

The canonical alternative is already proved in the same owner:
`paper_recursive_addressing_prefix_site_min_visible_quotient` forms the
quotient by the additive subgroup generated by all cocycle values on nonempty
triple overlaps. The projection kills those values, and every additive
homomorphism that kills them factors uniquely through that quotient. The
separate `PointwiseInvisible` theorem gives the corresponding result for an
unindexed family of values. These results do not assert factorization through
an arbitrary surjection with only selected-generator vanishing. A locked build
of `Omega.RecursiveAddressing.PrefixSiteMinVisibleQuotient` passed (3,092
jobs); Lean reported one unnecessary-`simpa` linter warning in the owner.
Repository-wide counterexample discovery remains open.

## Proved archetypes can have empty input carriers (2026-10-27)

`InfoGeometry.MetaCompiler.TypedArchetype` defines `.proved` evidence as
`∀ x : Input, claim x`. This is a sound universal statement, but `.proved`
alone does not imply that the carrier has any inhabitants. The kernel-checked
counterexample in `Meta/ArchetypePipelineCounterexamples` instantiates
`Input = Empty` and `claim := fun _ => False`; empty elimination proves the
universal evidence even though `¬ Nonempty Empty`.

The stronger consumer contract is to require an actual input witness when
non-vacuous content is needed. The companion theorem shows that a supplied
`input : Input`, together with the existing universal evidence, yields
`Nonempty Input` and the claim at that input. This does not change the existing
`promoteToProved` API or say that Lean's proof of a universal statement over an
empty carrier is unsound.

The target passed a locked build (3 jobs). Independent A-A review accepted the
counterexample and its scope; distinct QA-A independently reran the locked
build and kernel certification. The four declarations use only standard
foundational axioms or none. This closes this one reviewed counterexample
family only; repository-wide discovery remains open.

## Refreshed lexical candidate checkpoint (2026-10-27)

A current run of `tools/quality/counterexample_inventory.py --json` scanned
47,899 Lean files, emitted 19,785 lexical candidate rows (6,461 tagged
`repo-owned`), and reported zero read errors. The 31 repo-owned rows classified
as `countermodel` were reconciled against this inventory and the focused
review records, including `COUNTEREXAMPLE_EXISTING_POSITIVE_BATCH.md` and
`QUADRATIC_ARNOLD_NUMERATOR.md`; they are already represented as reviewed
families rather than new discoveries in this pass.

This result is a refreshed navigation snapshot only. The scanner is lexical,
not a Lean parser or semantic falsity detector; positive-named counterexamples
and claims without negative syntax can be missed, while ordinary negative
lemmas can be false positives. The complete objective therefore remains open.

## Duplicate indices in the G₂ candidate root family

`Algebra.Zorn.G2TwoExplicitGenerators.candidateRootFamily_one_eq_three`
proves that indices `1` and `3` give the same automorphism, and
`candidateRootFamily_not_injective` refutes injectivity of the `Fin 6`
indexing. The owner explicitly calls these entries candidates and warns that
they are not six independent root coordinates. The subgroup is generated by
`Set.range candidateRootFamily`, so its definition makes no six-element range
claim. Its separate cardinality lower bound of eight is obtained from the
embedded simple-root subgroup, not from six distinct candidates.

`Algebra.Zorn.G2SteinbergPositiveRoots.positiveRootPacket` is a distinct
`Fin 6` enumeration with its own proved injectivity theorem. This supplies six
distinct automorphisms for that packet; no equivalence with
`candidateRootFamily` is asserted or proved. The searched Zorn consumers do not
rely on candidate-family injectivity. Both owner modules passed the locked
build (3,097 jobs); warnings were emitted by imported G₂ automorphism and
basis-rigidity modules. This is a documented collision boundary and existing
replacement, not a newly discovered downstream theorem failure.

## Multi-label commit profiles refute unique single-archetype assignment

The proposed reading “each commit has `∃!` species label” conflicts with the
repository's multi-label taxonomy if “label” means one individual archetype.
`tools/infra/evolution_taxonomy.py` collects every rule matching the commit
subject/body and adds path-derived labels; it does not stop at a single match.
The Lean model stores archetypes in a `Finset`. The new theorem
`InfoGeometry.Graph.mixedArchetypeProfile_not_unique_label` gives a profile
containing both `bugFix` and `refactor` and proves that no single member is its
unique label.

The precise distinction is that a fixed commit profile has one finite-set
value, while that set may have multiple members. The theorem does not claim
that the *set-valued classifier output* is non-unique. Nor does the current
Lean model prove a codec from Python string labels (`labels[].species`) to
`ChangeArchetype` constructors. Jungian/alchemical phase names therefore
remain an application-level interpretation, not mathematical identities in
Lean.

The taxonomy target passed a locked build (3,093 jobs) and kernel certification;
the axiom report contains only standard foundational axioms or none. A-A and
distinct QA-A accepted the theorem and its scope. The overall repository audit
remains open.

## Pigeonhole collision between G₂ carriers (2026-10-27)

`Algebra.Zorn.G2PeircePrefixCarrierFacts` computes 72 nontrivial idempotents
and 63 nonzero isotropic imaginary points. The existing theorem
`no_injective_nontrivialIdempotent_to_octImIsotropicPoint` rules out an
injective map between these carriers. The companion theorem
`exists_distinct_nontrivialIdempotents_same_octImIsotropicPoint` states the
sharper canonical alternative: every map between the carriers identifies a
pair of distinct idempotents. This is an existential collision consequence
of the finite cardinality gap; it does not identify one fixed pair that
collides for every map.

The owner passed a locked build (8,940 jobs) and OpenGauss kernel axiom audit.
The new declaration reports only `propext`, `Classical.choice`, and
`Quot.sound`. Repository-wide counterexample discovery remains open.

## Bost--Connes generator equations admit the unit-projection model (2026-10-27)

`Algebra.BostConnesKMSPhaseTransition.BostConnesSystem` requires a
commutative ring and has the equation `x_star n * x n = 1`. Commutativity
therefore forces `x n * x_star n = 1` for every mode in every model. The new
`projection_mode_eq_one` theorem records this stronger canonical consequence;
`BostConnesKMSPhaseTransitionCounterexamples.unitModeSystem` separately
witnesses that the structure is inhabited. Consequently the current carrier
cannot model a proper isometry range projection. This diagnoses only this
abstract owner, not the separate, more fully specified Bost--Connes owners.

The source comments for the abstract structure and scalar lemmas were narrowed
to match their formal types: `kms_projection_expectation` is only the scalar
identity `weight * 1 = weight`, not an expectation under a state; weight
multiplicativity is not derived from a time evolution; and the numerical
phase predicates alone do not prove KMS uniqueness or symmetry breaking. The
owner and counterexample audit passed a locked build (8,927 jobs) after the
stronger universal conclusion. The new declarations report only
`propext`, `Classical.choice`, and `Quot.sound`. Repository-wide counterexample
discovery remains open.

## Mediality of the concrete 36-element table (2026-10-27)

The former `Omega.StableArithmetic.MedialityFailure` definition used a sparse
handwritten operation while describing it as a restriction of the audited
table. That provenance claim was false: for instance, the sparse operation
gave `op 17 0 = 28`, whereas `NonAffineTable.stable_audit_non_affine_table_op`
gives 10. The file now imports and checks the actual table operation. The
explicit mediality witness `(a,b,c,d) = (0,0,9,0)` evaluates the two sides to
28 and 32, so the audited table is non-medial. The locked owner build passed
(3,093 jobs). This statement applies to that finite table only; it makes no
claim about other operations or classifications. Repository-wide
counterexample discovery remains open.

## Separate non-affine identity refutation on the 36-element table

`Omega.StableArithmetic.NonAffineTable.stable_audit_non_affine_refutation`
is a distinct countermodel family, not the preceding mediality witness. Its
explicit operation on `Fin 36` satisfies
`x = op y (op x (op y (op y x)))` for every `x,y`, but does not satisfy
`op x x = op (op (op x x) x) x` for every `x`. At `x = 0`, the owner records
`op 0 0 = 17` and the nested right-hand value `11`, so the failed identity is
witnessed concretely. `Omega.StableArithmetic.NonAffineWitness` contains a
second spelling of the audited table and proves the same failure directly at
zero. These are finite magma statements only; they do not classify all
36-element operations. This family was hidden from the scanner's 30-row
`countermodel` category because its declaration is named `refutation`; the
fresh name-based cross-category search found it under `negative-boundary`.
Source review only in this pass; no fresh locked build was run.

## Additional counterexample families with explicit repaired hypotheses

Source review of two further repo-owned countermodel candidates confirms that
each has a native corrected theorem alongside the boundary witness:

- `Omega.CircleDimension.ResidualEntropyLowerBound` refutes the unqualified
  lower-bound signature at `(b,r,k,t,R) = (1,1,2,4,2)`. The corrected theorem
  assumes `0 < t` and `k ≤ r`, in addition to the finite injective encoding,
  and proves `(r-k)*b + Nat.log 2 t ≤ Nat.log 2 R`.
- `Omega.Conclusion.RanktwoSmithBlindclassBooleanPrimeblockTorsor` refutes the
  formula at `(a,b)=(0,0)`, where the gcd/lcm quotient has degenerate zero
  inputs. Its corrected theorem assumes both inputs are positive and proves
  the unitary-divisor count `2 ^ h.primeFactors.card` for
  `h = lcm(a,b) / gcd(a,b)`.

These are scoped repairs of the stated formulas, not claims that all related
entropy or divisor theorems have been audited. Both owner modules passed a
locked build (3,097 jobs, exit 0). Repository-wide discovery remains open.

## Finite Möbius lookup is not the global arithmetic function

`InfoGeometry.Arithmetic.PhysicsRiemannHypothesisFinite.muPaper` is an explicit
table on inputs through 12 and returns zero on every larger input. Tracing its
repo-owned uses found no consumer treating it as the global Möbius function;
the importer describes the examples as finite. To make the scope executable,
the owner proves `muPaper_eq_zero_of_gt_twelve` and, using Mathlib's canonical
`ArithmeticFunction.moebius_apply_prime`, proves that for every prime `p > 12`,
`muPaper p` differs from `ArithmeticFunction.moebius p`. The result is also
instantiated at 13. This is a counterexample to extending the lookup globally,
not a defect in the finite examples. The owner passed a locked build (3,093
jobs, exit 0) after the general statements were added.
Repository-wide discovery remains open.

A focused follow-up on other repo-owned finite fallback definitions found
three scoped uses with matching consumers: the Golay generator coefficient
formula is used under `k < 23` and separately made periodic modulo 23;
`pickPoissonZ` is consumed in the characteristic-polynomial sum over
`Finset.range 4`; and `xiTerminalCollisionNodeResidue` is used only to state
the five explicit residue/Legendre-sign entries in its table proposition.
These checks are limited to those definitions and their direct source
consumers; they are not a general scan of all finite tables in the repository.

## Tripotency of an element does not imply tripotency of its inner derivation (2026-10-27)

The generic positive result already exists as
`Canonical.GrassmannianBundleCyclotomicOrientability.adjoint_idempotent_cubic`:
for every associative ring and idempotent `P`, the inner commutator satisfies
`ad_P^3(X) = ad_P(X)`. A nearby tripotent-element API (`P^3 = P`) must not be
confused with the stronger idempotent hypothesis. The new matrix witness in
`Physics.TripotentAdjointCubicCounterexample` uses the non-diagonal operator
`p = [[1,1],[0,-1]]` and `e₁₂`: it proves `p^3 = p`, `p^2 ≠ p`,
`p*e₁₂ ≠ e₁₂*p`, `ad_p(e₁₂) = 2 e₁₂`, and
`ad_p^3(e₁₂) = 8 e₁₂`. Thus the idempotent theorem is the canonical corrected
statement; the element-tripotent hypothesis alone is insufficient. The
focused counterexample module passed its locked build and OpenGauss T1–T17
screen. This result is one scoped counterexample family, not a completeness
claim for the repository inventory.

The same module now records `ad_one_eq_zero`: for the idempotent `P = 1`, the
inner derivation vanishes on every operator. This shows why the general law
`ad_P^3 = ad_P` is an annihilating identity, not necessarily the *minimal*
polynomial of `ad_P`. The focused target rebuilt (8,926 jobs), and the kernel
axiom audit passed for all 11 declarations with only standard foundational
axioms.

## Operator-coefficient chiral block square (2026-10-27)

`Attention.MetriplecticAttentionDynamics.chiral_bipolar_sq` is correctly
restricted to real entries, where the two off-diagonal products commute. Its
generalization to a noncommutative coefficient operator ring is instead
`chiralBlock x y ^ 2 = diag(x*y, y*x)`, as proved in
`Attention.NoncommutativeChiralBlockSquare`. The exact corrected criterion is
that this square equals the repeated-entry block `diag(x*y, x*y)` iff
`x*y = y*x`. Matrix units in the coefficient algebra give a concrete
noncommuting witness, and the outer block matrix algebra also has an explicit
noncommutativity witness. The target passed the strict OpenGauss screen,
file-specific proof-proxy gate, and locked Lake build (8,924 jobs). Independent
A-A and QA-A reviews accepted the mathematics after a wording correction; the
OpenGauss kernel/axiom audit also passed for all 13 declarations, using only
`propext`, `Classical.choice`, and `Quot.sound`. The wording correction was:
`scalarDiagonal` is a repeated matrix coefficient, not necessarily a real
scalar multiple of the outer identity. This repairs the operator-coefficient
extension; it does not refute the original real-coefficient theorem.

## Attention obstruction trace sign boundary (2026-10-27)

`Attention.MetriplecticAttentionDynamics.balancedPositiveAttention_counterexample`
is a concrete positive row-stochastic matrix with positive diagonal-core trace
but zero trace of the chiral obstruction, while the obstruction matrix itself
is nonzero. The corrected general identity is
`trace (chiral_obstruction M) = M₀₀ - M₁₁`; positivity of both diagonal entries
only gives positivity of the separate diagonal-core trace. This refutes the
stronger “positive diagonal implies nonvanishing obstruction trace” inference,
not the positive-trace theorem for the diagonal core. I repaired the owner’s
explicit noncommuting matrix-unit witness and rewrote the positive-trace proof
to use both hypotheses directly. The focused screen, proof-proxy gate, locked
build (3,093 jobs), and kernel/axiom audit of all 20 declarations passed; the
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Secondary normalization is not additive (2026-10-27)

`Probability.GromovPermutationNormalization.normalization_non_additive_counterexample`
proves `(1+1)/(2+3) ≠ 1/2 + 1/3`, refuting unweighted additivity of
secondary normalization. The canonical replacement is the mass-weighted
identity `normalization_sum_eq_mass_mixture`, under the necessary condition
that every zero-mass component has zero numerator. The pooled nonnegative
weight theorem proves this condition for nonnegative component data, including
zero-mass blocks; probability normalization separately assumes positive total
mass. The owner passed the strict screen, proof-proxy gate, locked build (3,093
jobs), and kernel/axiom audit for all six declarations, with no rejected axioms.

## Attention readout coordinates: exact identifiability criterion (2026-10-27)

The owner `Routing.AttentionInteriorFiber` has a concrete collinear-value
counterexample: two distinct strictly positive normalized rows have the same
fixed-value readout, and both rows are realized by finite softmax logits. Its
canonical replacement is `unique_probability_coords_at_positive_iff`: at a
strictly positive normalized row, uniqueness among nonnegative normalized
coordinates is equivalent to affine independence of the complete indexed
value family. For dependent values, `exists_positive_kernel_line` gives a
nontrivial interval of equivalent interior coordinates; the fiber direction
space is exactly the homogeneous decoder kernel, with dimension computed by
rank-nullity. This concerns value-coordinate identifiability, not uniqueness
of arbitrary network parameters. The current owner passed strict screening,
proof-proxy gate, locked build (8,933 jobs), and a kernel/axiom audit of all 20
declarations; no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`
were reported.

## Operator Cayley–Dickson star anti-multiplicativity boundary (2026-10-27)

`NCG.OperatorCayleyDickson` defines a pairwise `Star` and a signature-indexed
product `mulMu`; it does not install a multiplication instance or prove that
this `Star` is anti-multiplicative for `mulMu`. On the generator `j = (0,1)`,
the exact criterion is
`star (mulMu μ j j) = mulMu μ (star j) (star j) ↔ star μ = μ`.
The new `NCG.OperatorCayleyDicksonStarCounterexample` proves this criterion
and refutes the unrestricted claim with noncommuting real `2×2` matrix
coefficients. This only disproves the arbitrary-signature claim; it does not
characterize all signatures for which anti-multiplicativity holds on every
pair. The focused build and kernel axiom audit passed. In the owner, the
coordinatewise additive-group construction and the displayed quadratic
identity proof were repaired so the imported module compiles; the build still
reports linter warnings.

## Owner Zorn root derivation and total-weight defect (2026-10-27)

`Canonical.ZornChannelDerivations.rootXY_leibniz` verifies one contragredient
coordinate root action directly against the owner's `OpZornMatrix` product,
whose contraction and transverse term are `-dot` and `skewCross`. The total
vector weight does not have an unconditional derivation law: its exact
Leibniz defect is the pair of negative sums of three owner `skewCross` terms
in `totalVectorWeight_defect`. Thus the failure depends on coefficient
characteristic; in characteristic three this particular defect vanishes.
The source does not claim that the exhibited root action exhausts all
derivations or establishes an iff classification by `sl₃(Z(A))`. The new
module built in a locked 3,095-job Lake run (exit 0); the imported owner emits
pre-existing linter warnings.

The separate real split-Zorn owner `Lie.CanonicalZornDerivationDimension`
proves a 14-parameter linear model for its derivations. Its companion
`Lie.CanonicalZornDerivationBeyondSL3` gives a parameter derivation sending
`U 0` to an element with diagonal coordinate `1`, so it fails the stated
grade-preservation property of the standard block `sl₃` action. This refutes
identifying the full derivation algebra of that real split-Zorn carrier with
the grade-preserving `sl₃` action. It is not a classification for arbitrary
noncommutative coefficient rings. The focused locked build passed (3,106 jobs);
warnings came from the imported canonical vector-matrix bridge.

## Operator-valued Zorn alternativity obstruction (2026-10-27)

`Canonical.NCZornAlternativityAudit` works with the displayed `NCZornElement`
product over `BdGBlock ℚ = M₂(ℚ)`. For the upper-coordinate test element with
coefficients `a,b` and the pure upper diagonal element with coefficient `d`,
the two sides of left alternativity have `sigma_minus 2` coordinates
`(ab-ba)d` and `0`. The new
`left_alternativity_sigma_minus_two_eq_iff` states the exact equality
criterion for that coordinate; `left_alternativity_obstruction` and
`bdg_left_alternativity_fails` turn nonzero commutators into a failure of the
full law. The corresponding right-side coordinate is `0` versus
`d(ab-ba)`, with its exact criterion in
`right_alternativity_sigma_minus_two_eq_iff`; the BdG matrix-unit witness
refutes right alternativity as well. These coordinate criteria do not assert
that vanishing of the selected coordinate suffices for equality of the full
products. The focused locked build passed (3,096 jobs); warnings came from
imported BdG and Zorn owners.

## Trace of a commutator needs commutative coefficients (2026-10-27)

`OperatorAlgebra.NoncommutativeAssociativeGeometry.matrix_trace_lieBracket_eq_zero`
correctly assumes a `CommRing` coefficient type. The new
`OperatorAlgebra.NoncommutativeMatrixTraceCounterexample` witnesses why that
assumption matters: two off-diagonal block operators over the noncommutative
coefficient algebra `M₂(ℝ)` have a nonzero coefficient-valued trace of their
commutator. The outer block operators also fail to commute. Thus the canonical
trace-zero claim cannot be extended to arbitrary noncommutative coefficient
rings. The canonical replacement is
`matrix_trace_lieBracket_eq_sum_entry_commutators`, proved for arbitrary
`[Ring R]`: `trace (x*y - y*x) = ∑ i, ∑ j, (x i j * y j i - y i j * x j i)`.
It records precisely the coefficient commutators that obstruct cancellation.
The focused strict screen and proof-proxy gate passed; the locked owner build
passed (8,954 jobs). The kernel axiom audit passed for all eight declarations
with only `propext`, `Classical.choice`, and `Quot.sound`; two independent
read-only reviews approved the witness and its scope.

## Concrete left-regular commutator defect on the Zorn carrier (2026-10-27)

`Algebra.AkivisLeftRegularBridge.leftRegular_commutator_obstruction_apply`
identifies the defect with the negative associator under the alternative
associator-swap law. The stronger map-level identity
`leftRegular_commutator_obstruction_eq_neg_associatorOperator` says the full
linear-map defect equals `-associatorOperator x y`; it is proved under the same
explicit alternative associator-swap hypothesis. The native specialization
`Algebra.AkivisLeftRegularObstructionCounterexample`
specializes this to the native Zorn vector-matrix carrier: the pair
`(U 0, U 1)` has a nonzero left-regular commutator-obstruction map, witnessed
by evaluation at `U 2` and the existing nonzero associator theorem. This is a
finite concrete failure of the left-regular map to intertwine the carrier Lie
bracket; it does not assert that endomorphism composition fails Jacobi (it
satisfies Jacobi by associativity).

The target build passed (3,103 jobs); the generated kernel axiom audit passed
with only `[propext, Classical.choice, Quot.sound]`. The path-scoped strict
trap screen, staged proof-proxy gate, and semantic-vacuity gate passed. The
repo-wide diff gate and automated QMS preflight were blocked by unrelated
pre-existing staged files absent from `HEAD` and staged header failures; they
do not indicate a finding in this new file. Independent read-only semantic
review approved the witness and its scope; kernel acceptance is established
separately by the locked build and axiom audit above.

## Nonzero self-cross for noncommuting matrix operators (2026-10-27)

`Canonical.ThreeColorOperatorCrossCommutator.operatorCross_self_eq_zero_iff`
is the canonical alternative: the operator-valued self-cross vanishes exactly
when its three coefficient pairs commute. The new
`Canonical.OperatorCrossMatrixCounterexample.operatorCross_self_ne_zero`
instantiates this with two off-diagonal matrix units in `M₂(ℝ)`, making the
first self-cross coordinate their nonzero commutator. This refutes importing
the alternating self-cross law from a commutative-coefficient vector cross
product into the noncommutative operator carrier.

The target build passed (3,096 jobs), and the kernel axiom audit passed for all
three declarations with only `[propext, Classical.choice, Quot.sound]`. The
path-scoped strict trap, staged proof-proxy, and semantic-vacuity gates passed.
The broader automated QMS preflight is still rejected by unrelated staged
header failures. Independent read-only semantic review approved the matrix
witness and confirmed the theorem's scope is only this vector in `M₂(ℝ)`.

## Characteristic-two boundaries for Zorn symmetries and grade extraction (2026-10-27)

`InfoGeometry.Canonical.FiveGradeCharacteristicObstructionCounterexample`
uses the owner `OpZornMatrix` and `opEulerFiveGrading` over the genuinely
noncommutative coefficient ring `M₂(ℤ/2ℤ)`. Its matrix units do not commute,
but negation is the identity in characteristic two. Consequently all three
owner double-sign maps `zornKleinX/Y/Z` collapse to the identity, so the
unqualified claim of a faithful `V₄` action over every noncommutative ring is
false. The same module exhibits a nonzero grade-zero operator annihilated by
the owner’s unnormalised quartic grade-zero extraction polynomial, showing
that the scaled extraction identity alone does not give a universally
faithful projector in arbitrary characteristic. These counterexamples do
not refute the owner’s pointwise multiplicativity, group-relation, or
scaled-extraction identities where those exact statements hold.

The focused locked target build passed (3,095 jobs). The build reports
pre-existing owner linter warnings and two unnecessary-sequence-focus
warnings in the counterexample module; no independent semantic review or
axiom audit has yet been recorded for this entry.

## Owner-resolved counterexample families: Freudenthal, Arnold numerator, and Krein trace (2026-10-27)

Three additional lexical counterexample candidates were traced to their Lean
carriers, exact theorem statements, and constructive replacements:

- `Exceptional.FreudenthalSymplecticMixedTripleCounterexample` refutes the
  proposed universal mixed-triple symmetry for the existing
  `mixedSymplecticBracket`. The owner’s exact alternative is
  `tkk_mixed_jacobi_plus1_component`, which identifies the relevant Jacobi
  component with the difference of the two rank-two operator actions; for a
  set of charges, `tkk_mixed_jacobi_on_iff_pairing_zero` characterizes its
  universal vanishing by pairwise symplectic orthogonality. The corrected
  `symplecticContactLieAlgebra` is a separate bracket construction; this does
  not assert that the legacy total TKK bracket satisfies Jacobi.
- `Geometry.QuadraticArnoldNumerator.numerator_counterexample` gives a
  concrete nonzero ambient numerator (value `52`). The owner’s corrected
  statement is conditional: `numerator_zero_of_displacement_minors` proves
  vanishing from all displacement minors being zero, while
  `displacement_minors_of_numerator_zero` proves the converse when the
  relevant quadratic factor is nonzero. No quotient or divisibility claim is
  inferred from the ambient polynomial identity.
- `Modular.KreinPotentialTrace.trace_superTrace_counterexample` refutes
  unconditional equality of the ordinary trace and supertrace Krein
  expressions. `trace_krein_square_correction` gives their exact block-trace
  correction, and `trace_eq_superTrace_krein_square_iff` states the precise
  equality criterion as equality of the two Gram traces.

The three owner targets built in one locked run (3,112 jobs); their associated
Freudenthal contact, Arnold vanishing, and Krein trace audit modules replayed
successfully (8,952 jobs). The selected Freudenthal and Krein audit outputs
reported only `[propext, Classical.choice, Quot.sound]`; the Arnold audit
module also replayed. A fresh focused build of
`InfoGeometry.Geometry.QuadraticArnoldVanishingAudit` passed (3,099 jobs,
exit 0); all ten printed declarations report only `[propext,
Classical.choice, Quot.sound]`. This records three verified families, not a
complete semantic census of all lexical candidates.

## Galois–Zorn fixed-sector claim corrections (2026-10-27)

`Canonical.GaloisG2FixedSectorConsequences` formalizes owner-aligned
consequences using the actual `OpZornMatrix` product: the unnormalised
sign-trace reconstruction, fixedness of the three sign traces, the exact
`zornKleinX` coordinate fixed-locus characterization under additive
2-torsion-freeness, and the sign-correct x-axis encoding into `M₂(A)`.
The owner associativity theorem is reused for that axis sector.

This prevents several overstatements in the motivating narrative. In
characteristic two the sign action is not faithful; unnormalised traces are
not generally idempotent projections; the plus-sign matrix encoding is not
compatible with the owner multiplication; and the owner results do not imply
that every proper subgroup fixed locus is associative, that the full
automorphism group is exactly `A₄`, or that GNS/K-theory/gauge conclusions
hold without their additional hypotheses. See
`docs/GALOIS_G2_FIXED_SECTOR_CLAIM_AUDIT.md` for the corrected claim table.

The final locked target build passed (3,095 jobs). OpenGauss Gate 4 kernel
certification passed for all public declarations; the reported axiom sets are
subsets of `[propext, Classical.choice, Quot.sound]`, with no rejected axioms.
The scoped semantic-vacuity audit reports zero findings. The repository-wide
staged proof-proxy gate remains blocked by ten unrelated malformed/missing
copyright headers in other files; the bridge itself has the required header.

The follow-up `Canonical.GaloisG2MatrixRingEquivalence.mul_val_eq_owner`
closes a compatibility gap in the transported subtype ring: it proves that
the subtype product's underlying value is the ambient owner Zorn product.
Without this lemma, the abstract `Equiv.ringEquiv` alone only identifies the
transported ring and does not establish compatibility with the multiplication
on `OpZornMatrix`. The lemma reuses `axisXMatrix_mul` and the channel
coordinate reconstruction; its focused locked build passed (3,096 jobs).

## Current lexical scan reconciliation (2026-10-27)

A fresh run of `tools/quality/counterexample_inventory.py --json` against the
current worktree scanned 47,913 physical Lean files and emitted 19,800
candidate rows, of which 6,476 are tagged `repo-owned`; there were zero read
errors. The repo-owned lexical categories are 31 `countermodel`, 361
`obstruction`, 66 `identifiability`, and 6,018 `negative-boundary` rows.
These are declaration-level navigation counts, not counts of false theorems
or distinct mathematical counterexamples.

The 31 current `countermodel` rows were compared against the source-reviewed
family records above. Twelve declaration names were not literal text matches
in this log, but their families are already represented: five fixed-metric
shear witnesses are covered by the fixed-metric projector covariance entry;
the transformed binary-barrier witness by the nonlinear log-odds barrier
entry; the collinear attention witness by the exact probability-fiber entry;
three `MultiPrimeSpectrum` witnesses by the singleton-spectrum/pair-value
entry; and the residual-entropy and rank-two Smith witnesses by the additional
source-grounded batch. Thus this scan added no distinct source-reviewed
countermodel family. This reconciliation was performed by reading the current
owner declarations and matching each family to its existing constructive
replacement; it does not certify every lexical candidate.

The scan still contains 361 `obstruction`, 66 `identifiability`, and 6,018
`negative-boundary` rows. The aggregate does not identify how many are already
covered by older family records, so it is not a valid unresolved-work count.
Their per-declaration status needs source-level reconciliation. Many are valid
conditional theorems or boundary lemmas rather than counterexamples; the
scanner cannot decide that distinction. Result artifact:
the scan output is ephemeral and was not retained as a repository artifact.


## Current replay of named countermodel owners (2026-10-28)

A single locked Lake invocation replayed 23 current owner/audit targets covering
the explicitly named repo-owned countermodel families: signed-radius and
reflection, symmetry localization, fixed-metric projectors, Gramian and Peirce
signs, barrier and harmonic estimates, Freudenthal/Jacobi, Arnold numerators,
Krein kernels/traces, split-octonion representation, spin mixing, normalization,
attention fibers, and the Omega examples. It completed successfully (9,376
jobs, exit 0). This establishes compilation for those selected targets only;
it does not semantically review every declaration in them or cover the 359
lexical obstruction family and 12,047 negative-boundary matches.

## Tracked-surface lexical refresh (2026-10-28)

`counterexample_inventory.py --tracked` scanned 27,961 Lean files with zero
read errors and emitted 12,539 candidate declarations: 30 countermodels, 359
obstructions, 103 identifiability boundaries, and 12,047 negative-boundary
matches. These are lexical counts across tracked/unignored files, including
work and audit surfaces; they are navigation data, not counts of unresolved
mathematical counterexamples. The current source-reviewed batch below is only
one family within that inventory.

A mechanical cross-reference of the 30 repo-owned `countermodel` candidates
against this ledger found a name or owner-family mention for all 30. This is
only a coverage pointer: it does not certify that each entry's current owner,
corrected theorem, dependents, and build evidence have been freshly rechecked.
The negative-boundary and obstruction categories are much larger and still
require semantic triage.

## Obstruction-name triage: witnesses versus positive criteria (2026-10-28)

A targeted read of further lexical `obstruction` matches confirmed they are not
all counterexamples. `Algebra/H3ZornJordanObstruction` explicitly records that
its historical sparse pair satisfies the Jordan product law; the owner
`H3ZornJordanIdentity.TJordanCommutation_proof` closes the global law from the
quadratic-representation identities. Thus the two declarations ending in
`_proof` are positive refutations of an old candidate, not countermodels.
`DihedralArtinI2SixSpinOrder.spin_coxeter_twelfth_lower_order_obstructions`
is likewise a positive conditional power-order package; the `orderOf` theorem
states the exact-order conclusion only with its explicit lower-power
hypothesis. `Algebra/Zorn/AssociatorObstruction` is a genuine concrete
nonassociativity/Jacobi witness, and its finite Akivis identities give the
exact alternating-associator correction. The general owner identities are in
`Algebra/AkivisIdentity` and `NCG/ZornCommutator`.

The current locked replay of these owners together with
`AkivisLeftRegularBridge` passed (3,124 jobs, exit 0). Existing deprecation and
linter warnings remain. This triage illustrates why name-based “obstruction”
counts require semantic review.

## Peirce anomaly-generation owner replay (2026-10-28)

The current `NCG.AnomalyGradeGeneration` owner and its four direct dependencies
(`ZornCommutator`, `PeirceGradingOperator`, `TrialitySingletLieDerivation`,
`CausalPoset`) built successfully together in a locked run (3,099 jobs, exit
0). The owner proves the four-component Peirce decomposition, the actual
`skewCross`-valued homogeneous product/associator formulas, and exact
component-vanishing criteria. Its statements distinguish “defect decomposes
into grades” from the stronger and generally invalid inference “every nonzero
defect generates a specified grade.” Existing warnings in the large
Albert–Cayley–Dickson owner and this file remain; this was not a warning-free
build or an independent semantic review.

## Singular Moore–Penrose support anomalies (2026-10-28)

Two nearby witnesses have different exact resolutions and should not be
collapsed into one slogan:

- `Singular/CharacteristicTwoOverlapCounterexample` gives a noncommuting
  Moore–Penrose pair of `3 × 3` matrices over `ZMod 2`. Its symmetric support
overlap is zero while the product of the two support idempotents is nonzero.
  The owner-level theorem `Core.IdempotentSymmetricOverlap.symmetric_overlap_zero_iff`
  supplies the arbitrary-ring correction: for idempotent `p`,
  `p*q + q*p = 0` iff `p*q = q*p` and `p*q + p*q = 0`. The witness now proves
  both nonzero support product and this exact decomposition in
  `support_product_nonzero` and `support_overlap_anomaly_components`.
- `Singular/HigherNilpotentAssociatorCounterexample` uses the real length-three
  shift: its cube is zero and square is nonzero, while the two Moore–Penrose
  supports commute and the support Jordan associator vanishes for every middle
  matrix. The existing general criterion
  `Core.JordanAssociator.idempotent_double_commutator_zero_iff` is the
  structural explanation; no additional wrapper theorem was needed.

The locked target `InfoGeometry.Singular.CharacteristicTwoOverlapCounterexample`
built successfully (8,927 jobs). Its `#print axioms` output contains standard
Lean axioms only. This is a source-verified family, not closure of the full
lexical inventory.


## Split-octonion left-regular obstruction and associator correction (2026-10-28)

The witnesses in `Lie/SplitOctonionNonmultiplicativity` refute the claim that
left multiplication is a multiplicative representation into the associative
endomorphism algebra. The general owner theorem `associatorOperator_apply`
identifies `L_(x*y) - L_x ∘ L_y`, evaluated at `z`, with the carrier
associator. Under the explicit alternative-law hypothesis,
`leftRegular_commutator_obstruction_apply` gives the corresponding signed
commutator defect; the same owner separately proves Jacobi for endomorphism
commutators. Thus the carrier associator defect does not imply Jacobi failure
in the associative operator algebra. The native Zorn specialization obtains
the required alternative associator swap from the actual product. No duplicate
theorem was added. A fresh locked build of
`InfoGeometry.Algebra.AkivisLeftRegularBridge`,
`InfoGeometry.Lie.SplitOctonionOperatorRealignmentAudit`, and
`InfoGeometry.Canonical.UnifiedGeometryOperatorSignificanceAudit` passed
(9,285 jobs, exit 0). Their audits report only standard Lean axioms; imported
owners still emit existing warnings.

## Asano–Ruelle counterexample and corrected endpoint theorem (2026-10-28)

The unrestricted claim has explicit vacuity witnesses in
`AsanoRuelle/UnrestrictedFalse` and related owners. The wrapper's former
`CorrectedAsanoRuelleClaim` was not yet a theorem: it stated closed sets and
zero exclusion but omitted the boundedness hypotheses required by the actual
Möbius pole-escape result. The claim now includes closedness, boundedness,
zero exclusion, and zero-freeness on the two-variable complement. Its proof
converts these inputs to the native `ZeroFreeOutside` and signed-product
definitions, then applies
`asanoContract_ne_zero_outside_signedProduct_of_closed_bounded_zeroFree_all_branches`.
This preserves the D=0, rank-one, and nondegenerate branches proved by that
owner; it does not overstate an unrestricted theorem. The locked target
`InfoGeometry.AsanoRuelle.AsanoRuelleCounterexample` built successfully
(8,963 jobs, exit 0). The first attempt exposed wrapper namespace/binder
mismatches and was corrected before the successful build.

## Peirce reflection/tangent characteristic-two anomaly (2026-10-28)

`Core/PeirceTangentCounterexample` exhibits a noncommuting `2 × 2` matrix
over `ZMod 2` whose reflection anticommutator vanishes although the
Grassmannian tangent equation fails. The owner `Core/PeirceTangent` gives the
exact defect identity
`(2*p - 1)*x + x*(2*p - 1) = 2 • (p*x + x*p - x)`.
Its universal correction
`reflection_anticommutes_iff_diagonal_corners_two_torsion` characterizes the
additional solutions in every characteristic: both diagonal Peirce corners
are killed by doubling, while the off-diagonal corners are unrestricted.
When doubling is injective, the reflection criterion is equivalent to
tangency; the explicit `ZMod 2` witness shows why that hypothesis cannot be
omitted. This is a resolved anomaly family, not a new theorem request; no
duplicate API was added in this audit pass.

## Higher-nilpotent support-associator witness: independent source audit (2026-10-28)

The present `lean/InfoGeometry/Singular/HigherNilpotentAssociatorCounterexample.lean`
uses the actual noncommuting `3 × 3` matrix shift `chain3` and its transpose.
The source proves `chain3 ^ 3 = 0` and `chain3 * chain3 ≠ 0`; its Moore–Penrose
support idempotents are respectively `diag(1,1,0)` and `diag(0,1,1)`. These
supports commute although `chain3` and `chain3.transpose` do not. The proposed
implication from a nonzero square (or nilpotency index three) to a nonzero
support Jordan associator is therefore false on this operator carrier.

The exact replacement is already in the native arbitrary-ring owner:
`Core.JordanAssociator.symm_associator_eq_double_commutator` identifies the
unnormalized Jordan associator with the double commutator of its endpoints,
and `idempotent_double_commutator_zero_iff` / `idempotent_all_associators_zero_iff`
prove that, when the first endpoint is idempotent, vanishing of that defect
(respectively for one input / every middle input) is equivalent to commuting
endpoints. Thus the witness is explained by support commutation; it does not
assert associativity of the full matrix algebra's Jordan product or infer
support commutation from nilpotence.

Independent source review followed the exact definitions and proof terms in
`MoorePenroseSectorExamples`, `HigherNilpotentAssociatorCounterexample`,
`Core/JordanAssociatorRing`, and `MoorePenroseChiralDefects`. The locked build
of `InfoGeometry.Singular.HigherNilpotentAssociatorCounterexample` and
`InfoGeometry.NCG.AnomalyGradeGeneration` passed (3,187 jobs, exit 0). The
counterexample's `#print axioms` reports `[propext, Classical.choice,
Quot.sound]`; the arbitrary-ring idempotent criterion reports
`[propext, Quot.sound]`. Existing warnings in imported Moore–Penrose and
Albert–Cayley–Dickson owners remain; this is a focused family review, not a
repository-wide closure result.

## Stale characteristic-obstruction path

An earlier ledger entry names
`InfoGeometry.Canonical.FiveGradeCharacteristicObstructionCounterexample`,
but that module path is absent from the current checkout: it is not returned by
`rg --files lean`, and the matching path/name occurs only in this ledger. The
old description is therefore historical navigation context, not current
source evidence; its stated build and axiom status were not replayed in this
pass. The tracked inventory does not establish whether the former source was
renamed, removed, or exists only outside this checkout.

## Peirce reflection/tangency anomaly: full-ring correction (2026-10-28)

The current source family is `Core.PeirceTangent` plus its characteristic-two
matrix witness. Its exact general statement is not merely the conditional
reflection/tangency equivalence. For any idempotent `p` in any ring and any
`x`, `tangent_iff_diagonal_corners_zero` identifies the first-order tangent
equation with vanishing of both diagonal Peirce corners. The companion
`reflection_anticommutes_iff_diagonal_corners_two_torsion` proves that
reflection anticommutation is equivalent, in every characteristic, to
annihilation by doubling of those same corners. Thus the anomaly is precisely
the two-torsion in the diagonal Peirce components; the off-diagonal tangent
corners remain unrestricted. Injective doubling recovers the familiar
equivalence, while the existing noncommuting `2 × 2` matrix over `ZMod 2`
exhibits its failure without replacing the general operator-ring theorem.

The dependent `SuperGrassmannian.SignedPullbackMatrixBoundary` reuses that
witness and proves invariance for arbitrary matrix-valued graded fields under
the signed identity pullback. `Canonical.PeirceParityBoundaryExamples` records
the separate support-difference boundary examples. The focused locked build of
`InfoGeometry.Core.PeirceTangentCounterexample`,
`InfoGeometry.SuperGrassmannian.SignedPullbackMatrixBoundary`, and
`InfoGeometry.Canonical.PeirceParityBoundaryExamples` passed (8,973 jobs,
exit 0). This closes this family at the theorem/source level; it does not
certify the remaining lexical inventory as semantically reviewed.

## Noncentral corner compression and cyclic trace (2026-10-28)

`Algebra.CornerCompressionTraceCounterexample` uses noncommuting integral
`3 × 3` matrices and a noncentral idempotent projection. The sandwich
functional `X ↦ Matrix.trace (P * X * P)` is not cyclic: the explicit
enter/leave-corner pair gives unequal compressed product traces. Consequently
it cannot factor through the additive commutator quotient. This is an anomaly
of the compressed functional, not of the ambient matrix trace.

The corrected general structures are already present. `Algebra.CyclicQuotient`
defines the additive module quotient by the linear span of commutators, and
`Algebra.CyclicMatrixCurvature.cyclicTrace` composes the full matrix trace with
the coefficient cyclic class. Its `cyclicTrace_mul_comm` holds for matrices
over an arbitrary associative coefficient ring after passing to that
quotient. The distinction is exact: the quotient is an additive module, not a
ring quotient, and compression by a noncentral projector does not inherit
cyclicity. The focused locked build of
`InfoGeometry.Algebra.CornerCompressionTraceCounterexample` and
`InfoGeometry.Algebra.CyclicMatrixCurvature` passed (1,615 jobs, exit 0).

## Fixed-metric Moore--Penrose shear: promote the named witness (2026-10-28)

The current `Canonical.ConformalProjectorAgreement` counterexample had a
scope gap: its `ProjectorPair` record required only idempotency, although the
names described the metric-side values as Moore--Penrose projectors. I closed
that gap in the owner by adding explicit inverses for the two rational shear
matrices and proving the four Penrose equations for each. The new
`shear_metric_complements_are_penrose_projectors` theorem identifies the
stored metric complements as `1 - A†A` for those verified pairs. The existing
shear calculation then remains a genuine noncommuting matrix witness that a
fixed Euclidean metric does not transport its Moore--Penrose projector by
arbitrary similarity.

The correct general statement remains `MetricTransport.penrose_projectors_similarity_iff`:
fixed-metric covariance is equivalent to commutation of both source supports
with the Gram operator `g†g`. Transporting the metric restores covariance.
The new owner proof and its exact transport dependencies passed the locked
build of `InfoGeometry.Canonical.ConformalProjectorAgreement` (3,180 jobs,
exit 0). The `ProjectorPair` abstraction elsewhere still records idempotence
alone; this addition certifies the concrete shear data and does not silently
upgrade every abstract pair to Penrose data.

## Higher support spectrum is not determined by singleton marginals (2026-10-28)

The three current `Omega.CircleDimension.MultiPrimeSpectrum` countermodel
declarations are one coherent finite-support result. For distinct `p,q`, the
families `{{p},{q}}` and `{{p,q},∅}` have identical values on every singleton
query, but their `{p,q}` spectrum values are `0` and `1`. The exact corrected
statement is already proved by `higher_spectrum_counterexample_singleton_formula`,
`higher_spectrum_counterexample_pair_values`, and the combined
`paper_cdim_higher_spectrum_not_determined_by_marginals`; the companion
`higher_spectrum_counterexample_Aprime_piecewise` gives the full piecewise
formula for the second family. This establishes non-identifiability from
singleton marginals on the declared `Finset (Finset Nat)` carrier. It does not
establish a claim about arithmetic prime spectra beyond that formal carrier.
The locked build of `Omega.CircleDimension.MultiPrimeSpectrum` passed (3,092
jobs, exit 0); no duplicate theorem was added.

## Split-octonion/Cuntz/colimit intake: bridge and gap audit (2026-10-28)

The new intake combines several existing but separately owned structures. The
source-grounded boundary is:

* `Lie.G2FromSplitOctonions` and `Lie.RealSplitOctonionG2Classification`
  establish the concrete split-octonion derivation Lie algebra, its finrank
  14, and spanning by the named standard derivations. The latter owner
  explicitly distinguishes this Lie-algebra result from a proved global
  automorphism-group equivalence. These statements do not by themselves
  construct an `E₈` lattice, a Günaydin representation, or a mass-gap model.
* `Algebra.Cuntz.CuntzNAlgebra` owns the actual abstract star-ring relations
  `Sᵢ* Sⱼ = δᵢⱼ 1` and `∑ Sᵢ Sᵢ* = 1`. `Topology.CuntzCantorSpectralTriple`
  explicitly keeps Clifford and spectral-triple laws behind separate witness
  fields. By contrast, the legacy `GrandUnification.CuntzCantorBoundary`
  proves only a sum-to-one identity for three scalar trifactor components.
  Its comments now state that this does not define a Cuntz representation or a
  Cantor action.
* `Canonical.TensorTowerColimit` proves compatibility of a specified linear
  cone with iterated bonding maps and conditional survival under an explicit
  kernel-lifting hypothesis. The current `GrandUnification.PureSpinorContinuumColimit`
  packet stores finite orbifold values independently of its direct-limit
  operations; its anomaly equation is the explicit additive identity for
  translation and negation. Its comments now delimit that scope. Neither owner
  supplies a type-III factor, a Yang--Mills field, or scaling-invariant mass
  gap.
* The corrected mass-gap statement is already formalized in
  `Millennium.YangMillsMassGapAudit`: under only per-state positive coupling,
  every positive threshold admits a state with positive total energy below
  that threshold, so there is no uniform positive lower bound. A uniform
  lower bound on the coupling-squared values is a sufficient additional
  hypothesis. This audits that abstract energy model; it is not a proof or
  disproof of the Yang--Mills existence-and-gap problem.

The three edited owner files passed their locked builds:
`InfoGeometry.GrandUnification.CuntzCantorBoundary` (3,096 jobs),
`InfoGeometry.GrandUnification.PureSpinorContinuumColimit` (8,936 jobs), and
`InfoGeometry.Millennium.YangMillsMassGapAudit` (3,093 jobs), all exit 0.
The proposed combined map from split-octonion data through Cuntz dynamics and
the module colimit to a Yang--Mills mass gap remains an open bridge obligation;
the separate owner theorems do not compose without explicit maps and proved
compatibility laws.

## Reflection symmetry counterexample and its certification hypothesis (2026-10-28)

Reviewed `Arithmetic.SarnakLocalCertification` together with its direct
consumers in `LectureStructureAndRandomness`, `ReflectionZeroCount`, and
`SarnakLocalCertificationTests`. The witness `counterexample_f(z) = z(z-1)`
is invariant at the zero-set level under `z ↦ 1 - conj(z)`, but has zeros at
both 0 and 1, so reflection symmetry alone does not confine zeros to the fixed
line `Re(z)=1/2`. The module proves this as
`zero_reflection_does_not_imply_confinement`.

The corrected theorem is the existing `CertifiedRegion.zero_on_critical_line`:
for a reflection-invariant carrier on which the function has at most one zero,
any zero in that carrier is fixed by reflection and hence lies on the line.
`covered_zeros_on_critical_line` and its finite-height and all-height variants
then require explicit coverage of the zeros by such regions. The finite
`ReflectionZeroCount` route is distinct: reflection pairs off-line points, and
odd cardinality of a finite invariant zero set forces a fixed point. These are
valid conditional certification mechanisms; they do not certify that the
required regions cover all zeros of the actual Xi function.

The focused locked build of the owner, its tests, and these three direct
consumers passed (8,942 jobs, exit 0). The printed axiom dependencies were
`[propext, Classical.choice, Quot.sound]`. Existing linter warnings remain in
the replayed `CompletedZetaSouriauDInfinityThermodynamics`,
`ActualRiemannXiEntireBridge`, and test file; this review did not modify them.
The broader counterexample inventory remains incomplete.

## Lie/Jordan boundary-operator defects (2026-10-30)

`OperatorAlgebra.LieJordanBoundaryMatrices` contains three explicit matrix
witnesses for claims that fail without the omitted operator hypotheses. The
first refutes the bare mixed-difference formula
`ad_u J_v - ad_v J_u = J_[u,v]` on a non-diagonal idempotent's off-diagonal
Peirce corners. The corrected owner theorem
`LieJordanBoundaryCalculus.lie_jordan_difference` retains the exact defect:
`J_[u,v] + 2 • orientedTransport(u,v)`, where
`orientedTransport(u,v)(x) = u*x*v - v*x*u`. The second witness shows that
`u*u = 0` need not make `ad_u` square to zero; the general identity
`ad_square_of_square_zero` computes the square as `-(2 • (u*x*u))`. The
canonical square-zero differential is instead the doubled `boundary` on
`A × A`, whose square is `liftOp(ad_(u*u))`; `boundary_square_zero` therefore
has the precise square-zero premise. The third witness separates centrality
relative to the pair-generated quadratic element from centrality in the
ambient algebra. These are genuine noncommutative matrix examples, not
commutative scalar reductions. The witnesses and corrected general formulas
are in distinct owners. The focused locked build of
`InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus` and
`InfoGeometry.OperatorAlgebra.LieJordanBoundaryMatrices` passed (8,948 jobs,
exit 0). Existing linter and deprecation warnings in imported owners remain;
this is targeted kernel replay, not independent semantic QA.

## Krein-metric ket-bra adjunction (2026-10-30)

`CliffordWeyl.SpinorBilinearSoldering.ordinary_adjoint_not_dirac_solder_exchange`
refutes the claim that ordinary conjugate transpose exchanges the two
finite-spin ket-bra operators. The witness uses the existing noncommuting
off-diagonal pair `-J_plus` and `J_minus` in the native signature-(1,1)
matrix model. The corrected general theorem is
`solder_metric_adjoint`: for a Hermitian involution `η`, the exchanged
adjoint is `η * (solder η l r).conjTranspose * η = solder η r l`.
`diracAdjoint_solder` connects this identity to the existing Dirac-adjoint
API. This correction is metric-twisted adjunction; it does not assert positive
definiteness or identify the construction with right octonionic multiplication.
The locked build of `InfoGeometry.CliffordWeyl.DiracSolderAdjoint` and
`InfoGeometry.Canonical.AdjointCovarianceRealignmentAudit` passed (3,188 jobs,
exit 0). The audit reports only `[propext, Classical.choice, Quot.sound]` for
the adjunction theorem and finite witness. Existing deprecation and imported
Moore–Penrose linter warnings remain; no warning-free claim is made.

## Group-inverse transport needs the missing commutation law (2026-10-30)

`QuantumContext.IntertwinerAlgebra.groupInverse_intertwines_of_laws_needs_hQ_comm`
shows that five individual absorption/intertwining equations do not imply
transport of the proposed inverse: the `2 × 2` nilpotent exchange pair makes
the target conclusion fail. This is deliberately not a counterexample to the
bundled `IsGroupInverse` theorem. The source-level repair is explicit:
`groupInverse_intertwines_of_laws` assumes both commutation laws, including
`LQ * LQ_sharp = LQ_sharp * LQ`, and the full-bundle theorem
`groupInverse_intertwines` derives transport from the operator intertwiner
alone using the complete group-inverse laws. The separate witness
`nilpotentExchange_noncommutes` confirms the pair is genuinely
noncommutative. Thus the counterexample diagnoses a missing hypothesis in the
weaker interface, not failure of naturality for actual group inverses. The
locked build of `InfoGeometry.QuantumContext.GroupInverseIntertwinerAlgebra`
and its audit module passed (3,181 jobs, exit 0). The audited theorems report
only `[propext, Classical.choice, Quot.sound]`; imported Moore–Penrose
deprecation/linter warnings remain.

## Causal self-adjoint matrices need normalization for identity (2026-10-30)

`Probability.FiniteMarkovWeightedAdjoint.causalSymmetric_forcesIdentity_false`
uses the real `2 × 2` diagonal matrix `diag(-1,1)` to refute the claim that
symmetry and lower-triangular causality alone force the identity. The exact
general replacement is two-step: `symmetric_causalTriangular_isDiagonal`
proves diagonality, and `causalSymmetric_rowSumOne_eq_one` proves identity
once each row sum is normalized to one. The latter requires neither
nonnegativity nor a probabilistic interpretation. The weighted part of the
same owner separately characterizes detailed balance by vanishing stationary
edge currents and by self-adjointness under the stationary-weighted adjoint;
these are not consequences of symmetry and causality alone. The locked build
of `InfoGeometry.Probability.FiniteMarkovWeightedAdjoint` and
`InfoGeometry.Probability.FiniteMarkovWeightedAdjointAudit` passed (3,094
jobs, exit 0). The audited statements report only
`[propext, Classical.choice, Quot.sound]`; source linter and deprecation
warnings remain.

## Markov group-inverse range and stationary compatibility (2026-10-30)

`QuantumContext.MarkovGroupInverseIntertwinerFunctoriality` records two
distinct sharpness boundaries. First,
`unitRowSums_alone_do_not_intertwine_stationaryMeanMatrix` refutes omitting
stationary-row transport from the stationary-projector intertwining theorem:
the displayed row-stochastic `2 × 2` matrix has unit row sums but fails the
projector identity for the uniform stationary weight. The corrected theorem
`stationaryMeanMatrix_intertwines` assumes both unit row sums and transport of
the stationary row.

Second, the owner documents why the tempting range preimage `A*x` is wrong
for `range D` under a group inverse: at `A = diag(2,0)`, `D = diag(1/2,0)`
and `x = (1,1)`, that vector is not in `range D`, and `D` is not itself an
idempotent. The corrected `mulVec_mem_range_of_groupInverse'` uses
`A*(A*x)` as preimage; `range_groupInverse_eq` then proves equality of the
linear-map ranges using the existing opposite inclusion. The focused audit
module prints these declarations. The locked build of
`InfoGeometry.QuantumContext.MarkovGroupInverseIntertwinerFunctoriality` and
its audit passed (3,758 jobs, exit 0); the inspected declarations report only
`[propext, Classical.choice, Quot.sound]`. Existing imported-owner linter and
deprecation warnings remain.

## Block-swap reflection does not cancel the associator residual (2026-10-30)

`NCG.ReflectedAssociatorResidual` works on the existing
`AlbertCayleyDickson.SplitQuaternion.OpZornMatrix A` carrier. Its block swap
is involutive as a coordinate map, but
`blockSwap_not_multiplicative_on_witness` shows it is not an algebra
automorphism, and `witness_block_swap_associator_sum_ne_zero` refutes the
proposed universal three-term reflected-associator cancellation on explicit
noncommuting `2 × 2` integer-matrix coefficients. The owner gives the exact
replacement: `blockSwap_product_defect` computes the two signed skew-cross
defects, while `block_swap_associator_sum_eq_residual` expresses the full
three-term sum as an ordered vector residual. The iff theorem
`block_swap_associator_sum_eq_zero_iff_residual_eq_zero` states precisely
when cancellation does occur, without treating involutivity as
multiplicativity. The focused locked build of
`InfoGeometry.NCG.ReflectedAssociatorResidual` passed (3,101 jobs, exit 0).
Warnings remain in the large imported Albert–Cayley–Dickson and anomaly-grade
owners; this is targeted kernel replay, not independent semantic QA.

## Peirce coupling positivity requires a common-kernel condition (2026-10-30)

`NCG.OppositePeirceWitness.singular_square_not_posDef` gives a nonzero
off-diagonal coupling whose square has positive trace (`100`) but kills the
nonzero vector `(5,12,1,0)`. Thus nonzero coupling and positive trace do not
imply positive definiteness. The owner theorem
`OppositePeirceRealMetric.square_posDef_iff` gives the exact alternative:
the square is positive definite iff the forward and adjoint corner maps have
trivial common kernel. The owner also constructs a separate full non-diagonal
coupling with an explicit inverse to prove strict positivity is attainable.
Finally, `graded_square_not_posSemidef` proves that multiplying an odd
coupling by the Peirce reflection reverses its square, making it non-positive
semidefinite whenever the original coupling is nonzero. The focused locked
build of `InfoGeometry.NCG.OppositePeirceRealMetric` and
`InfoGeometry.NCG.OppositePeirceWitness` passed (3,114 jobs, exit 0). No
dedicated `#print axioms` audit module was found in the searched NCG owners;
the build confirms kernel acceptance, but this entry does not claim a separate
axiom audit or independent semantic review.

## Normalized averaging is a projection, not invertible transport (2026-10-30)

`Streaming.GaugeCovariantRouting.twoPointAverage_not_injective` refutes
identifying normalized two-node averaging with parallel transport: the average
maps both `(1,-1)` and `(0,0)` to zero. The exact repair in the same owner is
`twoPointAverage_eq_zero_iff`, whose kernel is the antisymmetric component,
and `twoPointAverage_idempotent`, which makes the average a retraction onto
constant-valued vectors. `twoPointAverage_reconstruction` restores the lost
contrast and recovers the input from mean plus contrast. The connection-valued
operator `routed` is a distinct construction: `routed_gauge_covariant` proves
its gauge covariance, while `flat_links_eq_reference_frames` gives the
complete-node flat reconstruction. These statements do not identify a scalar
averaging matrix with an invertible gauge link. The focused locked build of
`InfoGeometry.Streaming.GaugeCovariantRouting` passed (8,930 jobs, exit 0).
Warnings remain in imported Gibbs/conditioning owners; this is targeted
kernel replay, not independent semantic QA.

## Recheck: nonlinear-chart barrier inequality (2026-10-28)

Re-read `Convex.BinaryBarrierCoordinateHessian` and its direct consumers. The
counterexample evaluates the actual iterated derivatives at a point with
`p = 15/16` and refutes the squared affine-coordinate self-concordance
inequality after the nonlinear log-odds chart. It is not a failure of the
original interval barrier's affine-coordinate theorem. The replacement remains
the exact criterion `barrier_chart_standard_bound_iff`, together with the
global strict third-derivative bound
`barrier_chart_third_abs_lt_twice_second`; the coordinate defect theorem also
exhibits the explicit nonpositive correction `-4 * (2p - 1)^2`.

A fresh locked build of the coordinate-Hessian axiom audit, the Dikin
derivative bridge and its audit passed (8,982 jobs, exit 0). The audited
declarations report `[propext, Classical.choice, Quot.sound]`. Imported
dependencies emit pre-existing linter warnings. This confirms these local
claims and dependent bridge, not general invariance of self-concordance under
nonlinear charts or the repository-wide counterexample census.

## Krein quadratic trace versus supertrace (2026-10-28)

The finite matrix witness `Modular.Graded.trace_superTrace_counterexample`
refutes unconditional equality of the ordinary trace and supertrace of the
Krein square: at the identity operator, the supertrace is zero while the
ordinary trace is twice the dimension of the positive block. The owner-level
replacement is the exact identity
`trace_krein_square_correction`, whose correction is twice the difference
between the lower-right and upper-right block Gram traces. Over `ℂ`,
`trace_eq_superTrace_krein_square_iff` proves that equality holds exactly
when those Gram traces agree. The carrier is a full block matrix algebra;
the identity witness is used only to refute the universal trace claim, not to
replace the operator statement by a scalar model.

The focused locked build of `InfoGeometry.Modular.KreinPotentialTraceAudit`
and `InfoGeometry.Canonical.KreinSpinPositiveAudit` passed (8,952 jobs,
exit 0). The audit printed only the standard Lean axioms for the correction
and equivalence theorems. Existing linter and deprecation warnings were
emitted in imported owners; this is targeted verification, not a warning-free
global build.

## Attention readout: affine dependence creates a positive-dimensional fiber (2026-10-30)

The explicit `Routing.AttentionInteriorFiber.collinear_counterexample` gives
two distinct, strictly positive, normalized rows on three indexed values with
the same fixed-value readout; `collinear_softmax_realization` realizes both rows
with finite softmax logits. The exact owner-level replacement is
`unique_probability_coords_at_positive_iff`: uniqueness at an interior row
holds exactly when the indexed value family is affinely independent. For
dependent values, `exists_positive_kernel_line` constructs a nonzero direction
and a two-sided interval of distinct positive rows in the same decoder fiber.
The fiber's linear span is the actual decoder kernel, and
`fiber_finrank_eq_card_sub_rank` gives its exact dimension using the actual
decoder rank. This avoids replacing a rank-deficient decoder by the ambient
upper bound. `softmax_nonidentifiable` transports the result to arbitrary
finite logits at nonzero temperature.

The locked builds of `InfoGeometry.Routing.AttentionInteriorFiber` and
`InfoGeometry.Canonical.CounterexamplePositiveBatchAudit` passed (8,941 jobs,
exit 0). The audit reported only `[propext, Classical.choice, Quot.sound]` for
the inspected counterexample and fiber theorems. This is one more audited
family; repository-wide discovery remains open.

## Real Lie–Jordan matrix witnesses: idempotence and positivity have separate exact defects (2026-10-30)

`Canonical/RealLieJordanExamples.lean` contains several witnesses on the full
real `3 × 3` matrix algebra, built from a dense self-adjoint idempotent and
opposite Peirce corners that do not commute. The first obstruction is not a
general failure of an idempotence law: `one_sub_idempotence_defect` in
`Core/LieJordanGenerators.lean` proves the exact identity
`(1-k)^2-(1-k)=k^2-k`. The concrete owner theorem
`one_sub_gram_not_idempotent` supplies a nonzero matrix entry of this defect
for `k = U Uᵀ + Uᵀ U`. On the same carrier,
`skewPlusGenerator_one_sub_eq_zero_iff_real` gives the corrected general
criterion: for opposite Peirce corners over `ℝ`, the skew-plus generator
vanishes on `1-(uv+vu)` exactly when the anticommutator `uv+vu` is idempotent.

The positivity witnesses are distinct. `skew_sandwich_one_not_posSemidef`
uses a negative diagonal entry of `U Uᵀ-Uᵀ U`; it refutes positivity of that
particular skew sandwich, not positivity of every Lie–Jordan generator.
`affineOrbit_hasDerivAt` proves that the explicit affine matrix curve solves
the owner’s operator ODE, while `affineOrbit_quadratic_form` computes a test
quadratic form equal to `-(19208/3)t`. Therefore
`affineOrbit_not_posSemidef` proves that this positive initial projection
leaves the positive cone for every positive parameter. This does not assert
that a positivity-preserving semigroup exists or that every generator orbit
leaves the cone. The same owner separately records the reflection-metric
transpose sign and a negative bilinear trace value; these do not identify the
Krein form with a positive inner product.

This family was absent by declaration name from the prior inventory search.
Its exact alternatives are already kernel-proved in the source owners, so no
parallel Lean declarations were added in this pass. The focused locked build
of `InfoGeometry.Canonical.RealLieJordanExamples` passed (3,236 jobs, exit 0).
Imported-owner warnings remain; this is targeted kernel replay, not independent
axiom/semantic QA. Repository-wide counterexample discovery remains open.

## Bilateral Peirce action: separability, support, multiplicativity, and reassociation (2026-10-30)

`Canonical/TwoSidedKernelAudit.lean` collects four distinct counterexamples
that share the same left/right multiplication setting. The exact owner
`Core.PeirceBilateralAction.four_corner_expansion` gives the four coefficients
as products `(l*r, l*s, m*r, m*s)`; `weights_separable` proves their determinant
relation, so they cannot be prescribed independently. The theorem
`proper_support_not_identity` exhibits a nonzero harmonic matrix killed by
the active bilateral support. The corrected target is the active compression
`carrierSupport * x * carrierSupport`; `completed_diagonal_inverse` restores
the complementary identity sector for the completed block, rather than
claiming that the active block alone is ambient identity.

The explicit rational-matrix witness
`symmetric_sandwich_not_multiplicative` refutes multiplicativity of that
particular bilateral sandwich. Its structural replacement is the exact
composition law `bilateral_comp u v a b = bilateral (u*a) (b*v)`, which keeps
the reversed order of right factors. Finally, `invalid_reassociation` is a
counterexample in the existing nonassociative Zorn carrier; the correct
replacement is the owner theorem `ZornBilateralAction.middle_moufang_operator`,
which proves the actual middle Moufang identity as an equality of linear
endomorphisms. These are four separate defects, not one universal failure of
bilateral actions or of Moufang laws. No new Lean API was needed in this pass.

The focused locked build of `InfoGeometry.Canonical.TwoSidedKernelAudit`
passed (3,251 jobs, exit 0). Imported linter/deprecation warnings remain; this
is targeted kernel replay, not independent semantic QA or a full root build.
Repository-wide counterexample discovery remains open.

## Zorn versus the specified tensor-swap braid pair (2026-10-30)

`Physics/YangBaxterZornBridge.not_projectively_equivalent` proves a scoped
non-equivalence: for `q : ℂ` with `q ≠ 0`, its Clifford-left-multiplication
generator pair is not simultaneously projectively conjugate to the specified
`q`-scaled tensor-swap pair. The replacement argument is the exact invariant
already proved in that owner: `trace_sq_LeftMulR_zero` gives squared trace zero
for the first Zorn generator, while `trace_sq_C12` gives `8*q^2` for the
comparison generator. Conjugation preserves trace and a nonzero projective
scale multiplies this invariant by a nonzero square, yielding the contradiction.
This excludes only the stated target pair; it says nothing about equivalence
to arbitrary braid or quantum-group representations. The root-level and
`External/Auto` same-named files are parallel copies, not additional
counterexample families. The focused locked build of
`InfoGeometry.Physics.YangBaxterZornBridge` passed (3,128 jobs, exit 0).
Imported deprecation/linter warnings remain; this is a targeted kernel replay,
not an independent axiom audit. Repository-wide discovery remains open.

## Split-octonion axial grading: exact negative-grade Leibniz defect (2026-10-30)

`Lie/SplitOctonionCircularZ3Grading.ellCommutator_not_derivation` and
`circularAxialGrading_not_derivation` refute derivation claims on the native
nonassociative split-octonion/Zorn carrier. The corrected local statement now
records the actual residual on the already-proved product
`rootPlus 0 * rootPlus 1 = rootMinus 2`:

`axialGrading (rootPlus 0 * rootPlus 1) -
 axialGrading (rootPlus 0) * rootPlus 1 -
 rootPlus 0 * axialGrading (rootPlus 1) = -3 • rootMinus 2`.

`rootMinus_two_ne_zero` proves this residual is nonzero. Thus this instance of
the failed Leibniz law lands in the negative root sector. It does not establish
a general theorem that every derivation defect generates complementary
Peirce grades. The focused locked build of
`InfoGeometry.Lie.SplitOctonionCircularZ3Grading` passed (8,980 jobs, exit 0)
after the two exact-defect declarations were added. Imported linter and
deprecation warnings remain; no independent axiom audit was run.

## Grassmannian reflection product: correct the orientation signs (2026-10-30)

The algebraic A₂₃/A₂₄ material is already owned by
`Core.IdempotentGraphGrassmannian` and
`Core.IdempotentGraphReflectionOrder`; it should not be duplicated as a new
24-stage monolithic file. The owner defines upper and lower graph points
`p - n` and `p + m`, their chord coordinates, overlap `V = nm + mn`, and
commutator area `Σ = nm - mn`. It proves the ordered reflection products
separately, because reversing the factors changes the result.

For the convention `S_q = 2q - 1`, the actual owner identities are
`S_upper * S_lower = 1 + 2J - 2Σ - 2V` and
`S_lower * S_upper = 1 - 2J + 2Σ - 2V`, where `J = n - m`.
Consequently the ordered commutator is `4J - 4Σ`, while the anticommutator
is `2 - 4V`. The supplied draft assigns the second ordered product to the
first and gives its commutator as `4(Σ - J)`; that sign/order claim is false
for the stated graph and reflection definitions. The owner also proves the
two orders differ on explicit noncommuting `2 × 2` integer matrices
(`matrix_reflection_products_are_order_distinct`).

These are ring identities. The transition operator `1-(q-r)^2` is not by
itself a metric, principal-angle cosine, Kähler curvature, or geodesic
distance. Likewise, an idempotent specifies a split (image together with a
chosen complement), not just an unqualified subspace. The existing owner
explicitly limits its claims to algebraic graph points, tangent equations,
chords, and ordered reflection products; no new Lean declarations were needed.

## Operator-valued Zorn multiplication: alternativity defects are ordered (2026-10-30)

`Canonical/NCZornAlternativityAudit.lean` checks the displayed Zorn product
with coefficients in an arbitrary ring `A`. For `x = upperTwo a b`, the
`sigma_minus 2` coordinate of `(x*x) * pureNPlus d` is exactly
`(a*b-b*a)*d`, while the same coordinate of `x*(x*pureNPlus d)` is zero.
For the right-alternative witness `x = pureNMinus d`, `y = upperTwo a b`,
the corresponding coordinates are zero and `d*(a*b-b*a)`. The owner proves
both exact coordinate iff criteria and derives full-product inequality when
the indicated ordered coefficient product is nonzero.

The concrete `BdGBlockQ` witnesses use `matrixE12`, `matrixE21`, and the unit
coefficient, proving failure of both global alternative laws for that
noncommutative coefficient lift. This is not a counterexample to the
commutative split-octonion Zorn algebra. The canonical replacement is the
explicit coordinate defect criterion; a vanishing witness coordinate alone
is not claimed to imply equality of the full products. The owner is imported
by `Canonical/ChiralZornAlternativityAudit.lean` and `AllExhaustive.lean`.

The owner now also proves the general necessary conditions
`leftAlternativeLaw_implies_coefficients_commute` and
`rightAlternativeLaw_implies_coefficients_commute`: global left or right
alternativity of this displayed operator-valued product forces every pair of
coefficients to commute. The proof specializes the exact coordinate criteria
at `d = 1`. This strengthens the isolated matrix witnesses into a universal
necessary condition. Conversely, `noncommutativity_produces_both_alternativity_witnesses`
constructs explicit left- and right-alternativity witnesses from any supplied
noncommuting coefficient pair, using `upperTwo a b` and unit pure-sector
vectors. Thus noncommutativity is equivalent to failure of each global
alternative law for this displayed product; no claim is made about other
Zorn variants.

The focused locked build of `InfoGeometry.Canonical.NCZornAlternativityAudit`
passed (3,097 jobs, exit 0), including the new necessary-condition and
constructive-witness theorems. `axiom_index.py --json` reports 26 declarations,
zero nonstandard axiom users, and only `[propext, Quot.sound, Classical.choice]`.
The vacuity linter reports one `no_hyp_use` warning, a regex false positive on
the multiline hypotheses `h : leftAlternativeLaw ...` and
`h : rightAlternativeLaw ...`; both are explicitly consumed in `hEq` on the
following lines. Imported Lean linter warnings remain. Repository-wide
counterexample discovery remains open.

## Zorn associator/Jacobi correction: convention and characteristic recheck (2026-10-30)

Re-reading `Algebra/Zorn/AssociatorObstruction.lean` alongside its generic
owners confirms the convention-sensitive correction. Its concrete
`commutatorJacobiatorZ` is right-nested, and its finite `akivisRhsZ` is the
matching signed alternating associator sum. `akivis_all_basis` checks only
the 8³ standard-basis triples; the generic `Algebra/AkivisIdentity.akivis_identity`
proves the left-nested Akivis identity for arbitrary elements of a
nonassociative ring, while `rightNestedJacobiator_eq_neg` accounts for the
opposite nesting sign.

For the alternative `ZornVectorMatrix` carrier, the stronger owner theorem
`zornJacobiator_eq_neg_six_smul_zornAssociator` gives the right-nested
Jacobiator as `-6` times the associator. Therefore the Jacobi obstruction is
not guaranteed nonzero in characteristics where `6` annihilates the
associator; the concrete `ZornVectorMatrix` nonzero criterion carries the
explicit hypothesis `(6 : R) ≠ 0`. The finite integer witnesses themselves
evaluate to the nonzero diagonal `(6,-6)`.

Fresh focused locked builds passed for
`InfoGeometry.Algebra.Zorn.AssociatorObstruction` (3,095 jobs),
`InfoGeometry.Algebra.ZornAlternativeLaws` (1,573 jobs), and
`InfoGeometry.Algebra.AkivisIdentity` (3,095 jobs), all exit 0. Existing
import/deprecation/linter warnings remain. This is a recheck of a family
already inventoried on 2026-10-28, not a new family or a repository-wide
completion claim.

The signed split-basis owner `Canonical/CattoGurseySplitBasis.lean` supplies
an independent concrete realization of the same boundary: its `u 0, u 1,
u 2` associator equals `uZero - uStarZero`, and
`no_injective_associative_realization` uses injectivity plus multiplication
preservation to rule out an embedding into any associative ring. Its
downstream 6|21 supermatrix owner explicitly treats the associative carrier
as separate and makes no such embedding claim. Focused locked builds of the
split-basis owner and its three direct consumers (`CattoGurseyOctonionicStandalone`,
`CattoGurseyOctonionicHadronicSuperalgebra`, and `ZornSignedCAR`) passed
together (8,940 jobs, exit 0). The basis witness is nonzero under the owner's
`[Nontrivial R]` hypothesis; the Jacobiator additionally has the separate
characteristic factor `-6`, so its nonvanishing requires `(6 : R) ≠ 0`.

## `External/Auto/FusOctonionKKS`: scalar proxy is not an octonion/KKS witness (2026-10-30)

The owner `External/Auto/FusOctonionKKS.lean` compiles, but its names
overstate the mathematical carrier. It sets `Q := ℚ` and defines
`octonionAssociator x y z = (x*y)*z - x*(y*z)` using rational multiplication;
the scalar expression reduces to zero by `ring`. Separately,
`octonionAssociatorObstruction` and `associatorObstructionValue` are assigned
the constant `2`. Therefore `octonion_kks_obstruction_nonzero` checks a
Boolean comparison against that hard-coded value; it does not evaluate an
octonion associator or a KKS form. Likewise, the `classicalKKS*` declarations
are literal `Bool := true` flags without a form, differential, or
nondegeneracy predicate.

The canonical algebraic alternative is the genuine nonassociative Zorn
carrier: `Algebra/Zorn/AssociatorObstruction.associator_e11_u1_u2_eq_v3` and
`associator_e11_u1_u2_ne_zero` prove an actual product-associator witness;
the generic `ZornAlternativeLaws` owner supplies the corresponding
characteristic-aware commutator/Jacobi relation. No map from the rational
proxy to a KKS structure on this Zorn carrier is present, so these results do
not prove a KKS nonclosedness theorem. The focused locked build of
`InfoGeometry.External.Auto.FusOctonionKKS` passed (3,093 jobs, exit 0), which
confirms Lean validity of its propositions, not the octonion/KKS prose
interpretation. Repository-wide counterexample discovery remains open.

## Zorn regular action: CAR holds while multiplication transport fails (2026-10-30)

`Algebra/Zorn/RegularCARVacuumSeparation.lean` separates three carriers that
must not be identified. The native Zorn product is nonassociative, its left
regular map `L : Zorn → Module.End ℝ Zorn` is linear and unital, and
composition in the endomorphism algebra is associative. Polarized
alternativity proves `regular_anticommutator`; combined with the exact raw
upper/lower Zorn products, this yields the genuine operator CAR theorems
`regular_mixed_CAR`, `regular_upper_CAR`, and `regular_lower_CAR`. Thus CAR
survives passage to these regular operators even though the map `L` is not a
multiplicative representation: `regular_action_not_multiplicative` gives an
explicit witness.

The vacuum distinction is also exact. `vacuumProjector` is the product of
three mode projectors in the associative endomorphism algebra;
`vacuumProjector_apply` and `vacuumProjector_range` identify its image with
the one-dimensional line spanned by `poleMinus`. The theorem
`vacuumProjector_ne_pole_action` proves it is not left multiplication by that
Peirce idempotent. The repaired statement is therefore the represented CAR
and rank-one vacuum projection on the regular-action carrier, not an
identification of the nonassociative Zorn multiplication with operator
composition or of the vacuum projector with a Peirce half.

The owner is imported by `Clifford/ExteriorZornCARIntertwiner.lean`,
`Algebra/All.lean`, and `AllExhaustive.lean`. Its focused locked build passed
(8,971 jobs, exit 0); existing dependency and source linter/deprecation
warnings remain. This review does not establish an exhaustive inventory.

## Regular bimodule phase claims: exact commutant and conditional obstruction (2026-10-30)

The regular-action owners give a canonical operator-algebra statement rather
than a finite-dimensional counterexample. For every associative ring `A`,
left multiplication and right multiplication commute as endomorphisms of the
regular bimodule. More precisely,
`Physics/RegularBimoduleCommutant.leftCommutant_eq_rightActionRange` proves
that the full commutant of all left actions is exactly the range of the right
regular action. The additive-map variant
`SignedNetwork/RegularBimoduleSeparation.commutant_characterization` states
the pointwise criterion `T (a*x) = a*T x ↔ T x = x*T 1`.

The Weyl-phase result has narrower hypotheses. In
`Algebra/RegularBimoduleWeylObstruction`, if `x,z` are units and
`z*x = q • (x*z)`, commutation forces `q = 1`; hence `q ≠ 1` excludes
commutation. The unit and scalar-algebra assumptions are essential to the
cancellation argument. This does not assert a Weyl relation for arbitrary
operators, nor infer a modular flow or spectrum. The matrix conjugation
lemmas separately prove the adjoint exchanges left and right actions and is
conjugate-linear over `ℂ`.

The three focused locked targets
`InfoGeometry.Physics.RegularBimoduleCommutant`,
`InfoGeometry.SignedNetwork.RegularBimoduleSeparation`, and
`InfoGeometry.Algebra.RegularBimoduleWeylObstruction` passed together (8,927
jobs, exit 0); an existing unused-simp-argument warning remains. These are
canonical positive owner results, not additional counterexample families;
they are recorded here to constrain future counterexample claims about
regular left/right actions. Exhaustive discovery remains open.

## Cuntz boundary coupling: exact coefficient criterion for commutator transport (2026-10-30)

`Canonical/CuntzBoundaryCouplingObstruction.lean` gives an embedding-specific
counterexample and its exact replacement. On its concrete two-site tensor
carrier, the raw `ZZ` coupling fails to commute with the old-site switch for
every nonzero complex coefficient. The reindexing map `concreteStep` is
injective and transports products, so the same witness applies to the
embedded boundary operator. The theorem
`boundaryZZ_commutator_compatible_iff_zero` sharpens this to an iff: for the
specified old Hamiltonian `H`, strict commutator transport across every old
observable holds exactly when the boundary coefficient `lam` is zero.

This does not rule out other embeddings, altered boundary terms, or weaker
intertwining laws. It specifically corrects the claim that this nonzero
boundary increment preserves the native `concreteStep` commutator law. The
focused locked build of `InfoGeometry.Canonical.CuntzBoundaryCouplingObstruction`
passed (3,683 jobs, exit 0); imported deprecation and linter warnings remain.
The theorem has no downstream theorem applications in the current Lean source
search, so the result is recorded as a standalone owner boundary. The complete
counterexample census remains unfinished.

## Twistor CCR cross product: separate the failed literal law from the repaired composition (2026-10-30)

The Twistor owners provide a complete, source-ordered counterexample and
replacement chain. `PenroseLiteralCrossObstruction.literalCross_line_image`
shows that the proposed triple product collapses to one line on the
symplectic-orthogonal hyperplane. The explicit nonisotropic test pair has
quadratic values `+1` and `-1`, while its literal cross product vanishes.
Consequently `candidate_not_composition` refutes norm composition for that
pair, and `candidate_not_left_alternative` refutes left alternativity for
every nonzero scalar normalization, including the printed and
norm-normalized choices.

The canonical alternative is already proved in
`PenroseWittCompositionCompletion`: the existing Witt coordinate map is
completed to a real-linear equivalence with the native Zorn carrier, and the
native Zorn product is transported back as `selectedMul`. The owner proves
its unit laws, left and right alternativity, and composition of the original
quadratic form. Crucially, `selectedMul_ne_literal_candidate` proves the
replacement is distinct from every normalization of the failed literal
candidate. `PenroseCCRPristineChain` assembles the actual operator CCR
closure, the literal-product obstruction, and the separately chosen
composition law without conflating them. This establishes no exceptional
group classification.

The focused locked build of
`InfoGeometry.Twistor.PenroseLiteralCrossObstruction`,
`InfoGeometry.Twistor.PenroseWittCompositionCompletion`, and
`InfoGeometry.Twistor.PenroseCCRPristineChain` passed (8,987 jobs, exit 0).
Existing imported linter and deprecation warnings remain. This is one
audited counterexample family; exhaustive discovery remains open.

## Native Zorn chiral exchange: involution lifts as an anti-automorphism (2026-10-30)

`Topology/NativeZornChiralExchangeTopological.lean` defines a continuous
involution swapping the upper and lower vector coordinates. The separate
product-obstruction owner proves the exact multiplication law
`nativeChiralExchange (X * Y) = nativeChiralExchange Y * nativeChiralExchange X`
for all native Zorn elements. Its explicit `U 0`, `U 1` witness proves that
the same map is not multiplicative in the original factor order. The canonical
replacement for an asserted algebra automorphism is therefore an involutive
anti-automorphism, equivalently a multiplicative map to the opposite algebra.

`Topology/NativeZornDihedralTopological.lean` combines the exchange with the
cubic charge for its dihedral readout. The owner documentation expressly
limits that result: the readout relations alone do not yield an unconditional
`S₃` action on the Zorn algebra or an external completion. A source search
found no theorem applications of the exact anti-automorphism statements
outside this focused owner family. The locked build of the exchange,
obstruction, and dihedral targets passed (8,934 jobs, exit 0); existing Zorn
and topology linter warnings remain. This is another reviewed family, not a
completion claim for the full inventory.

## Zorn-to-doubled Krein map: exact Gram form without split-norm isometry (2026-10-30)

`Krein/ZornDoubledGramObstruction.lean` expands the existing composite map
`zornToDoubleKrein` in the existing `exterior3PeirceBasis`. The theorem
`zornToDoubleKrein_kreinForm` gives its exact signed Gram coordinates: the
first four real coordinates contribute positively and the last four
negatively. This is the supported replacement for an unproved identification
with another Peirce map or an unconditional split-octonion norm isometry.

The witness is carrier-level and explicit. The image of `uPlus` has doubled
Krein self-pairing `1`, whereas the native Zorn-vector norm of `uPlus` is `0`;
`zornToDoubleKrein_not_norm_isometry` therefore refutes norm preservation for
this map. The correction retains the actual map and its Gram form instead of
discarding the construction. A source search found no applications of these
new exact declarations outside the owner. The focused locked build of
`InfoGeometry.Krein.ZornDoubledGramObstruction` passed (9,258 jobs, exit 0).
This verifies the signed Gram formula and norm counterexample; the
repository-wide inventory remains open.

## Fibonacci braid intertwiners: phase-specific square obstruction (2026-10-30)

`Fibonacci/FibAnyonSpectralObstruction.lean` proves a second concrete
phase realization of the same square-obstruction mechanism used by the
boundary/Fibonacci owners. Here the target matrix is built from the fifth
root `q = exp(2πi/5)`, with diagonal entries `q⁻⁴` and `q³`; the existing
Jones source generator satisfies `s₀² = -I`. The owner proves
`det (R² + I) ≠ 0`, hence `R² + I` is invertible. Therefore the first
generator equation `T*s₀ = R*T` already forces `T = 0`; the simultaneous
two-generator Hom submodule and its finrank are then proved zero. The
correct scope is this concrete phase and these matrix carriers, not all
Fibonacci braid representations.

This is a related phase-specific owner, not evidence for a new abstract
intertwiner theorem: `Canonical/BoundaryFibonacciIntertwinerObstruction`
already proves the same square mechanism for its own Yang–Baxter phase and
feeds `BoundaryFibonacciHomObstruction` and the horizon intertwiner. The
two concrete phases are separately defined and no equality between their
matrices was assumed in this review. The focused locked build of
`InfoGeometry.Fibonacci.FibAnyonSpectralObstruction` passed (3,127 jobs,
exit 0). This verifies the phase-specific zero-Hom conclusion; it does not
generalize it to every Fibonacci braid representation, and the complete
inventory remains open.

## Complementary resolvent obstruction on the unrestricted nuclear carrier (2026-10-30)

`Physics/NuclearAlgebraicResolventObstruction.lean` gives an exact algebraic
counterexample to treating the finite model compression as a complete spectral
reduction on the repository's current common carrier. The carrier is the
unrestricted sequence space `ℕ → (Fin 4 → NativeZorn)`; it has no summability
or operator-domain condition. For every real energy `E` and every nonzero
coupling `g`, the owner constructs a nonzero vacuum-sector sequence
`discardedEigenvector E omega g` satisfying the full Hamiltonian eigen-equation.
Its chosen model projection is zero, so the shifted complementary denominator
annihilates this vector. The theorem `no_left_complementary_resolvent` then
proves that no operator can be a left inverse of that denominator on the whole
carrier. Consequently a two-sided complementary resolvent is impossible in
this realization at nonzero coupling.

The canonical replacement is conditional Feshbach reduction, not a claimed
resolvent: `Physics/NuclearFeshbachReduction` proves the exact model/full
eigen-equation correspondence when a supported complementary inverse is
supplied. `Physics/NuclearFeshbachConfigurationBridge` applies that contract
to the same five-grade carrier and explicitly records that it does not
reconstruct every full eigenvector. The obstruction identifies the precise
hypothesis gap: a two-sided spectral reduction needs another carrier or
additional domain restrictions that remove the constructed complementary
eigenvectors. This result does not determine which alternative is appropriate,
and is not an analytic Hilbert-space spectrum theorem. The focused locked
build of `InfoGeometry.Physics.NuclearAlgebraicResolventObstruction` passed
(8,950 jobs, exit 0), verifying the witness and no-left-inverse theorem; the
broader inventory remains open.

## Uniform-softmax range involution anticommutes with the native Majorana (2026-10-30)

`QuantumContext/MarkovMajoranaLoxodromicObstruction.lean` specializes the
repository's actual row-softmax constructor to uniform logits on two states.
The resulting transition has entries `1/2`, its Laplacian is idempotent, and
the Laplacian itself is certified as a group inverse. For the resulting range
involution `R` and the existing Jordan–Wigner Majorana difference `M`, the
owner proves `R*M = -(M*R)` and `R*M ≠ M*R`. This refutes any commuting-axis
claim for this concrete pair; it is not evidence about arbitrary softmax
kernels or a time-dependent loxodromic flow.

The corrected construction reuses the same operators in
`QuantumContext/MarkovMajoranaCliffordResolution.lean`: their squares and
anticommutation realize the native split quadratic form `Cl11Matrix.q11`,
and `markovClifford_surjective` gives an explicit preimage for every `2 × 2`
real matrix. Thus the noncommuting pair generates the full matrix carrier
through the Clifford algebra rather than being forced into a commuting
description. The owner’s audit modules are present; a fresh locked build was
not run because the earlier shared Lake session is still pending.

## Two-coordinate skew Casimir obstruction and sharp classification (2026-10-30)

`Thermo/BipolarTwoDimensionalSkewObstruction.lean` proves that on its actual
two-coordinate real carrier, a skew linear map from covectors to vectors that
annihilates the nonzero eta covector must be the zero map. Its companion
`BipolarSkewClassification.lean` gives the sharp alternative: every skew map
on that carrier is uniquely determined by one coefficient and has the
explicit coordinate form
`α ↦ (c * α(thetaBasis2), -c * α(etaBasis2))`. Hence the Casimir premise
forces that coefficient to vanish; a nonzero reversible theta lane is
incompatible with the stated two-dimensional skew structure.

The repository's constructive alternative is the existing
`Thermo/BipolarGENERICThreeCoordinateModel.lean`, which adds an auxiliary
coordinate and proves a nonzero skew reversible operator with the eta
covector in its kernel. `BipolarGENERICRestriction.lean` records the
projection relation to the two-coordinate dissipative flow. These theorems
establish the obstruction and repair for these specified finite carriers and
operators only; they do not prove that three dimensions are necessary for
all possible GENERIC structures. The focused classification audit and its
independent limited-scope review are recorded in
`docs/BIPOLAR_SKEW_REALIGNMENT.md`; this pass did not rerun them because the
current shared Lake session remains pending.

## Q55 deck permutation monodromy cannot recover the Jones phase (2026-10-30)

`Projective/Cl55ProjectiveNullJonesDeckMonodromyObstruction.lean` lifts the
already proved braid-group quotient obstruction to the concrete `Q55`
configuration covering, conditional on two ordered exchange paths and their
Artin homotopy. Under those explicit inputs,
`q55ExchangePermutationMonodromy_eq_braidPermutation` identifies the induced
covering monodromy with the native permutation shadow. The square of the first
exchange loop is therefore pure for the finite covering, while the Jones
representation sends that same presented braid square to `-I`. The theorem
`q55JonesRepresentation_not_factor_through_exchangeDeckMonodromy` rules out
every postcomposition `S₃ → GL₈(ℂ)` as a way to recover the Jones
representation from this finite deck monodromy.

This is a genuine representational obstruction, not a claim that a richer
local system or another covering cannot carry the Jones phase. It also does
not construct the exchange paths or prove the Artin homotopy: those remain
hypotheses in the Q55 bridge. Its canonical general base is already
`ProjectiveNullBoundaryJonesPermutationObstruction`, whose corrected endpoint
is precisely nonfactorization through `B₃ → S₃`. The Q55 owner specializes that
result to covering monodromy without changing its scope. Source review only;
the pre-existing locked build remains pending, so this owner has not been
recompiled during this pass.

## Positive-weight detailed balance eliminates strict one-way transitions (2026-10-30)

`Probability/CausalDetailedBalanceObstruction.lean` sharpens the already
recorded symmetric-causal matrix correction. Its theorem
`causal_detailedBalance_offDiagonal_zero` uses only a strictly positive
weight, lower-triangular support (`i < j → P i j = 0`), and detailed balance
to prove every off-diagonal entry is zero. Adding unit row sums gives
`causal_detailedBalance_rowSumOne_eq_one`, hence `P = 1`; entrywise
nonnegativity is not needed. This rules out a nontrivial stochastic kernel
that is both strictly one-way causal in this support convention and reversible
for a positive stationary weight.

The scope-preserving alternative is not to retain detailed balance and the
one-way mask simultaneously. The existing
`Physics/FiniteMarkovReversibilization.weightedSelfPart_detailedBalance`
constructs the weighted self-adjoint part on the same matrix carrier; its
`weightedSelfPart_eq_zero_iff` shows its support is the union of the original
two directed supports when entries are nonnegative. Thus reversible averaging
restores detailed balance but can add reverse edges and change the causal
support. The earlier `FiniteMarkovWeightedAdjoint` witness remains a separate
claim: symmetry and causality without row normalization need only imply
diagonality, not identity. Source review only in this pass; the existing
locked Lake session has not terminated, so this new owner has not been
recompiled here.

## Paired double-commutator kernels and nonuniform GNS coercivity (2026-10-30)

`OperatorAlgebra/PeirceSuperoperators/CrossoverExamples.lean` contains exact
matrix witnesses showing that the ordinary paired double-commutator kernel
is not interchangeable with the graded Hodge kernel. For the inherited
noncommuting `4 × 4` charge, `identity_doubleCommutator_kernel` puts the
identity in the ordinary kernel, while `identity_not_hodge_kernel` excludes
it from the graded kernel. The owner also records that the charge itself is
not in the ordinary kernel, and gives explicit trace-skewness and star
compatibility defects. The canonical replacement is the exact criterion in
`PeirceSuperoperators/DoubleCommutator`: the paired kernel is the intersection
of the two inner-action kernels, equivalently the centralizer of the charge
and its adjoint. It is not generally the graded kernel.

`OperatorAlgebra/TracialGNSMatrixTests.lean` separately constructs a genuine
operator Dirichlet Laplacian on the completed GNS space of the `2 × 2`
complex matrix trace. Its identity vector is a zero mode; the nonzero
commutator vector is an eigenvector with eigenvalue `9` and lies in the
orthogonal complement of the joint kernel. Therefore that complement is
nontrivial. The theorem `no_uniform_positive_scaling_bound` rules out one
positive coercivity constant uniform over every positive rescaling of the
same commutator family. It does **not** show absence of a positive bound for
each fixed nonzero scale. The exact replacement is in
`Analysis/OperatorDirichletScaling`: nonzero scaling preserves the kernel
and its orthogonal complement, while energy and the Dirichlet operator scale
quadratically; consequently any fixed bound must depend on the scale. The
two matrix families (the `4 × 4` Peirce crossover and `2 × 2` tracial GNS
example) are related by operator-kernel themes but are not the same witness.
This pass is source-level only; a focused build cannot be started while the
previous locked Lake session remains live and pending.

## Full-tree lexical inventory checkpoint (2026-10-30)

Ran `python3 tools/quality/counterexample_inventory_all_folders.py --tracked`
against the current checkout. It scanned 28,421 Lean files, reported 13,099
lexical candidate declarations (30 countermodel, 364 obstruction, 111
identifiability, and 12,594 negative-boundary), with zero read errors and
seven skipped paths. These are identifier-level candidates, not a count of
mathematical counterexamples; for example, declarations named
`obstruction_of_not_loopFlat` can be positive lemmas or logical consequences.

The 30 repo-owned declarations tagged `countermodel` were cross-checked
against the existing inventory entries. The two that a simple exact-name
comparison initially failed to match—
`ResidualEntropyLowerBound.paper_cdim_residual_entropy_lower_bound_counterexample`
and `RanktwoSmithBlindclassBooleanPrimeblockTorsor`—are already covered in the
inventory's opening summary and the earlier source-reconciliation section.
Their source owners supply corrected positive statements; they are not new
unresolved families. The wider 364-declaration `obstruction` class remains
untriaged because it also includes positive defect formulas and conditional
vanishing criteria. No repository-wide completion claim follows from this
checkpoint.

One lexical false positive inspected during triage is
`Omega/TypedAddressBiaxialCompletion/GlobalizationFlatness.lean`:
`cechObstructed` is defined as `¬ loopFlat`, and
`obstruction_of_not_loopFlat` simply extracts the corresponding balanced loop
with nontrivial residual. The owner proves the substantive positive direction
that a global section makes every balanced loop residual equal to one, by a
product telescoping argument. This minimal transition-data model does not
define a cover, Čech complex, or cohomology class, so the label “Čech
obstruction” is only local packaging and must not be read as a theorem about
Čech cohomology. Source review only; the shared locked Lake session remained
pending.

Another name-level candidate is `Omega/Zeta/XiReverseKLRadiusRenormalizationCyclicSymmetrization.lean`.
Its private lemma `xiReverseKLNonMultipleModesDisappear_false` is a proof that
the particular profile `(1,2,4,8)` is not invariant under the order-two cyclic
average; it is not itself a failed theorem. The public statement is evaluated
only at that fixed profile, where both sides of its equality characterization
are false: the entropy drop is strict, and the non-multiple modes do not
disappear. Thus the `↔` is true there but vacuous as a general equality
criterion. The source-grounded general result is currently the separate
parameterized identity in
`XiReverseKLCyclicKLDecomposition.paper_xi_reversekl_cyclic_kl_decomposition`,
which identifies the cyclic entropy-gap expression with the reverse-KL
divergence for every positive finite profile. It does not itself prove the
nonnegativity/equality characterization of that divergence. The current pass
adds `xiReverseKLCyclicKL_nonneg` and
`xiReverseKLCyclicKL_eq_zero_iff_uniform` in the KL decomposition owner,
reusing the existing finite Gibbs inequality and its equality theorem. It also
proves `xiReverseKLCyclicKL_eq_zero_iff_profile_eq_average`, identifying
equality exactly with every profile entry equaling the orbit average. The
focused locked build of `Omega.Zeta.XiReverseKLCyclicKLDecomposition` passed
(3,669 jobs, exit 0), so these results are kernel-compiled. The source review
of the name-level candidate itself added no Lean declaration.

## More lexical “obstruction” candidates are positive conditional laws (2026-10-30)

Source review of two entries in the 363-row obstruction slice found no
counterexample claim to repair. In `Canonical/AlgebraicStationarity.lean`,
`starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement`
is an equivalence conditional on exact operator agreement; it transports
stationarity across negation and does not assert that the agreement always
holds. In `Canonical/BogoliubovOptimalTransport.lean`,
`alignmentObstruction_eq_zero` follows from the certified support/kill laws,
while `chiObstruction_eq_zero_iff_alignment` and
`chiObstruction_ne_zero_iff_non_alignment` are exact owner-provided
characterizations. Their lexical labels describe named defects, not failed
theorems. This is source-level classification only; no new theorem was
needed, and both declarations remain subject to the repository's existing
build state. The remaining obstruction slice has not been semantically
triaged.

Two conformal/Weyl files were also checked because the lexical scan emits many
rows for them. `Canonical/WeylKKTAnomalyIdentity.lean` states the dilation
commutator as `-1/2` times the projector obstruction under explicit projector
agreement and commutation hypotheses; its zero-collapse theorems retain those
hypotheses, and its Einstein-residual theorem additionally assumes the source
equation. `Canonical/WeylTransportChiralBridge.lean` derives holonomy readouts
from an explicit `FlatCurvatureProjectorObstructionBridge` plus flatness. These
are conditional transport identities, not counterexamples or unconditional
claims that flatness alone determines holonomy. Source review only; no new Lean
statement was required, and this does not triage the rest of the 363-row slice.

The refreshed `--tracked` full-folder scan reproduced the recorded snapshot:
28,421 Lean files, 13,099 lexical candidates, zero read errors, and seven
skipped paths (30 countermodel, 364 obstruction, 111 identifiability, and
12,594 negative-boundary tags). A separate identifiability candidate,
`Core/PeirceMatrixRepresentation.representation_injective_iff`, is a positive
criterion for the existing non-unital representation from `M₂(R)` generated
by a nonzero dual-seed pair; it does not conflict with the no-faithful-map
theorem for a genuinely nonassociative Zorn source. The carriers and
multiplication laws differ. This source check adds no new theorem and does not
classify the remaining identifiability or negative-boundary candidates.

## Consensus readout “not a sheaf” claim reduced to its exact finite criterion (2026-10-30)

`Omega/Conclusion/ConsensusFunctorSeparatedNotSheaf.lean` takes as structure
fields both a nonzero obstruction and the implication that any global readout
forces that obstruction to vanish. Its no-global-readout theorem is therefore
conditional on those fields; the alleged self-overlap compatibility is the
tautology `a - a = 0`, and this owner does not construct a site, presheaf, or
sheaf. I added `global_readout_iff_pairwise_agreement` and
`no_global_readout_iff_pairwise_disagreement`, which state the exact finite
criterion using only the local integer family and its nonempty anchor. A
two-site datum with readouts `0` and `1` witnesses non-globalizability and
provides a concrete inhabitant of the existing structure. Both the semantic
vacuity screen and strict OpenGauss source screen pass; kernel compilation is
still waiting on the shared Lake lock. This repairs the finite consensus
statement without promoting it to a sheaf-theoretic counterexample.

## Two probe vectors do not separate unrestricted matrix operators (2026-10-30)

`Synthesis/G2Sl2SeventeenParameterProductActionBridge.lean` gives an explicit
nonzero `3 × 3` matrix annihilating both selected probe vectors, so the
two-probe separation claim fails on the full matrix carrier. The owner’s
canonical replacement is exact for coordinate probes: if `X e₀ = X e₁ =
X e₂ = 0`, then `X = 0`. This does not refute the owner’s two-probe theorem on
its smaller three-dimensional `so21LinearComb` subspace; the domain has
changed. `Synthesis/ThreeProbeReconstruction.lean` is another, separate
three-probe fiber classification on its own carrier and should not be merged
with this `3 × 3` witness. Source-level classification only in this pass.

## Clifford action noninjectivity sharpened by a kernel-dimension bound (2026-10-30)

`Lie/SplitOctonionCliffordNoninjective.lean` proves the seven-generator Clifford
representation into endomorphisms of `CanonicalZorn` is not injective from the
dimension comparison `128 > 64`. I added
`splitOctonionLeftCliffordRepresentation_kernel_finrank_ge`: rank-nullity and
the codomain rank bound give a kernel of dimension at least 64. This is the
quantitative alternative to the negative injectivity statement; it does not
claim that the action of the seven Clifford generators themselves is
nonfaithful. The new Lean statement is staged but not kernel-verified yet,
because the shared Lake build lock is still unavailable in this session.

## Positive-slice Zorn norm readout fibers (2026-10-30)

`EmergentGeometry/ZornChiralPotential.lean` exhibits distinct spatial
coordinates with the same `zornNorm` on the positive slice. The owner already
proves the readout formula `temporal² + Vec3.dot spatial spatial`; I added
`positiveSlice_norm_fiber_iff`, which characterizes every fiber at temporal
coordinate 1 by equality of those spatial quadratic values. Thus the
noninjectivity is a precise loss of directional information by this scalar
readout, not a failure of the underlying Zorn operator construction. The new
lemma is staged but still needs the focused kernel build.

## Infinity-twistor noninjectivity is its computed radical (2026-10-30)

The complex and intrinsically real `Twistor/InfinityTwistor` owners both prove
their infinity-twistor linear map is noninjective because the upper-spinor
plane is its radical. The exact replacement is already present as
`infinityTwistor_radical` and `ker_infinityTwistor` in the complex owner, and
`infinityTwistor_radical` in the real owner. This is genuine degeneracy of the
alternating form, not an invertible map with a missing proof. No new theorem
was necessary in this pass; the candidate is classified by source inspection.


## Pauli-matrix quaternion sign and corrected basis (2026-10-30)

`Canonical.UnifiedMatrixQuantumGeometryFinite.quaternion_literal_i_j_sign_obstruction`
shows that the literal assignment `i ↦ I • σ₁`, `j ↦ I • σ₂`, `k ↦ I • σ₃`
does not preserve the quaternion relation `ij = k`: its actual product is
`-I • σ₃`. The owner supplies the corrected finite matrix basis
`qI = I • σ₁`, `qJ = I • σ₂`, `qK = -I • σ₃`, and proves `qI_mul_qJ`,
`qJ_mul_qK`, and `qK_mul_qI` with the quaternion square relations. This is a
counterexample to that specific literal basis assignment, not to the existence
of a matrix realization of the quaternions. `Physics/Section32QuaternionicEmergentSpacetime`
uses the sign witness in its repaired theorem packet. Parallel sandbox owners
also contain quaternion multiplication tables; they use separately defined
carriers and do not establish that the canonical owners are definitionally
identical. Source and direct-consumer review only in this pass; the shared Lake
lock prevented a fresh kernel build, so this entry does not claim new
verification evidence.


## Character-blind gluing claim is a conditional proposition package (2026-10-30)

The lexical obstruction candidate
`Omega.Topos.paper_gluing_failure_character_blind_obstructions` does not
construct a counterexample in a site, sheaf, gerbe, or category. Its carrier
consists solely of nine arbitrary propositions. The conclusion follows from
six supplied equivalences/implications (`hKernelVisible`, `hKernelEval`,
`hEvalPureExt`, `hNonNeutral`, `hAllClassAdmissible`, `hNullGlue`). Its two
publication wrappers and `paper_gluing_failure_unique_branch_banded_gerbe`
consumer pass the same propositions and hypotheses through the package. Thus
the source proves a valid conditional implication, but does not independently
establish that any premise is inhabited or that an actual gluing failure
occurs. The canonical scope is the conditional proposition-level theorem as
written; promoting its title to an instantiated topological counterexample
would require concrete carriers, maps, and verified witnesses. This is a
source-level classification only; no new Lean theorem was needed and no fresh
build was run.


## Krein no-leakage obstruction theorem is certificate-conditional (2026-10-30)

`Arithmetic.RHRealDoubledKreinReformulation.kreinRH_of_oddObstructionCertificate`
is not an independently derived spectral-concentration result. Its input
`KreinOddObstructionCertificate C` supplies both implications needed for the
conclusion: every zero-sector state off the throat creates an obstruction, and
every zero-sector state has no such obstruction. The proof is the direct
contradiction between those fields. Repository-wide source search found the
certificate declaration and a capstone theorem that accepts it as an explicit
parameter, but no construction/instance of the certificate. Thus the
canonical theorem is the conditional chart-level implication; this source
alone does not instantiate the obstruction-vanishing/topological premise or
prove a statement about zeta zeros. This is a source-level dependency audit;
no replacement Lean declaration was needed and no fresh build was run.

## Finite-dimensional scalar-commutator characteristic boundary (source review)

`Canonical.FiniteDimensionalCCRObstruction.charTwo_commutator_eq_one` is a
concrete counterexample to extending the characteristic-zero scalar-CCR
impossibility to arbitrary fields: the two matrix units in
`Matrix (Fin 2) (Fin 2) (ZMod 2)` have commutator equal to the identity. The
owner's general replacement is
`scalar_commutator_forces_dimension_scalar_zero`, which proves over any field
that a scalar commutator with value `c` forces
`c * (Module.finrank K V : K) = 0`. Thus the characteristic-zero result
`no_nonzero_scalar_commutator` is valid under its stated finite-dimensional,
nontrivial, characteristic-zero hypotheses, while the characteristic-two
witness shows why those hypotheses cannot be dropped. This is a source-level
classification. A fresh sequential locked Lake build of
`InfoGeometry.Canonical.FiniteDimensionalCCRObstruction`,
`InfoGeometry.Canonical.CyclicTraceIsometryObstruction`,
`InfoGeometry.Canonical.ApolloniusScalarOperatorSurprisalNoGo`,
`Experimental.Sandbox.SuperGrassmannian.FiniteCCRTraceObstruction`, and
`proofs.HestenesKreinBdGPrecision` passed (9,289 jobs, exit 0). This resolves
the earlier pending-build note for the finite-dimensional CCR family. The
Hestenes/Krein owner additionally proves a balanced `16 + 16` block
supertrace readout with `superTrace32 1 = 0` while the ordinary block trace of
the identity is 32; this does not construct a CCR representation or show that
the supertrace removes the finite-dimensional ordinary-trace obstruction.
Existing imported-owner linter and deprecation warnings remain.

## Finite-matrix Cuntz trace obstruction scope correction (source review)

`Synthesis.BohmianCuntzHolomovementPoset.cuntz_finite_matrix_trace_obstruction`
proves the finite-dimensional trace contradiction for two isometries with
complete range projections, and
`no_cuntz_isometries_on_nonempty_finite_matrix` excludes such a pair on a
nonempty finite carrier. The source commentary had inferred that this forces
the specific repository UHF matrix colimit to carry an exact Cuntz
`O₂`-action. That implication is not proved by the trace calculation or by the
separate `uhf_tower_enfold_and_state_coherence_bridge`, which concerns state
and enfolding coherence. I corrected the source comments to restrict the
conclusion to finite-stage nonexistence. The repository's
`Canonical.FiniteMatrixCuntzObstruction` separately supplies rectangular
branch amplification as a finite-stage replacement; this does not assert an
exact `O₂` representation on the UHF colimit. Source review only; no fresh
kernel build was available in this pass.

## Window-6 double-irreducibility conclusion narrowed to encoded rank data (source review)

`Omega.Conclusion.Window6BoundaryDoubleIrreducibilityObstruction` previously defined
`noCompactIrreducibleModel D` without using `D`; it was merely a conjunction of a
fixed boundary-spinor statement, fixed `Unit` split bookkeeping, and `3 ≠ 1`.
That did not prove nonexistence of a compact irreducible model. The wrapper
predicate was removed. The paper-labelled theorem now states only its actual
proved content: the fixed boundary-spinor rigidity statement, the fixed split
`K₀` rank identities, and exclusion of the supplied finite simple-Lie-type
constructor under its explicitly fixed central-rank-three datum. The `D` input
selects only an element of the encoded simple-type enumeration. No actual
boundary action or derivation of its rank-three premise is established here.
As a reusable canonical replacement, the owner now exposes
`centerTwoRank_lt_three` and `centerTwoRank_ne_three` directly for every type
in its finite inductive classification; the record-level contradiction is a
specialization of that table fact. The owner passed a locked build (3,140 jobs,
exit 0); imported Omega modules emitted existing deprecation and linter
warnings.

## Fresh tracked lexical inventory (2026-10-30)

`tools/quality/counterexample_inventory.py --tracked --json` scanned 28,422
Lean files with zero read errors and seven skipped paths. The refreshed scan
emitted 13,109 lexical candidate rows: 30 countermodels, 366 obstruction rows,
111 identifiability rows, and 12,602 negative-boundary rows. Relative to the
prior ephemeral scan, 20 candidate rows appeared and 17 disappeared as the
worktree and staged source changed. Four of the newly named obstruction rows
are the exact diagonal-leak characterization and counterexample/correction
lemmas added to `Attention.MetriplecticAttentionDynamics`; their focused locked
build passed earlier in this audit. This is navigation evidence only, not
semantic coverage: it includes staged and unignored worktree files, and the
candidate parser does not prove that all counterexamples have been found or
that every row needs a repair. The refreshed JSON snapshot is
`/tmp/cc_current_20261030.json` and is ephemeral.

I reconciled the refreshed scan's 30 repo-owned `countermodel` rows against
the source-level entries in this ledger. Exact name/path matching found 23;
the remaining seven collapse into three already-audited families: five
supporting matrix identities in the fixed-metric shear witness,
`transformed_barrier_self_concordance_counterexample` (the nonlinear-chart
barrier family), and
`paper_conclusion_ranktwo_smith_blindclass_boolean_primeblock_torsor_counterexample`.
For the latter, the owner proves the exact domain theorem
`ranktwo_smith_unitary_divisor_count_iff_positive`: the claimed count holds
exactly when both inputs are positive. This reconciliation does not classify
the much larger obstruction and negative-boundary slices, and the row-to-family
mapping is source/document review rather than a scanner certification.

## Post-repair lexical refresh (2026-10-30)

After adding `Attention.MetriplecticAttentionDynamics.chiral_obstruction_trace_pos_iff`,
the tracked-source scanner reports 13,112 candidate rows (30 countermodels,
368 obstruction, 111 identifiability, and 12,603 negative-boundary), with zero
read errors and seven skipped paths. The new row is the exact sign criterion
for the already-audited equal-positive-diagonal counterexample family; it is
not a new countermodel. The 30-row countermodel slice is unchanged. The fresh
JSON snapshot is `/tmp/cc_resume_20261030.json`. The remaining lexical slices
still require semantic owner-by-owner classification.

The staged repair in `Arithmetic.PrimitiveSetsAbove` also passed its focused
locked build (3,514 jobs, exit 0) after repairing the singleton divisor-fiber
proof and the primitive/support witnesses. Existing deprecated-API warnings
remain in that owner.

## Conditional conformal-anomaly readout (2026-10-30)

The lexical inventory flags
`Canonical.ConformalInference.projectorObstruction_eq_zero_of_unitRelativeVolumeBit`
as an obstruction candidate. Source inspection shows its input is explicitly
proof-carrying: `UnitRelativeVolumeBit n M` is the equality
`relativeVolumeChangeRN n M = 1`. The readout additionally requires
`hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M`; the upstream
Kähler/log-det theorem then yields projector commutation, from which the
normal-phase package proves the obstruction is zero. This is a conditional
readout theorem, not an unconditional vanishing claim. No replacement theorem
is needed. This entry records source inspection only; no new build was run.

## Conditional incompressible Cramér–Rao projector collapse (2026-10-30)

The lexical obstruction candidate
`Canonical.IncompressibleCramerRaoActionBridge.projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_incompressible`
is a conditional consequence, not a witnessed counterexample or an
unconditional collapse. Its inputs include a
`CramerRaoNegLogVolumeAnomalyReadout`, an
`IncompressibleMongeAmpere` proof, equality of the two Moore–Penrose right
projectors, and commutation of the dilation operator with the left projector.
The proof obtains zero chiral scale from the incompressibility readout, derives
projector commutation and vanishing obstruction, then transports the explicit
left-projector commutation through the supplied right-projector agreement to
the dilation-commutator zero theorem. This is consistent with the stated
hypotheses; no replacement Lean declaration was needed. Source inspection
only, with no fresh build in this pass.

## Exact finite Krein-connection compatibility criterion (2026-10-30)

`Canonical.KreinSpinConnectionObstruction.connection_obstruction_explicit`
is an exact matrix expansion of the commutator between the specified
off-diagonal connection and exponential diagonal weight. Its companion
`compatibility_iff_mu_zero` proves that, when the off-diagonal coefficient is
nonzero, this particular commutator vanishes exactly at parameter `mu = 0`.
The statement is a finite `2 × 2` operator criterion and its explicit
hypotheses prevent it from claiming a global connection theorem. This
obstruction-name hit has a positive exact alternative already in the owner;
source inspection only, with no fresh build in this pass.

## Idempotent Grassmannian claims and reflection-order sign audit (2026-10-30)

The proposed `A₂₃/A₂₄` synthesis overlaps existing owners rather than requiring
a second 24-stage spine. `Core.IdempotentGraphGrassmannian` is imported by
`InfoGeometry.lean`; it defines the algebraic idempotent locus, upper/lower
Peirce graph idempotents, tangent displacement equations, graph absorption,
two-sided complementary-unit witnesses, chord coordinates, the chord square,
and the transition operator. `Core.PeirceTangent` proves that the linearized
equation `p*x + x*p = x` is equivalent to vanishing of the two diagonal
Peirce corners and to the fixed-point equation for the squared inner adjoint.
These are algebraic statements over an associative ring. They do not establish
a manifold atlas, a differentiable curve for every tangent vector, or metric,
principal-angle, or geodesic interpretations.

The pasted reflection product has its order-dependent signs reversed. With the
repository conventions `upperGraph = p - u`, `lowerGraph = p + w`,
`J = u - w`, `Sigma = u*w - w*u`, `V = u*w + w*u`, and
`pointReflection(q) = q - (1-q)`, the owners prove:

* `S_upper * S_lower = 1 + 2*J - 2*Sigma - 2*V`;
* `S_lower * S_upper = 1 - 2*J + 2*Sigma - 2*V`;
* their anticommutator is `2 - 4*V`;
* their commutator is `4*(J - Sigma)`.

Thus the proposed formula for `S_upper * S_lower` and the proposed
commutator `4*(Sigma-J)` are false under these definitions; reversing the
reflection order gives the stated opposite signs for the linear terms. The
identity `2 - 4*V` is an algebraic anticommutator formula, not by itself a
principal-angle cosine law. The owner’s named replacement results are
`pointReflection_ordered_products` and
`pointReflection_anticommutator_formula` in
`Core.IdempotentGraphGrassmannian`, with their ordered expansions proved in
`Core.IdempotentGraphReflectionOrder`. The locked builds of
`InfoGeometry.Core.IdempotentGraphGrassmannian` and
`InfoGeometry.Algebra.HuaBergmanZornExtensions` passed in the current pass.
The latter emitted existing imported-owner linter warnings; no warnings were
reported for the Grassmannian owner. Axiom indexing found only foundational
axioms (`propext` for the Grassmannian module; `propext`, `Quot.sound`, and one
`Classical.choice` use for the Hua/Bergman module), with no nonstandard axioms.

The graph-band laws and complementary-unit formulas are valid algebraic facts,
but descriptions such as “same kernel,” “same image,” “transverse subspaces,”
and “affine chart” require a specified module or geometric structure; they do
not follow as such from an arbitrary ring element. The owner states the actual
absorption products and two-sided inverse equations. Likewise,
`transitionOperator q r = 1 - (q-r)^2` is an operator-valued algebraic
expression. Calling it a metric, principal-angle operator, or geodesic
invariant needs extra structure absent from the owner hypotheses. The existing
`graph_chord_tangent` and `graph_midpointDefect_tangent` results prove only the
linearized idempotent equation for those directions; they do not construct
differentiable curves or a manifold tangent bundle.

Follow-up source change: the owner now also states the generic algebraic fact
`pointReflection_idempotent_involution`: for every idempotent `q` in the
associative ring, `pointReflection q = q - (1-q)` squares to `1`. This
generalizes the graph-specific involution result without adding geometric
structure. Its focused locked builds passed in this pass:
`InfoGeometry.Core.IdempotentGraphReflectionOrder` (1,222 jobs) and its
consumer `InfoGeometry.Core.IdempotentGraphGrassmannian` (3,097 jobs).

## Bergman sandwich iterate and non-involution witness (2026-10-30)

The staged `Algebra.HuaBergmanZornExtensions.bergmanOp` is the sandwich map
`X ↦ (1-u v) X (1-v u)`. Its earlier prose called it an involution, which is
not justified by the definition. I corrected the name to “Bergman operator,”
added the exact iterate formula `(1-u v)^2 X (1-v u)^2`, and added a concrete
noncommuting `2 × 2` integer-matrix witness where the idempotent base and
off-diagonal inputs make the operator send `1` to `0`; hence it cannot be an
involution. The first build exposed that a “zero on equal differences” claim
is not generally true: the two chart projections need not commute. A proposed
parameter-swap antisymmetry replacement also does not follow, because swapping
the raw parameters does not swap the distinct upper and lower Peirce images.
I removed both unsupported properties and kept only the exact commutator
identity already proved by the module. The matrix-notation import was corrected
to the module present in the pinned Mathlib tree. A focused locked build of
`HuaBergmanZornExtensions`, `Core.IdempotentGraphGrassmannian`, and
`Core.IdempotentGraphReflectionOrder` passed (3,100 jobs, exit 0). Including
`PureNonCommutativeOperatorSpine` in the same build fails: Lean reports many
unresolved goals throughout that pre-existing aggregate file, beginning at
line 107. The successful owner build does not validate that aggregate spine.

Follow-up repair pass: the aggregate file's missing `NoncommRing` import,
two Peirce-corner associativity steps, two malformed documentation-comment
openers, and three conjunction arities were corrected and staged. The locked
build still fails with 42 diagnostics (down from 54 in the first captured
build). Remaining diagnostics include timeouts in broad `peirce_abel` proof
expansion, unresolved noncommutative polynomial identities, and invalid or
incomplete A21–A24 calculations. This is a diagnostic count, not a count of
independent mathematical defects; the aggregate file remains unverified.

## Weyl flatness-to-holonomy contract boundary (2026-10-30)

The 23 lexical obstruction hits in
`Canonical.PhaseSpaceWeylCausalBridge` are mostly transported corollaries,
not independent counterexamples. Tracing the owner shows that
`WeylTransportBridge.FlatCurvatureValueBridge` carries both
`flat_to_zeroCurvatureIntegral` and
`zeroCurvatureIntegral_to_target` as explicit fields. The general theorem
`holonomy_eq_target_of_flat` composes those fields. In contrast,
`WeylTransport.finiteSumIntegrator_integrateCurvature_eq_zero_of_flat`
constructively proves the flat-to-zero-curvature-integral step for the finite
sum integrator. No theorem in this chain derives the second field, or a
holonomy target, from flatness alone. Consequently the norm and nonvanishing
endpoints in the phase-space leaf are valid conditional consequences of the
bridge contract and the stated projector hypotheses; they are not standalone
flatness-to-holonomy results. The canonical source-grounded statement is the
existing conditional theorem `holonomy_eq_target_of_flat`, with the finite-sum
curvature-zero lemma kept separate. Source inspection only; no fresh build was
run in this pass.

Further source tracing separates three other claims that are easy to conflate.
`toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator` is an exact
intertwining identity for a linear equivalence; it does not define or prove a
time-dependent flow. The dilation-source identity
`spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_from_conformal`
has the explicit hypothesis that the Drazin spectral projector commutes with
the right Moore–Penrose projector. The KKT block conclusions use the three
separate grading hypotheses on `A`, `A_MP`, and `A_D`; under them,
`projectorObstruction_eq_diagonal_blocks_of_kkt_wings` gives the diagonal-block
decomposition and the two mixed blocks vanish. Finally,
`holonomy_ne_zero_of_flat_from_conformal_of_noncommute` assumes noncommutation
of the Drazin and Moore–Penrose projectors and a
`FlatCurvatureProjectorObstructionBridge`; its nonzero conclusion follows from
the bridge's target norm plus the operator-norm zero criterion. Thus neither
the phase intertwiner nor KKT grading alone supplies a holonomy value, and the
nonzero result is a conditional theorem rather than a counterexample. The
owner files inspected were `PhaseSpaceConformalKKTBridge`,
`PhaseSpaceWeylCausalBridge`, `ConformalAnomalySource`, and
`WeylTransportChiralBridge`. Source inspection only; the active shared build
lock prevented a fresh compile in this pass.

## Conformal projector-obstruction iff statements (2026-10-30)

The lexical obstruction cluster in `Canonical.ConformalAnomalySource` includes
46 lexical rows in the current scanner snapshot, but these are not 46 failed
claims. The owner defines `projectorObstruction` as the spectral/metric
projector commutator and proves `projectorObstruction_eq_zero_iff_commute`;
the scalar scale is exactly its operator norm, and zero scale iff zero
obstruction. Under the explicit three KKT wing hypotheses, the obstruction is
grade zero and equals the sum of its two diagonal Peirce blocks; both
off-diagonal blocks vanish. These are positive conditional structure theorems,
not counterexamples and not unconditional consequences of the commutator
definition; the exact results are
`projectorObstruction_eq_diagonal_blocks_of_kkt_wings`,
`projectorObstruction_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings`,
and `projectorObstruction_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings`.
The owner also proves
`chiralScale_eq_zero_iff_projectors_commute`, using the operator norm readout.
For the dilation commutator, the exact zero iff is conditional on right
projector commutation:
`spectralProjector_commutator_dilation_eq_zero_iff_projectorObstruction_eq_zero_of_rightProjectorCommute`.
The hypothesis is essential to the stated bridge, since the preceding
commutator identity is only derived under that condition. These declarations
are canonical positive alternatives already present in the owner, not new
counterexamples. Source inspection only; no fresh build was run in this pass.

## Supercharge-to-projector nonvanishing contract (2026-10-30)

The six negative-name candidates in
`Canonical.SuperchargeEinsteinSourceBridge` are conditional implications, not
counterexamples. The precise canonical endpoint is already
`ConformalInference.projectorObstruction_eq_zero_iff_commute`: the obstruction
is nonzero exactly when the spectral and metric projectors fail to commute.
The owner theorem `projectorObstruction_ne_zero_of_compat_of_mismatch` obtains
that failure from the explicit implication stored in
`SuperchargeProjectorCompatibility`; it does not derive the implication from
the mismatch itself. The central-charge and transported-index variants first
use the proved index-transport equalities to obtain a kernel-slice dimension
mismatch, then invoke that same compatibility contract. The boundary-carrier
variants additionally require identified polarization slices, oddness of the
transported operator, boundary nonvanishing on nonzero zero-modes, and
alignment of the conformal projectors with the boundary projectors. The
canonical alternative is therefore the exact projector-commutation criterion,
with the supercharge/index bridge explicitly conditional on compatibility;
nonzero central charge alone is not asserted to force noncommuting conformal
projectors. Owner source reviewed: `SuperchargeEinsteinSourceBridge`,
`ChiralDefectIndexBridge`, `OperatorialCentralCharge`, and
`ConformalAnomalySource`. Source inspection only; no fresh build was run.

## Welded projector-correlation bridge lexical hits (2026-10-30)

The five negative-name candidates in `Quantum.WeldedProjectorCorrelationBridge`
are positive transport/readout identities, not failure witnesses. The seed is
defined as minus the channel phase-axis image of the lifted projector
obstruction; the owner proves that applying the phase axis again recovers the
obstruction, using the exact square law for that operator. Under the explicit
Moore–Penrose projector-agreement equation, the welded state phase readout is
identified with the phase-shifted two-state correlation, with same-state
specializations to the comparison-state phase form. The final derivative lemma
transports the already-owned infinitesimal correlation law at zero through the
seed identity to the comparison-metric readout. No topological interpretation
or independent anomaly-generation claim follows. These are canonical
owner-level alternatives to the scanner's lexical classification; source
inspection only, no fresh build in this pass.

## Geometric-tensor operator-lift obstruction labels (2026-10-30)

The four lexical obstruction hits in `Quantum.GeometricTensorOperatorLift` are
proved transport/readout identities. The two derivative specializations for
the lifted projector-obstruction seed follow from the general split of
infinitesimal modular transport into a gauge derivative and a
relative-modular source derivative; when the seed commutes with the gauge
part, the gauge contribution is removed and only the source readout remains.
The weld identity
`berryTwoFormJEpsOfOperator_liftedEinsteinAnomalyOperator_eq_neg_liftedProjectorObstructionOperator_of_projectorAgreement`
requires Moore–Penrose right/left projector agreement. The star-certified QGT
identity then combines that hypothesis-dependent operator equality with the
QGT theorem that the Berry form of a skew-adjoint operator is the negative
operator-metric readout. These results provide exact conditional alternatives;
they neither assert the projector agreement unconditionally nor constitute
counterexamples. The declarations are in `GeometricTensorOperatorLift`, with
the projector weld owned by `ConformalProjectorCore` and its source wrapper in
`ConformalAnomalySource`. Source inspection only; no fresh build was run.

## Xi radial Stokes counterterm lexical obstruction (2026-10-30)

The two obstruction-named declarations in
`Omega.Zeta.XiRadialStokesCurvatureCountertermObstruction` do not provide a
counterexample. The owner defines an affine scalar potential `2*r + 1 + c`,
declares its curvature to be the constant slope `2`, and defines boundary and
area integrals by the corresponding rectangle formulas. The private Stokes
lemma then proves equality by expanding those definitions; the public
paper-labelled theorem packages that equality together with counterterm
independence and the endpoint value. The canonical proved scope is this
explicit affine scalar model. There is no differential-form complex,
connection curvature derived from an exterior derivative, or link to a Xi
operator in this owner, so the theorem cannot support a general radial
Stokes/counterterm obstruction claim. Source inspection only; no fresh build
was run.

## Conductor-two Ramanujan nonrepairability name scope (2026-10-30)

The three obstruction-named declarations in
`Omega.Conclusion.ConductorTwoRamanujanObstructionNonrepairable` prove facts
about an abstract sequence `2^n`: a polynomial coefficient correction
vanishes beyond its natural degree, and the fixed logarithmic ratio
`log 2 / log(φ²)` exceeds `1/2`. The owner explicitly does not define
Ramanujan coefficients or connect this sequence to them. The canonical
mathematical statement is therefore the exact eventual-equality theorem for
finitely supported polynomial corrections, not arithmetic nonrepairability.
This lexical family supplies no counterexample to a theorem about the actual
Ramanujan sequence. Source inspection only; no fresh build was run.

## Chiral KMS preservation obstruction scope (2026-10-30)

`Canonical.ChiralKMSOwner.KMSPreservesChirality_iff_obstruction_zero` is an
exact algebraic iff over an associative ring: preservation is defined as
commutation with the supplied grading, and the obstruction is that same
commutator. `KMSPreservesChirality_mul` proves closure under products when
both factors already commute with the grading. The module header explicitly
limits the result: it constructs no modular flow or matrix exponential and
proves no KMS uniqueness theorem. The replacement for an overbroad reading is
the existing commutator criterion with its factorwise hypotheses, not a
thermodynamic claim. Source inspection only; no fresh build was run in this
pass.

## Hestenes–Kähler obstruction-name cluster (2026-10-30)

The 15 lexical `obstruction` hits in `Quantum.HestenesKahler` are not 15
negative results. Source review groups them into: (i) exact bidegree labels
for the certified and welded operator axes; (ii) vanishing of the welded axis
and its Berry readout under the explicit `operatorialIncidence` equality;
(iii) state-induced dynamics split into gauge plus source terms, with paired
gauge-only reduction conditional on the supplied `hCancel`; and (iv) readout
identities inherited from constant state-generator data, with the metric
identification requiring the explicit Moore–Penrose projector-agreement
hypothesis. These declarations are positive algebraic identities or
conditional contracts. The canonical statements already live in the owner;
no counterexample replacement API is indicated by these lexical hits. Source
inspection only; no fresh build was run in this pass.

## Spin Factor variance-floor theorem scope correction (2026-10-30)

`Quantum.ZeroPointEnergy.zero_point_energy_topological_obstruction` was only a
forwarding copy of `zero_point_energy_positive`. The latter proves a valid
finite-dimensional implication from the explicit structure field
`cramer_rao_floor` and the hypothesis that the dimension is positive. It does
not derive that floor from the Spin Factor Hessian. The supposedly topological
and thermodynamic conclusion therefore had no topological or limit content.

I removed the duplicate overclaiming theorem and corrected the module and
structure documentation to identify `cramer_rao_floor` as supplied model data.
I also removed the unused Cramer and Hessian imports, which had suggested an
unproved derivation path. The retained canonical result is
`zero_point_energy_positive`, exactly conditional on the stored lower bound.
No repository consumers of the removed theorem were found. The focused locked
build of `InfoGeometry.Quantum.ZeroPointEnergy` passed (3,168 jobs, exit 0).
The vacuity scan found no findings, and the axiom index reported only
`propext`, `Classical.choice`, and `Quot.sound`, with no nonstandard axioms.

## Exact creation-word grade classification (2026-10-30)

`Clifford.Cl55CreationWordGradeObstruction.topCreation_not_grade_two` is not
an isolated negative witness. Its owner constructs `creationWord is`, proves
nonvanishing for `List.Nodup`, and proves uniqueness of the operator grade.
I added `creationWord_grade_iff`: for every no-repeat word, membership in the
grade-`k` submodule is equivalent to `k` being the integer cast of the word
length. This gives the exact alternative statement behind the five-mode
grade-window counterexample. `Clifford.All`, `Cl55CreationWordSupport`, and the
source reconstruction audit import the owner; no new aggregator edge was
needed. The focused locked build passed (8,946 jobs, exit 0).

## Circle-dimension null-readout wrapper classification (2026-10-30)

`Omega.CircleDimension.NullReadoutObstruction.cdim_null_readout_obstruction`
is a lexical obstruction hit, not a counterexample or a derivation from
primitive budget definitions. Its hypotheses already assert each of the
three implications returned in the conclusion (`hOut`, `hCech`, `hHard`);
the proof only repackages them. A repository search found no consumers beyond
the owner file. It therefore contributes no independently proved readout
obstruction and needs no counterexample replacement theorem. This classifies
one lexical hit only; it does not resolve the remaining obstruction slice.

## Circle-dimension splitting-torsor obstruction names (2026-10-30)

All seven lexical obstruction rows in
`Omega.CircleDimension.CdimAnomalySplittingTorsorObstruction` belong to one
constructive theorem, not to refutations. For the explicit product extension
`A0 × D → D`, the owner constructs a homomorphic section from every
`h : D →+ A0`, recovers every section from its first-coordinate homomorphism,
and proves any two sections are related by a unique translation in
`Hom(D,A0)`. Its cocycle `α0 ∘ h - h ∘ αD` vanishes exactly when the
corresponding section is invariant; existence of an invariant section is
equivalent to existence of a homomorphism with zero cocycle. These are full
algebraic statements for the specified split product extension, not a claim
about arbitrary nonsplit extensions. The existing
`paper_cdim_anomaly_splitting_torsor_obstruction` is the canonical alternative;
no repair declaration is indicated. Source inspection only; no fresh build was
run in this pass.

## Total-natural multiplicative ledger collapse (2026-10-30)

Source review of `Omega.Conclusion.LocalizedColimitFiniteLedgerLinearizationObstruction`
found that its ledger homomorphism is defined on all of `ℕ` and its
multiplicativity premise quantifies over all natural inputs. Substituting
`m = 0` gives `ledger 0 = ledger 0 + ledger n`, hence `ledger n = 0` for every
`n` by additive cancellation. I added two kernel-proof candidates in the
owner: `...totalLedger_eq_zero` and the stronger
`...totalLedger_not_injective`, which needs no finite-rank or prime-relation
assumption. The existing paper-labelled prime-product theorem remains as a
specialized formulation and its docstring now records this stronger collapse.
If the intended object is a multiplicative ledger on positive naturals, the
domain or multiplicativity hypotheses must be changed; the current all-`ℕ`
contract is necessarily trivial. The focused locked build of
`Omega.Conclusion.LocalizedColimitFiniteLedgerLinearizationObstruction` passed
(3,092 jobs, exit 0), confirming the two stronger alternatives and the
existing prime-product result compile together.

## Winding-orbit closure scope and obstruction rows (2026-10-30)

The 12 lexical obstruction candidates in `Canonical.WindingOrbitClosure` are
commutation/vanishing statements, not 12 independent counterexamples. The
forward canonical result is that the exponential shift vanishes when the
generator commutes with the clock axis; for a modular transport generator,
phase-linearity supplies that commutation. The reverse equivalence is stated
only under `IsClockFaithfulExponentialBranch`, whose proposition explicitly
assumes that equality of the two exponential values implies the desired
commutation. The local gauge certificate carries this same faithful-readout
implication as a field. Thus no unconditional converse or global exponential
injectivity is proved. Detailed-equilibrium equivalences are separately
proved from the exact scale-part commutator formula and invertibility of the
clock axis.

The source header and two definition docstrings previously called the integer
branch parameter a topological winding number and claimed it maps to a
Drazin index. The owner defines only an integer-indexed `2π` clock-axis shift;
there is no Drazin-index map in the file. I corrected that prose to the
source-supported algebraic scope. The formal theorem statements and proofs
were not changed. Source review only; no fresh build was run in this pass.

## Finite-stage mass-gap predicates refuted at stage zero (2026-10-30)

`QuantumGravity.TopologicalMassGapZeroStageAudit` proves an actual
counterexample to two universal predicates. `AmplituhedronAlgebra 0` has no
columns, so it has no nonzero matrix; therefore
`TwistorMassGenesis.topological_mass_gap := ∀ n, finite_obstruction_class n`
and `ColimitTwistorMass.emergent_colimit_mass_gap ħ := ∀ n,
finite_heisenberg_obstruction n ħ` are false for every `ħ`. The owner proves
the precise finite-stage replacement: both nonzero-matrix predicates are
equivalent to `0 < n`; the latter is independent of `ħ`. It also constructs
nonzero witnesses at positive stages and transports them along the injective
matrix inclusions. This proves persistence of nonzero finite matrices only,
not noncommutativity, a topological obstruction, or a spectral gap on an
actual colimit. I narrowed the two owner modules' prose to those source-proved
facts while retaining their declarations and the audit theorems. Source
inspection only; no fresh build was run in this pass.

## Weyl/KKT anomaly closure hypotheses (2026-10-30)

The eight lexical obstruction hits in `Canonical.WeylKKTAnomalyIdentity` are
conditional closure statements and compatibility aliases. The dilation-source
identity requires both Moore–Penrose projector agreement and commutation of
the Drazin projector with the agreed projector. The zero-collapse results
additionally require zero chiral scale or the explicit Kähler identification
and unit-relative-volume witness. The transported Einstein-residual result
requires the source equation identifying that residual with the chiral scale;
nonzero projector obstruction then implies nonzero residual through the
operator-norm readout. These assumptions are carried to the owner theorems in
`WeylAnomalySource` and `ConformalAnomalySource`, so the lexical hits do not
expose an unconditional claim or a missing counterexample replacement. Source
inspection only; no fresh build was run in this pass.

## Signed Peirce transport positivity counterexample and energy identity (2026-10-30)

`OperatorAlgebra.SignedTransportMetric.skewTransport_positive_input_obstruction`
is a genuine positive-cone counterexample under the explicit hypotheses that
the arrow `a` is nonzero and square-zero. The input `a*aᴴ` is positive
semidefinite, while its signed-transport image is proved not positive
semidefinite. This refutes positivity for that signed map; it does not refute
positivity of the separate `crossTransport` map or identify the signed map as a
quantum channel.

The source-grounded replacement is structural: for every real matrix input
`x`, `skewTransport_energy` identifies the energy of the negative square with
the Frobenius norm-square of the first transport output, and
`skewTransport_energy_nonneg` proves its nonnegativity. The owner also proves
Frobenius skew-adjointness, Hermitian preservation, and equality of the kernel
of the square with the kernel of the map. `SignedTransportWitness` instantiates
the counterexample on the existing dense noncommuting `4 × 4` arrow and proves
the signed map and its square are nonzero. The focused locked build of
`InfoGeometry.OperatorAlgebra.SignedTransportWitness` passed (8,949 jobs,
exit 0); imported linter and deprecation warnings remain. This is one audited
operator-positivity family, not a completion of the lexical inventory.

## Tracked countermodel slice refresh (2026-10-30)

A fresh `counterexample_inventory.py --tracked --json` run scanned the current
tracked/staged/unignored Lean sources: 13,111 lexical candidate rows, zero
read errors, and seven skipped paths. The rows comprise 30 `countermodel`,
367 `obstruction`, 111 `identifiability`, and 12,603 `negative-boundary`
candidates. Exact source-name reconciliation of the 30 repo-owned countermodel
rows found 25 declarations already named in this inventory. The other five
are supporting shear witness equalities in
`Canonical.ConformalProjectorAgreement`; their parent fixed-metric
counterexample family and its Penrose-corrected interpretation are already
audited above. Thus this scan's explicit countermodel slice is reconciled to
the recorded families. This does not establish completeness beyond the
scanner's lexical rules and does not semantically classify the much larger
obstruction, identifiability, or negative-boundary slices. The JSON result is
ephemeral at `/tmp/cc_active_20261030.json`.

## Refutation-name coverage and ordered Grassmannian reflections (2026-10-30)

The scanner now assigns a separate lexical `refutation` category to declaration
names containing `refut`; it no longer silently merges those names into the
countermodel count. The refreshed tracked-source scan reports 13,116 rows over
28,422 Lean files, zero read errors, and seven skipped paths: 31 countermodels,
6 refutation-named rows, 368 obstructions, 111 identifiability rows, and 12,600
negative-boundary rows. Manual source review of the six refutation-named rows
finds two actual finite/operator counterexample families (`mat2Z` Jordan
associator sign and the `Fin 36` non-affine table); the CP-visible, Hecke, and
Xi entries are positive implication/arithmetic theorems despite their names.
This is why the new category remains lexical navigation, not a semantic count.
The exact false-positive declaration heads are
`paper_conclusion_cp_visible_nonrealizability_has_finite_refuter`,
`paper_hecke_e4_three_prime_refutation`,
`paper_xi_finite_prime_refutation_audit`, and
`xi_finite_prime_refutation_audit_int_eq_zero_of_natAbs_lt_of_dvd`. The
CP-visible theorem is a generic contrapositive conditional on the supplied
equivalence; the Xi theorems are divisibility-and-size implications without a
concrete residual witness. The actual Jordan sign witness is
`mat2Z_jordanAssociator_sign_refutation`; its corrected ordered identity is
recorded above.

The current Peirce graph-reflection owner also contains
`matrix_counterexample_reversed_forward_reflection_formula`, using its existing
noncommuting integer matrix-unit witness to refute the proposed forward A₂₄
sign/order formula. The canonical alternatives are the general ordered product
theorems `pointReflection_upper_mul_lower` and
`pointReflection_lower_mul_upper`; their sum gives the already stated
anticommutator law. The focused locked build of
`InfoGeometry.Core.IdempotentGraphGrassmannian` and
`InfoGeometry.Core.IdempotentGraphReflectionOrder` passed (3,097 jobs, exit
0); `git diff --cached --check` also passed.

The cross-category `witness` review also found a carrier-strengthening of an
already known state counterexample. In
`OperatorAlgebra.CantorBernoulliGeneratedCStarSpatialStateBridge`,
`spatialAnnihilator_mem_generated` places the annihilator in the concrete
generated C⋆-subalgebra, and `generatedSpatialState_not_faithful_witness`
proves it is nonzero while the restricted normalized spatial state vanishes
on its positive square `A⋆A`. The canonical statement is therefore
non-faithfulness on this generated carrier; it does not identify the spatial
state with the distinct gauge/KMS state. The proof is source-reviewed here but
was not rebuilt in this pass.

Another exact matrix counterexample is owned by
`OperatorAlgebra.CliffordDirac.MatrixModel`. For the explicit Hermitian,
nondiagonal coefficient matrices `witnessA` and `witnessB`, the owner proves
`[A²+B²,[A,B]] ≠ 0` and consequently proves that `matrixDirac A B ^ 2` commutes
with neither the Laplacian summand nor the curvature summand in the full
`4 × 4` operator algebra. The canonical replacement is the general identity
`matrixLaplacian_curvature_lie`, which expresses `[Δ,F]` as the lifted nested
coefficient commutator; commutation holds only when that nested commutator
vanishes. This is a concrete operator counterexample, not a general
noncommutativity claim. Source-reviewed; no fresh build in this pass.

## Exported G₂ point-permutation incidence failures (2026-10-30)

`Algebra.Zorn.G2ExportedIncidenceGenerator` proves two concrete failures of
incidence preservation for the finite exported point permutations:
`casPointPerm_zero_not_preserves_incidence` and
`correctedTPointPerm_not_preserves_incidence`. Their witnesses compare the
exported line images `1 ↦ 3` and `1 ↦ 7` against the respective point images
`0 ↦ 0` and `0 ↦ 28`. Thus bijectivity and point-action intertwining alone do
not certify preservation of the separately exported parabolic incidence data.

The constructive replacement has a different, native carrier:
`Algebra.Zorn.G2NativeIncidenceTransportCapstone` proves preservation of
`nativeLines` by each `pcGenerator`, the identity, products, and the generated
`pcWord` subgroup. This does not repair the failed CAS point permutations or
identify the exported and native incidence structures. Keep the failure and
the native positive theorem as separate carrier-specific results; do not infer
native flag preservation from the exported permutation tables. These owner
files passed a focused locked build together (8,974 jobs, exit 0); the build
reported pre-existing linter and deprecation warnings in imported G₂ owners.

## Window-6 rectangular-band equation countermodels (2026-10-30)

`Omega.GU.Window6FirstLastClassifier.paper_window6_first_last_classifier`
proves the general evaluation law on `Fin 3 × Fin 7`: every binary term takes
its first coordinate from its leftmost variable and its second coordinate
from its rightmost variable. The owner now also contains concrete assignment
witnesses `window6_rectangular_band_not_commutative` and
`window6_rectangular_band_not_unrestricted_product_equality`; these establish
that the rectangular-band operation does not satisfy the universal equations
`x ⋄ y = y ⋄ x` and `x ⋄ y = z ⋄ w`. These are actual model counterexamples,
with the finite coordinate assignments represented in the theorem statements.

The separate `Omega.EA.Window6CountermodelCertificate` checks five selected
equation indices through a `Nat × Nat` modular classifier. Its aggregate
`paper_window6_equational_spectrum` proves arithmetic identities for declared
count constants and zero lookup lists; it does not, by itself, enumerate or
verify all 4,694 equations. The two classifier owners use different carriers,
and this audit did not find a proved carrier isomorphism between them. Keep the
universal first/last theorem and the concrete countermodels as the canonical
scope until an explicit finite enumeration and carrier bridge are established.
The new concrete witness lemmas are staged; the shared Lake build lock is
currently held by the `decl-graph-refresh` owner, so no fresh kernel build is
claimed.

## Split-Clifford projectors versus the CAR null-mode pair (2026-10-30)

`InfoGeometry.Algebra.SplitCliffordOperatorModes.positive_projector_not_square_zero`
refutes treating the positive spectral idempotent `Pplus` as a nilpotent
creation/annihilation operator. The companion
`complementary_projectors_not_CAR` distinguishes the orthogonal idempotent pair
from a CAR pair. The exact corrected relation is exposed as
`complementary_projectors_mixed_anticommutator_zero`: the mixed
anticommutator of `Pplus` and `Pminus` is zero, while the separate null-mode
pair satisfies `null_pair_anticommutator : NPlus * NMinus + NMinus * NPlus = 1`.
The carrier distinction agrees with the existing constructive doubled-space
CAR package in `Canonical.SuperSouriauFermionGasBridge`; it does not identify
the projector pair with that CAR pair. This is one source-reviewed family,
not a completeness claim for the broader lexical inventory. The owner change
has not yet passed a new build in this audit turn.

## Prime-refutation names that only state conditional arithmetic (2026-10-30)

`Omega.Zeta.XiFinitePrimeRefutationAudit.paper_xi_finite_prime_refutation_audit`
is a conditional residual lemma: if every integer matrix entry is divisible
by the displayed finite product and twice its absolute value is smaller than
that product, then every entry is zero. The proof uses divisibility and the
bound; primality of the factors is not needed. I removed the unused primality
hypothesis so the Lean interface now matches the exact argument. This owner
does not supply a particular residual matrix, divisibility witness, or bound,
so it is not by itself a concrete refutation of a named Xi claim.

`Omega.GU.HeckeE4ThreePrimeRefutation.paper_hecke_e4_three_prime_refutation`
only evaluates the assumed coefficient formula
`a p = 240 * (1 + p^3)` at `p = 2, 3, 5`. It proves those three arithmetic
values, but contains no competing coefficient data and therefore establishes
no contradiction on its own. These two names are lexical refutation
false-positives; the conditional Xi lemma was strengthened, not promoted to
an instantiated mathematical counterexample. The modified Xi owner still
requires a locked Lean build.

## Witness-named conformal obstruction entries are positive conditionals (2026-10-30)

The lexical obstruction slice includes
`ConformalAnomalySource.projectorObstruction_eq_zero_of_kahlerLogDet_unitRelativeVolumeWitness`.
Despite its `Witness` suffix, this is not a counterexample: its hypothesis
`KahlerLogDetUnitRelativeVolumeWitness CI n M` is exactly the conjunction of
`CI.chiralScale = kahlerPotentialRN n M` and
`relativeVolumeChangeRN n M = 1`. The owner proves this forces
`CI.projectorObstruction = 0`, by first deriving the Kähler/log-det scalar
vanishing and then using the obstruction-norm identity. This statement is
conditional on those two equations; it does not assert that such a witness
exists or follows from arbitrary KKT data. The owner module passed its focused
locked build (3,832 jobs, exit 0), with pre-existing warnings in dependencies.
This is a semantic false positive in the name-based obstruction inventory, not
a new counterexample family.

The G₂ obstruction slice also contains
`G2GAPFlagWitnessAssembly.quotientRepresentative_injective_of_gap_witness_rows`.
This is a conditional injectivity assembly, not a counterexample and not an
unconditional global injectivity result: it requires pairwise disjointness of
the concrete Bruhat cells, quotient-equality alignment of residual words
within each cell, and injectivity of those residual words within each cell.
The row certificates prove factorization and cell membership; they do not
discharge these three premises. The owner also isolates the stronger
quotient-orbit separation input and the exact pair-coordinate alignment for
cell two. The assembly owner passed its focused locked build (9,013 jobs,
exit 0), with existing linter and deprecation warnings in imported G₂ owners.

## Current tracked-source candidate refresh (2026-10-30)

The latest `counterexample_inventory.py --tracked --json` run scanned 28,422
Lean files, reported zero read errors and seven skipped paths, and emitted
13,126 lexical candidates: 31 countermodels, 6 refutation-named rows, 368
obstruction rows, 111 identifiability rows, and 12,610 negative-boundary rows.
Exact-name reconciliation against this ledger covers all 31 repo-owned
countermodel rows and all 6 repo-owned refutation rows. This is only lexical
coverage: it neither semantically audits all 368 obstruction rows nor certifies
completeness of counterexample discovery. The larger obstruction,
identifiability, and negative-boundary slices remain under owner-by-owner
review. The JSON snapshot from this refresh is `/tmp/counterexample_inventory_current.json`
and is ephemeral.

## Aggregate replay of the repo-owned countermodel owners (2026-10-30)

The current lexical `countermodel` slice contains 31 declarations across 18
repo-owned owner files. A single sequential locked Lake invocation built all
18 module targets successfully (9,364 jobs, exit 0): `Analysis.BipolarCircleEnclosurePeriods`,
`Analysis.SimplePoleReflection`, `Arithmetic.SarnakLocalCertification`,
`Canonical.ConformalProjectorAgreement`, `Canonical.GramianInverseContracts`,
`Canonical.PeirceWeylExamples`, `Convex.BinaryBarrierCoordinateHessian`,
`Core.IdempotentGraphReflectionOrder`, `EmergentGeometry.HarmonicRectangle`,
`Exceptional.FreudenthalSymplecticMixedTripleCounterexample`,
`Geometry.QuadraticArnoldNumerator`, `HodgeCohomology.KreinHodgeDiracTests`,
`HodgeCohomology.KreinHodgeObstruction`, `Lie.SplitOctonionNonmultiplicativity`,
`Modular.KreinPotentialTrace`, `Physics.SpinAffineCasimirRigidity`,
`Probability.GromovPermutationNormalization`, and `Routing.AttentionInteriorFiber`
(each under `InfoGeometry`). The replay validates those current owner files at
their Lean statements. It does not independently re-evaluate every prose
interpretation, prove each countermodel has an adequate canonical replacement,
or certify the 13,126-row lexical inventory as exhaustive.

## Fixed versus growing period in the local-density obstruction (2026-10-30)

`Omega.Zeta.OperatorFixedKernelLocalDensityObstruction` proves positivity of
`Δ / B` for a fixed positive period `B`. Its conclusion does not provide a
uniform lower bound when the period varies with the stage. I added
`growing_period_mean_gap_tendsto_zero`, proving in Lean that for every real
`Δ`, the sequence `Δ / (n + 1)` tends to zero. This is the exact varying-period
boundary and does not contradict the fixed-`B` theorem. The focused locked build
of `Omega.Zeta.OperatorFixedKernelLocalDensityObstruction` passed (3,093 jobs,
exit 0); one existing `unnecessarySimpa` linter warning remains in the owner.

## Two-coordinate cosymplectic obstruction is a conditional rigidity theorem (2026-10-30)

The lexical obstruction declarations
`Canonical.BipolarVariableConnectionPoissonCosymplecticClosure.pristine_two_coordinate_obstruction_core`
and
`Canonical.BipolarVariableConnectionPoissonPristineChain.pristine_dimension_obstruction_core`
are wrappers around the same existing theorem
`bipolar_two_dimensional_obstruction_packet`. Their hypotheses are a skew
cotangent map and `L etaCovector2 = 0`; the proved conclusion is
`etaCovector2 ≠ 0`, `L thetaCovector2 = 0`, and `L = 0`. Thus the exact
corrected statement is a conditional two-dimensional rigidity result. The
three-coordinate GENERIC packet is a separate construction and supplies the
nonzero lanes after adjoining the auxiliary coordinate; it does not negate or
weaken the two-dimensional theorem. These two capstones are duplicate
packaging, not independent counterexamples. No new theorem was needed in this
pass. A fresh locked build of the core obstruction and both capstones passed
(8,965 jobs, exit 0); pre-existing linter warnings remain in imported bipolar
owners. A new axiom audit of these declarations was not run in this pass.

## Winding quantization is separate from the finite-dimensional CCR obstruction (2026-10-30)

`Canonical.ApolloniusWindingFluxBridge.winding_quantization_with_finite_ccr_obstruction`
is a conjunction of two already-proved results, not a counterexample to winding
quantization. The first component is the residue/winding identity
`quantizedWindingFlux = logarithmicPhase`; the second is the finite-dimensional
trace obstruction in `Canonical.ApolloniusScalarOperatorSurprisalNoGo`, which
rules out `[A,B] = c I` for nonzero real `c` on the eight-dimensional native
Zorn endomorphism carrier. The canonical corrected conclusion is coexistence:
integer winding has its `2π i n` period while finite exact scalar CCR is
impossible on that carrier. Neither statement derives the other, and the
bridge does not identify winding with a Riemann-zero ordinate. This source
review found no missing theorem to add; the focused owner build was not run in
this pass.

## Vandermonde identifiability entries are finite exact criteria (2026-10-30)

The lexical identifiability candidates
`PrimonCrystallizationFactIndex.finite_vandermonde_nonzero_iff_injective` and
`QuasicrystalRHExplicitFormula.finite_vandermonde_nonzero_iff_injective` are
re-exports of the same Mathlib-backed finite theorem in
`Canonical.VandermondeExclusionBridge`. There, the determinant product formula
gives `det(V(W)) ≠ 0 ↔ Function.Injective W`, while the zero criterion is
equivalent to an explicit pairwise collision, under `[CommRing R] [IsDomain R]`.
These statements concern `Fin n` and do not assert an infinite spectral or
quasicrystal limit. Both candidate names are therefore duplicated positive
criteria, not separate counterexamples; no additional proof was needed. The
three owners were not rebuilt in this pass.

## De Rham obstruction names restate the cochain-complex predicates (2026-10-30)

The lexical obstruction candidate
`Canonical.DeRhamSymplecticKKQuantizationLimit.TwoStepDeRhamComplex.obstruction_closed`
is simply the first projection of `IsObstruction α := IsClosed α ∧ ¬ IsExact α`.
The owner separately proves the substantive implication
`exact_is_closed` from `d_comp : d₁.comp d₀ = 0`, and `exact_not_obstruction`
from the same definitions. Hence this name is a definition-level wrapper, not
a counterexample or an unexpected closed-but-nonexact witness. The canonical
alternative is the existing complex axiom plus the exactness/closedness
implications; a particular nontrivial cohomology class would require an
additional construction. No source edit or fresh build was needed for this
classification.

## Projector mismatch is controlled by its commutator, not its size (2026-10-30)

The lexical obstruction wrapper
`Canonical.DilatedGapEquivariance.chiralAnomaly_eq_zero_of_projectorObstruction_eq_zero`
uses only the sufficient premise that the Drazin/Moore--Penrose projector
mismatch is zero. The owner identity
`chiralAnomaly_eq_mismatch_commutator_metric` shows that the anomaly is the
commutator of that mismatch with the metric projector. I added the exact
general-ring theorem
`chiralAnomaly_eq_zero_iff_projectorMismatch_commutes_metric` to
`Canonical.MoorePenrose`; it makes clear that the one-way wrapper is not the
full vanishing criterion. The new declaration uses no commutativity hypothesis
on the ambient ring. Its focused locked build passed (3,179 jobs, exit 0); the
build reports existing deprecation/style warnings in the imported
`Singular.MoorePenrose` owner. This is a corrected criterion, not a concrete
counterexample asserting nonzero mismatch with zero anomaly.

The related lexical obstruction
`Canonical.OperatorProjectorMismatch.ProjectorCommutatorObstruction.implies_mismatch`
has a genuine one-way boundary. The owner already proves that a nonzero
projector commutator forces a nonzero projector mismatch. I added the converse
refutation `commuting_projectors_can_have_nonzero_mismatch`: two explicit
non-diagonal complementary idempotents in `Matrix (Fin 2) (Fin 2) ℤ` have zero
commutator and nonzero difference. Thus mismatch detects both noncommuting
splits and distinct commuting projectors; it is not equivalent to
noncommutativity. The focused locked build of
`InfoGeometry.Canonical.OperatorProjectorMismatch` passed (3,095 jobs, exit
0). The witness stays inside the full noncommutative matrix algebra and is not
a diagonal scalar model.

## Fresh tracked lexical inventory (2026-10-30)

After the latest staged edits, `tools/quality/counterexample_inventory.py
--tracked --json` scanned 28,422 Lean files and emitted 13,120 lexical rows:
31 countermodel names, 6 refutation names, 368 obstruction names, 111
identifiability names, and 12,604 negative-boundary names. The `lean/` subtree
accounts for 11,520 rows (31, 6, 359, 101, and 11,023 respectively). The scan
reported zero read errors and seven skipped paths. All 37 countermodel and
refutation names were present somewhere in the current audit ledger; 398
obstruction/identifiability candidate names were not directly named there.

These are lexical navigation counts, not a semantic proof-status audit. In
particular, a name absent from the ledger is only a candidate for source review,
and a name present in it is not thereby kernel-certified. The machine-readable
snapshot used for this pass was temporary (`/tmp/counterexample_inventory_resume.json`).

## Conformal projector-obstruction family source audit (2026-10-30)

I traced the `ConformalAnomalyDegenerate` readout wrappers into
`ConformalAnomalySource` and its projector/anomaly owners. The source defines
the operator obstruction as the commutator of the spectral and metric
projectors, and already proves the exact equivalence
`projectorObstruction_eq_zero_iff_commute`. It also proves
`chiralScale_eq_zero_iff_projectorObstruction_eq_zero`. The degenerate package
from a unit-relative-volume witness additionally requires an explicit
Kähler/log-det readout equality; that premise is used to derive projector
commutation before constructing the package.

Thus the one-way `normalPhaseDegeneratePackage_of_unitRelativeVolumeBit` is a
conditional construction, not a claim that the volume bit alone determines
the operator state. The precise algebraic alternatives already exist in the
owners, so this review found no missing theorem to add. This source inspection
was not a fresh build or kernel check of those files.

## De Rham lexical obstruction is not an existence witness (2026-10-30)

The inventory candidate
`Canonical.DeRhamSymplecticKKQuantizationLimit.TwoStepDeRhamComplex.obstruction_not_exact`
is only the second projection of the predicate `IsObstruction := IsClosed ∧
¬ IsExact`. The owner separately proves `exact_is_closed` from `d₁ ∘ d₀ = 0`
and `exact_not_obstruction`. It constructs no closed non-exact current. The
module explicitly leaves construction of global de Rham cohomology and its
comparison map in `FullGlobalDeRhamObstructionDebt`; its finite matrix
certificates do not discharge that debt. Thus the canonical theorem-honest
result is exact-implies-closed in the two-step complex, while existence of a
nontrivial cohomology class remains unproved here. This was a source review;
no new theorem was added and no build was run for this owner.

## Einstein–Kähler isotropic source is an exact scalar criterion (2026-10-30)

The 46 lexical obstruction/readout candidates in
`Canonical.ConformalAnomalySource` include a routed theorem that closes an
Einstein equation after assuming `Ric = c g` and selecting scalar curvature
`2(c + Λ - κA)` for the isotropic source `T = A g`. I traced this to
`ChiralEinsteinBridge.einsteinEquation_of_anomaly_source`: its proof reduces
the equation componentwise to a ring identity. I added
`einsteinEquation_iff_anomaly_scalar_relation`, which proves the converse when
the metric has at least one nonzero component. This identifies the exact
scalar constraint and prevents the forward implication from being read as an
existence theorem for a metric or a field solution. The new Lean theorem is
staged and its focused locked build passed (`InfoGeometry.Canonical.ChiralEinsteinBridge`,
3,777 jobs, exit 0). The build replayed its dependency closure and reported
existing imported-owner linter warnings; the new owner compiled successfully.

## Weyl phase-space obstruction wrappers admit an exact zero criterion (2026-10-30)

The tracked lexical scan flagged 22 declarations in
`Canonical/PhaseSpaceWeylCausalBridge.lean` because their names include
`projectorObstruction`. Source inspection shows these are conditional bridge
packages and KKT/leaf/trunk projections, not counterexamples: the endpoint is
carried by `FlatCurvatureValueBridge.zeroCurvatureIntegral_to_target`, and the
flatness premise is used to reach its zero-curvature-integral premise. The
underlying operator is exactly the spectral/metric projector commutator in
`ConformalAnomalySource`, where
`projectorObstruction_eq_zero_iff_commute` already proves the exact vanishing
criterion.

I added `WeylTransportBridge.holonomy_eq_zero_iff_projectors_commute` to
`Canonical/WeylTransportChiralBridge.lean`. Given the explicit
`FlatCurvatureProjectorObstructionBridge` and flatness of the input gauge
field, zero holonomy is equivalent to commutation of the two projectors. The
forward and reverse directions respectively use the bridge endpoint, the
NNNorm zero criterion, and the exact projector-obstruction iff. This does not
derive a bridge from flatness alone and makes no unconditional holonomy claim.
The locked build of `InfoGeometry.Canonical.WeylTransportChiralBridge` passed
(4,099 jobs, exit 0); imported deprecation and linter warnings were present.
The refreshed scan is lexical navigation, not a completeness certificate.

## Weyl/KKT source identity has a projector-commutation zero criterion (2026-10-30)

Eight lexical obstruction candidates in
`Canonical/WeylKKTAnomalyIdentity.lean` reduce to readout identities and
conditional source implications. In particular,
`nonzeroProjectorObstruction_sources_transportedEinsteinResidual` assumes the
source equation equating the residual with `chiralScale`; it is not an
existence theorem for a sourced geometric solution. The operator source is
owned by `ConformalAnomalySource`, where the chiral scale is the nonnegative
norm of the projector obstruction and the obstruction vanishes exactly when
the spectral and metric projectors commute.

I added
`WeylKKTAnomalyIdentity.transportedEinsteinResidual_eq_zero_iff_projectors_commute`.
Under the same explicit source equation, it identifies zero residual exactly
with projector commutation, strengthening the existing one-way nonzero
implication without removing its source premise. The locked joint build of
`InfoGeometry.Canonical.WeylTransportChiralBridge` and
`InfoGeometry.Canonical.WeylKKTAnomalyIdentity` passed (4,185 jobs, exit 0);
existing imported warnings remain.

## Native Zorn Cartan weight-separation hits are positive criteria (2026-10-30)

The tracked scan marks weight nonvanishing, weight separation, joint-eigenspace
support, and zero-coordinate declarations in
`Lie/CanonicalZornCartanAdjointRootDecomposition.lean` as negative-boundary or
identifiability candidates. Reading the definitions and consumers shows these
are positive finite-spectrum results: the owner proves that exactly indices 6
and 13 have zero weight, separates every other coordinate weight, identifies
each nonzero joint eigenspace with the span of its basis derivation, and
identifies the zero joint eigenspace with the two-dimensional Cartan span.
Downstream root-bracket and Mathlib-bridge modules consume these exact
statements. The owner deliberately does not identify the named short/long
weight sets with an abstract root system; that requires the separately stated
Cartan-metric interpretation.

No counterexample replacement was missing in this family. The locked build of
`InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition` and
`InfoGeometry.Lie.CanonicalZornCartanAdjointRootBrackets` passed (8,992 jobs,
exit 0). An initial attempted target used a nonexistent shortened module name;
that invocation failed with “no such file or directory” and was superseded by
the successful build using the actual module names. Existing linter warnings
remain.

## Modular cycle obstruction is an exact potential criterion (2026-10-30)

The `GmCycleGcdModObstruction` owner is a genuine constructive alternative,
not merely a nonvanishing witness. For weights on the complete directed graph
with values in `ZMod q`, the exact theorem
`paper_gm_cycle_gcd_mod_obstruction` proves that a potential exists iff every
directed triangle sum vanishes, assuming skew-symmetry
`w a b + w b a = 0`. The reverse construction is explicit:
`φ v = w base v`, and the triangle based at `base` gives
`φ b = φ a + w a b`. These assumptions matter; the theorem does not claim a
criterion for an arbitrary sparse graph or nonskew edge data. The locked build
of `Omega.SyncKernelWeighted.GmCycleGcdModObstruction` and its consumer
`Omega.SyncKernelWeighted.GMAffineImprovementDichotomy` passed (3,096 jobs,
exit 0). Existing unused-section-variable and deprecated-import warnings
remain.

## Signed-correlation identifiability has an exact orthogonality boundary (2026-10-30)

The tracked inventory marks `Physics/ParticleGammaCorrelation` as an
identifiability candidate. Its source contains both the exact criterion
`correlation_separates_iff` and the concrete witness
`nonzero_vectors_need_not_separate`: two nonzero coordinate vectors on
different axes give equal correlations for signs `+1` and `-1`. The canonical
statement is therefore conditional separation: for this signed dot-product
readout, the two signs are distinguished exactly when the dot product is
nonzero. Nonzero inputs alone do not suffice. This is a finite real-vector
readout result; it does not establish separation for arbitrary operator
correlators or a noncommutative carrier. The existing Lean owner already proves
both the criterion and witness, so no duplicate declaration was added. Source
and proof-body review only; no fresh locked build was run in this pass.

## Finite-rank obstruction is the canonical replacement for the center claim (2026-10-30)

The tracked scan also finds
`Omega.GroupUnification.FoldbinCenter2TorsionDimensionObstructionM2`.
Its generic theorem `no_injective_linearMap_fin_fun_of_finrank_lt` is the
canonical statement: an injective linear map from `Fin n → K` into a
finite-dimensional space `V` forces `n ≤ finrank K V`. The paper-facing
specialization therefore correctly rules out an injective copy of
`(Z/2)^3` when the `F₂`-dimension of the center's 2-torsion is at most one.
This is a rank obstruction under the stated dimension hypothesis; it does not
prove that a particular center has that dimension. The source contains full
proofs and no `sorry`, `admit`, or custom `axiom`; the current build lock
prevents a fresh kernel replay, so this entry records source review only.

The lexical candidate
`Omega.EA.StableAuditSmallOrderObstruction` is a naming false positive rather
than a mathematical obstruction: its declarations count all binary-operation
tables on `Fin n` (`n^(n*n)`, hence 16 tables for `n=2` and 19,683 for `n=3`).
No associativity or other law is imposed, and no counterexample claim follows
from those counts. This source was reviewed only; it was not rebuilt here.

## Odd-cardinality root-closure obstruction is only a parity criterion (2026-10-30)

`Omega.Zeta.XiTimePart9zpWindow6OddResidualRootClosureObstruction` proves the
canonical replacement `root_card_even`: a finite carrier equipped with an
involutive, fixed-point-free negation has even cardinality. Its paper-facing
corollary excludes a root-system shadow of cardinality 21, including the
arithmetic count `18 + 3`. The owner does not encode an embedding of the
18-element cyclic set into the completed set, nor prove that an arbitrary
three-element extension preserves the existing root structure. Thus the
proved result is a cardinal-parity obstruction to a 21-element finite root
system, not a full root-closure or extension-classification theorem. A
repository-wide search found no consumer beyond the owning import surface.
The owner has complete source proofs and no visible `sorry`, `admit`, or
custom `axiom`; a fresh locked build remains unavailable because the shared
Lake lock is held by the external `decl-graph-refresh` process recorded in the
lock metadata.

## Mod-3 edge-flux obstruction constructs a left-annihilator invariant (2026-10-30)

`Omega.GroupUnification.EdgeFluxMod3Obstruction` turns the determinant
condition `3 ∣ det E` into a concrete algebraic alternative: after reducing
the integer matrix modulo 3, the owner constructs a nonzero linear functional
`χ` annihilating every reduced image vector. Its translation theorem then
proves `χ(b + E v) = χ(b)` whenever the same annihilation premise holds. The
`n = 1` specialization identifies `χ` with coordinate projection. These are
fully quantified Lean statements with proof terms in the owner; they do not
depend on an asserted “flux” interpretation. The source does not supply a
specific window-6 matrix `E`, so no concrete instance of `3 ∣ det E` is
certified here. A fresh owner build could not run because the shared Lake lock
continues to reject this session's build request; this is source review, not a
new kernel-verification claim.

## Odd nonzero modes do not obstruct ordinary linear recurrence (2026-10-30)

The Xi owner
`XiTimePart60abGaugeConstantNonCfiniteOgfObstruction` defines its local
`IsCFinite` surrogate to mean eventual vanishing of every odd-indexed
coefficient. Given a structure whose field already assumes that all odd modes
are nonzero, the named non-C-finiteness theorem is then an immediate
contradiction at index `2*N+1`; this does not prove non-C-finiteness in the
standard linear-recurrence sense. I added
`XiTimePart60abOddModesRecurrenceCounterexample`, which uses Mathlib's
`LinearRecurrence`: the constant-one sequence solves the order-one recurrence
`a(n+1)=a(n)`, has every odd-indexed term nonzero, and fails the local
odd-vanishing predicate. This is a formal counterexample to treating that
predicate as a general recurrence characterization. It does not assert or
prove a separate ordinary-generating-function identity. The new owner and its
`Omega.Zeta` import are staged, and its focused locked build passed after the
constant-one sum was proved explicitly over `Fin 1` (3,094 jobs, exit 0).
The static semantic-vacuity scanner emitted one `constant_function` warning on
the recurrence coefficients; this is intentional in this witness, whose point
is precisely that a constant sequence satisfies a nontrivial fixed linear
recurrence while never having an odd zero mode.

## Finite value range is not the C-finite condition (2026-10-30)

`Omega.Folding.FoldBinGaugeConstantNotCFinite` defines its `isCFinite`
surrogate as containment of the values of `2^n` in a finite set, then proves
that this value set is infinite. This does not obstruct a linear recurrence:
the same sequence satisfies the order-one Mathlib recurrence
`a(n+1) = 2*a(n)`. I added
`Omega.Folding.FoldBinGaugeConstantRecurrenceCounterexample` to prove that
recurrence and combine it with the existing infinite-range theorem. The exact
correction is that “finite range” and “satisfies a fixed linear recurrence”
are different properties. No ordinary-generating-function identity is newly
claimed here. The companion owner is staged and imported by `Omega.Folding`,
and its focused locked build passed after replacing the fragile simplifier
step with the explicit `Fin.sum_univ_one` recurrence calculation (8,925 jobs,
exit 0).

## Null-as-local-section labels are conditional set-theoretic criteria (2026-10-30)

`RecursiveAddressing.NullAsLocalSectionObstruction` proves two precise
statements: non-`NULL` readout is equivalent to an admitted nonempty prefix
fiber, and an existing section with an injective tuple-of-restrictions map is
the unique section realizing those restrictions. Its H²-named theorem is a
conditional contrapositive: if every global certificate forces an arbitrary
predicate `ObstructionVanishes r`, and that predicate is false, then the
certificate fiber is empty and the supplied readout criterion returns
`NULL`. The carrier `Cech2`, transition map, and predicate are unconstrained;
the owner defines no cochain complex, cocycle, coboundary, or cohomology group.
Thus the canonical Lean result is the stated set/readout implication, not a
proved Čech-H² theorem.

`PhysicalSpacetimeSkeleton.InstantiationCriterion.AcceptableInstantiation`
stores the obstruction witness, null-readout implication, positive kernelized
readout data, and continuum proposition as fields. Its criterion theorem and
the `ProceduralGrandChain` / `AdmissibleEinsteinClosureMain` wrappers project
those fields; they do not construct an instantiation. A repository-wide search
of `lean/` found only the structure declaration and universal quantifiers over
it, with no concrete inhabitant. This is an existence/instantiation boundary,
not a counterexample to the conditional theorems.

## Fold-π residual decoding: finite-cardinality theorem and model boundary (2026-10-30)

`Omega.Conclusion.FoldgaugePiSufficientStatisticFiberObstruction` proves a
valid finite-set statement: on a fiber of cardinality `F`, pairing a constant
`Fin 1` label with a residual in `Fin (d + 1)` cannot be injective when
`d + 1 < F`; for any deterministic decoder, at most `d + 1` microstates are
decoded correctly. In the single-path instance defined by this owner, the
success-probability upper bound tends to zero using the Fibonacci lower bound.
These are canonical alternatives to any claim that a low-cardinality residual
can recover every state of the modeled fiber.

The source does not construct an underlying path/sample space `Γₓ`, a fold map
whose actual fiber has that cardinality, or a statistic map derived from such
a fold. The name `fiber_card` is itself defined to be the product of shifted
Fibonacci numbers, and the displayed closed-form conjunct is therefore `rfl`.
Likewise, the residual is an arbitrary function to a finite type. The results
are kernel-level theorems about this explicitly parameterized finite model;
they do not establish a sufficient-statistic theorem for an independently
constructed folding process. The generic pigeonhole alternative is already
owned by `Omega.POM.SufficientStatisticResidualNoninvertibility`; no duplicate
Lean API is warranted. Source audit only in this pass; no new build was run.

## Current tracked-source inventory refresh (2026-10-30)

Re-running `tools/quality/counterexample_inventory.py --tracked --json` against
the present index/worktree scanned 28,425 Lean files, with zero read errors and
seven skipped paths. Its lexical categories are 12,613 negative-boundary,
368 obstruction, 111 identifiability, 31 countermodel, and 7 refutation
declarations. This is a name-pattern inventory, not a semantic count of
counterexamples. The additional refutation relative to the earlier six-row
snapshot is the staged
`FoldBinGaugeConstantRecurrenceCounterexample.exponentialScale_recurrence_refutes_finiteRange_surrogate`;
its theorem refutes the finite-range surrogate for C-finiteness while proving
the exponential sequence satisfies a first-order recurrence. The scan JSON is
ephemeral at `/tmp/counterexample_inventory_current.json`. The 368 obstruction
and 111 identifiability hits remain the main untriaged semantic backlog; their
lexical names alone do not establish counterexamples.

## Zorn upper-sector associator has a two-versus-three generator boundary (2026-10-30)

`Canonical.ZornAssociatorKreinBridge.associator_upper_eq_neg_tripleDet_smul_kreinJ`
proves the exact formula
`[U(u), U(v), U(w)] = -tripleDet(u,v,w) • kreinJ` on the repository's split-
octonion Zorn carrier. The owner
`Canonical.ZornThreeGeneratorObstruction` derives that every triple selected
from two fixed upper vectors has zero associator, while the canonical three
basis directions have determinant one and nonzero associator. This is a
source-grounded minimal-arity witness and exact replacement for any assertion
that two chosen upper directions can generate this scalar-triple-product
obstruction. It is deliberately only a Bool-indexed selection of two fixed
vectors; it is not a proof of Artin's general theorem about all subalgebras
generated by two elements.

The owner target `InfoGeometry.Canonical.ZornThreeGeneratorObstruction`
passed a locked build (3,095 jobs, exit 0). It emitted one pre-existing
deprecation warning in imported `SplitOctonionZornAlgebra.lean`; the owner
itself built. The theorem is an algebraic source result and does not establish
the physical identifications explicitly excluded by the module contract.

## Window-6 fold does not preserve the stated one-step fiber counts (2026-10-30)

`Omega.GU.paper_terminal_foldbin6_strong_lumpability_fails` gives an explicit
finite witness: `cBinFold 6 0 = cBinFold 6 21`, but the six bit-flip neighbors
of these representatives have different counts for at least one folded
output. The auxiliary `terminalFoldbin6BinaryWitness` records the discarded
Zeckendorf `F₈` bit, with values 0 and 1 on those two representatives.
This refutes strong lumpability for the exact six-coordinate transition-count
definition used in that theorem; it does not refute every possible quotient
or transition relation on the folded carrier.

The canonical finite-resolution alternative is the exact enumeration in
`Omega.GU.paper_terminal_foldbin6_two_point_fiber_direction_spectrum`: among
the size-two fibers enumerated from the 64 six-bit inputs, the XOR direction
spectrum is `{34, 38, 62}`, and the stated geometric involution swaps endpoints
only in direction 34. The F₈ witness is outside this enumerated size-two
fiber spectrum, so these are complementary finite results rather than a
classification of every fiber in `Nat`. The paper-facing combination
`Omega.GU.paper_window6_minimal_markov_obstruction_pure_f8_tail` proves the
displayed equal-fold, Fibonacci value, and off-spectrum statements.

The focused locked build of
`Omega.GU.Window6MinimalMarkovObstructionPureF8Tail` passed (3,132 jobs, exit
0). It replayed the finite owner dependency closure; existing deprecation
warnings were emitted by Zeckendorf and Hamming-distance dependencies. The
scope remains finite and computationally enumerated by `native_decide` for the
explicit 64-state fiber table.

## Idempotent-chart reflection order has a sign-sensitive counterexample (2026-10-30)

The incoming Grassmannian draft reuses the Peirce chart points
`P₊ = P - N₊` and `P₋ = P + N₋`, where `N₊ = P A (1-P)` and
`N₋ = (1-P) C P`. For the reflection convention `S_Q = Q - (1-Q)`, the
correct ordered products in the existing
`InfoGeometry.Core.IdempotentGraphReflectionOrder` owner are
`S_{P₊} S_{P₋} = 1 + 2J - 2Σ - 2V` and
`S_{P₋} S_{P₊} = 1 - 2J + 2Σ - 2V`. Consequently their anticommutator is
`2(1 - 2V)`, while their commutator in the first order is `4(J - Σ)`.
The draft assigned the reverse-order expression to the forward product and
gave the opposite commutator sign. Both errors have kernel-checked witnesses
in `Matrix (Fin 2) (Fin 2) ℤ`, with a noncentral idempotent and noncommuting
off-diagonal directions.

This is a correction to algebraic product identities, not a construction of a
Riemannian/Kähler metric, a geodesic, or principal angles. I initially created
a separate audit module, then removed it after a full source search found the
existing owner and consolidated the useful compact commutator formula and
opposite-sign witness there. The focused locked builds of
`InfoGeometry.Core.IdempotentGraphReflectionOrder` (1,222 jobs) and its consumer
`InfoGeometry.Core.IdempotentGraphGrassmannian` (3,097 jobs) passed. No duplicate
Grassmannian owner remains.

The broader staged source `InfoGeometry.PureNonCommutativeOperatorSpine` was
also checked because the incoming text described it as a complete proof spine.
Its locked build fails. The failure is not confined to the final super-derivation
proof: Lean reports heartbeat timeouts in earlier declarations (including
source lines 270, 289, 361, 387, and 430), unresolved goals in the long Hua
calculation, and an unresolved mixed super-derivation identity in A28. The
parity-conjugation subproof for the final A28 identity was simplified to use
the defining Peirce relations, but the enclosing module remains unverified and
must not be cited as a compiled 24-stage synthesis. Successful builds of the
focused Grassmannian owners do not imply that this separate spine compiles.

The opposite-sign witness is named
`InfoGeometry.Core.IdempotentGraphReflectionOrder.matrix_counterexample_reversed_reflection_commutator_sign`.

## Lexical inventory refresh after Grassmannian consolidation (2026-10-30)

The tracked-source scanner now sees 28,434 Lean files, zero read errors, and
seven skipped paths. Its lexical candidate counts are 12,615 negative-boundary,
368 obstruction, 111 identifiability, 32 countermodel, and 7 refutation rows.
These are candidate declarations, not semantic counts; broad negative-boundary
and obstruction classes still require owner-level review. The Grassmannian
sign correction lives in the existing Core owner, with no duplicate module.
Five Lean owner files appeared since the preceding scan; none added a new
lexical counterexample candidate. The refreshed report is
`/tmp/counterexample_inventory_resumed.json` and is navigation-only evidence.

## Idempotency-defect recurrence correction (2026-10-30)

The proposed A₃₆ universal recurrence
`V^3 - V^2 - V = V * (V^2 - V)` is false in a general ring: the right side
expands to `V^3 - V^2`, leaving an unsupported extra `-V` on the left. The
correct identity is `V^3 - V^2 = V * δ(V)`. The conditional conclusion
`δ(V)=1 → V^3=2V+1` is valid and follows from `V^2=V+1`.
`Core.IdempotentGraphGrassmannian` now owns the generic defect definition,
complement identity `δ(1-X)=δ(X)`, naturality under ring homomorphisms, the
correct cubic recurrence, and its conditional level-set consequence. It also
proves the precise repair boundary: the draft's incorrect recurrence holds
exactly when `V=0`. The
focused locked build of `InfoGeometry.Core.IdempotentGraphGrassmannian` passed
(3,097 jobs, exit 0), and the staged diff passes `git diff --cached --check`.
The additional A₃₅ claims about centrality, Peirce-sheet splitting, and
invariance remain separate claims: this correction does not certify them or
the aggregate `PureNonCommutativeOperatorSpine`.
