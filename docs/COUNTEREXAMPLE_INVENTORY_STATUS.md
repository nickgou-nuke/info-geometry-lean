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

The bounded test surface is now source-reviewed as well: its `Plane` witness
confirms the negative norm of a null vector, and its axiom audit covers the
nondegenerate Krein pairing, self-adjoint null differential, exact complex,
and contraction. The exact general replacement is
`KreinHodgeKernelCriterion.hodge_kernel_eq_iff`: for square-zero `d`, the
Hodge-kernel equality holds iff the range of `d + kreinAdjoint d` is disjoint
from its kernel. The locked build of
`InfoGeometry.HodgeCohomology.KreinHodgeDiracBoundedTests` passed (3,292 jobs,
exit 0); printed declarations depend only on standard foundational axioms.

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
both entries. The owner was replayed in the sequential locked build recorded
below.

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

## `External/Auto/NonIsoConf3QuadricCompactification`: conditional disjunction only (2026-10-31)

`compactification_obstruction_synthesis` assumes `hA : singular quadricA` and
returns the disjunction whose first branch is exactly that assumption. The
proof is valid, but the file defines no projective carrier, quadratic
equations, singular-locus predicate, or singular point. The surrounding
statement that the projective closures are singular is therefore not proved
by this declaration. Repository search found no Lean consumer establishing
`hA` or supplying a concrete singularity witness. The canonical statement is
the existing conditional implication; a geometric singularity claim remains
unformalized until its carrier and witness are given.

## Entanglement pairing: deterministic partner model versus relation monogamy (2026-10-31)

`Geometry/EntanglementGeometry.AMPS_two_partner_obstruction` is valid because
`MonogamousPairing` stores a function `partner : Node → Option Node`; equality
of two `some` outputs gives partner uniqueness. This does not prove a quantum
monogamy inequality from a state or entanglement measure. Added
`symmetric_irreflexive_relation_need_not_be_monogamous`: on `Fin 3`, the
undirected star relation is symmetric and loop-free while node `0` has distinct
neighbors `1` and `2`. This is the canonical counterexample to deriving
monogamy from symmetry and irreflexivity alone. The new theorem's Lean check is
pending behind pre-existing live locked-build session 9439; no concurrent
build was started.

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

## Indefinite Krein-Hodge kernel counterexample (2026-10-31)

The standalone owner `HodgeCohomology.KreinHodgeDiracTests` also compiles as a
direct target (locked build: 1,693 jobs, exit 0). Its `nullOperator` is
self-adjoint for a symmetric nondegenerate indefinite pairing and has square
zero, while its square has full kernel and the operator itself does not. Thus
`ker(D²) = ker(D)` is false without additional hypotheses, even in the
square-zero case. Its `hodge_counterexample` additionally exhibits a nonzero
closed, coclosed vector for the resulting zero Hodge operator.

The canonical replacement is the general theorem
`KreinHodgeKernelCriterion.hodge_kernel_eq_iff`: for square-zero `d`, equality
of the Hodge-Laplacian kernel with `ker(d + kreinAdjoint d)` is equivalent to
disjointness of the range and kernel of `d + kreinAdjoint d`. A proved
sufficient condition is commutation of a square-zero Krein-self-adjoint
operator with the positive fundamental symmetry; under those hypotheses the
operator is zero. These statements retain the bounded operator/Krein-space
carriers and do not infer a general Hodge theorem from the finite witness.

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

## MDPAS quotient and signed-pullback inventory reconciliation (2026-10-31)

Two inventory labels were checked against their current owner sources. In
`Physics.MDPASJMSouriauDigest.FiniteMDPASJMDirectSystem`,
`DirectLimitCarrier` is a quotient type of stage-tagged values, with a
set-valued lift/universal property; it has no ring operations or algebraic
colimit structure in that owner. The digest now proves
`ofStage_eq_of_bond_eq` and
`ofStage_not_injective_of_bond_not_injective`: any collision under a bond
descends to the quotient and prevents the corresponding canonical stage map
from being injective. This is conditional and does not assert that a concrete
bond in the system is noninjective. The audit target
`InfoGeometry.Physics.MDPASJMSouriauGlobalObstructionAudit` passed its locked
build (9,186 jobs); the new declarations report only `[propext,
Classical.choice, Quot.sound]`.

The lexical inventory marks
`SuperGrassmannian.SignedPullbackMatrixBoundary` as requiring source audit,
but its owner and audit already contain the canonical correction. On the
triple of ring-valued functions, identity signed-pullback invariance is
equivalent to `∀ x, 2 * f.odd1 x = 0`; in characteristic two every triple is
invariant. The existing noncommuting `2 × 2` matrix witness over `ZMod 2`
retains a nonzero middle component and a nonzero commutator, so invariance
does not imply vanishing or commutativity. The locked build of
`InfoGeometry.SuperGrassmannian.SignedPullbackMatrixBoundaryAudit` and
`InfoGeometry.SuperGrassmannian.SuperSheafOddAnnihilationAudit` passed (3,198
jobs). This is an inventory-status correction, not a new replacement theorem.
The overall lexical inventory and independent semantic review remain open.

## Quadratic Arnold numerator source-audit reconciliation (2026-10-31)

The inventory marks `External.Auto.NonIsoConf3LogWedgeObstruction` as needing
source audit, but its canonical replacement is already present in
`Geometry.QuadraticArnoldNumerator` and `Geometry.QuadraticArnoldVanishing`.
The owner proves an explicit integer evaluation with common-denominator
numerator coefficient `52`, refuting the unrestricted literal polynomial
identity on that witness. More generally, under
`q4 (sub Y Z) ≠ 0`, the complete numerator vanishes in every coordinate pair
iff all displacement minors of `sub X Y` and `sub Y Z` vanish. Necessity uses
the `xx` coefficient formula and nonzero signature factors; sufficiency uses
the decomposed coordinate formulas and the exact `mixedCore_zero` identity.

Scope is important: the formal carrier is integer `Vec4` data and a polynomial
numerator. The module does not construct differential forms, a logarithmic
complex, or a cohomological quotient, so the counterexample is to the encoded
numerator identity and does not establish a de Rham cohomology result. The
locked build of `InfoGeometry.External.Auto.NonIsoConf3LogWedgeObstructionAudit`,
`InfoGeometry.Geometry.QuadraticArnoldNumeratorAudit`, and
`InfoGeometry.Geometry.QuadraticArnoldVanishingAudit` passed (3,101 jobs).
Their audited declarations report only standard foundational axioms. This
reconciles a stale inventory label; no duplicate theorem API was added.

## Krein trace comparison source-audit reconciliation (2026-10-31)

`Modular.KreinPotentialTrace` is marked as requiring source audit in the
lexical inventory, but the owner already contains both the counterexample and
the canonical replacement. On the finite doubled matrix carrier
`Matrix (ι ⊕ ι) (ι ⊕ ι) R`, it proves
`trace A = superTrace A + 2 * trace (A₂₂)`. For a block matrix
`Z = fromBlocks A B C D`, the Krein-square correction is exactly
`2 * (trace (Dᴴ * D) - trace (Bᴴ * B))`; over `ℂ`, equality of ordinary and
graded traces is therefore equivalent to equality of those two Gram traces.
The identity matrix at `ι = Fin 1` is a concrete disagreement witness. This
does not identify Zorn multiplication with matrix multiplication or assert an
infinite-dimensional trace statement.

The locked build of `InfoGeometry.Modular.KreinPotentialTraceAudit` passed
(3,094 jobs); all four declarations in that audit report only standard
foundational axioms. One pre-existing linter warning notes an unused
`DecidableEq ι` section variable on the generic trace conversion. This
reconciles another stale inventory label without adding duplicate theorems.

## Freudenthal five-grading/contact replacement reconciliation (2026-10-31)

The inventory marks `Exceptional.FreudenthalSymplecticContactRepresentation`
for source audit, while its surrounding owners already contain the complete
counterexample/replacement chain. `legacy_fiveGradedBracket_not_jacobi` has an
explicit nonzero extreme-charge Jacobi readout. Separately,
`symplecticRankTwo_mixedTriple_counterexample` refutes the mixed-triple symmetry
needed by the proposed TKK socket, and `tkk_mixed_jacobi_alpha_beta_alpha_ne_zero`
locates a nonzero `minus1` Jacobi component for its stated witnesses. These do
not prove that every homogeneous Jacobi component fails.

The repaired statement is the faithful bracket representation
`symplecticContactRepresentation_bracket` and its induced
`symplecticContactLieAlgebra` on the existing five-graded carrier. The
coefficient refinement in `FreudenthalContactNormalization` computes the
actual mixed Jacobi defect for parameters `(c,d)` and proves that, when
`[Nontrivial J]`, universal vanishing is equivalent to `c = 1 ∧ d = -2`.
Fixing either standard coefficient gives the corresponding iff even without
that nontriviality assumption. No identification with an exceptional simple
Lie algebra or universal Jacobi theorem for the old bracket is inferred.

The locked builds of `InfoGeometry.Exceptional.FreudenthalCounterexampleAudit`
and `InfoGeometry.Exceptional.FreudenthalSymplecticContactAudit` passed
(8,968 jobs). Their audited declarations report only standard foundational
axioms. This reconciles an inventory label and records the boundary between
the obstructed bracket and its corrected contact Lie algebra; no duplicate
theorem API was needed.

## Cobalt angular-model counterexample and dependency-poset audit (2026-10-31)

The `Physics.CobaltAsymmetryDependency` inventory row is marked for source
audit, but its paired mathematical owner and executable tests already make the
counterexample and corrections explicit. For
`gammaAngularModel amplitude anisotropy angle = amplitude^2 - anisotropy *
sin(angle)^2`, nonzero anisotropy gives anisotropy while
`sin(pi-angle) = sin(angle)` gives reflection invariance; the owner also proves
a concrete nonnegative anisotropic invariant instance. Thus anisotropy alone
does not imply reflection violation. In contrast,
`beta_reflection_invariant_iff` proves that the beta model is reflection
invariant exactly when its alignment parameter is zero.

The owner further proves exact parameter domains:
`betaAngularIntensity a` is nonnegative everywhere iff `|a| ≤ 1`, and
`gammaAngularModel a k` is nonnegative everywhere iff `k ≤ a^2`, including
negative `k`. The finite `Archetype` prerequisite poset is only a dependency
encoding; it does not supply additional physical evidence. The locked build of
`InfoGeometry.Physics.CobaltAsymmetryTests` and
`InfoGeometry.Physics.CobaltPositivityCriteriaAudit` passed (1,962 jobs), and
the audited declarations report only standard foundational axioms. This
reconciles the stale inventory label; the full candidate inventory remains
open.

## Lee–Yang/Asano contraction claim scope reconciliation (2026-10-31)

The `Canonical.LeeYangAsanoDigest` candidate is not itself the missing proof:
it records the polynomial contract and both false and corrected theorem
surfaces. The unrestricted source claim is refuted independently by
`Analysis.AsanoRuelleObstruction.asanoRuelle_unrestricted_claim_false` and the
nondegenerate explicit witness
`Canonical.AsanoRuelleCounterexample.unrestricted_AsanoRuelle_contraction_statement_false`.
The repaired positive route is precisely scoped: the closed-set source claim is
equivalent to `AsanoNondegenerateTopologicalTheorem` in
`Canonical.LeeYangAsanoFullReduction`, while
`Canonical.LeeYangAsanoClosedBoundedNative.source_claim_closed_bounded_native`
proves the bounded closed-set version through the native contraction theorem.
The digest's endpoint-nondegenerate implication still consumes that endpoint
alternative as a hypothesis; it is not an unconditional derivation of it.

The locked build of `InfoGeometry.Canonical.AsanoCounterexampleRealignmentAudit`
and `InfoGeometry.Canonical.LeeYangAsanoClosedBoundedNative` passed (8,974
jobs). The audit reports only standard foundational axioms for the checked
counterexamples, native bounded result, and equivalence. This resolves the
candidate's scope classification without adding duplicate theorem statements;
the broader counterexample inventory remains open.

## Readout reversal/flow square obstruction audit (2026-10-31)

The inventory marks
`Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFlowObstructionCompHaus`
as requiring source audit, although its paired audit module already names the
three owner results. Source inspection confirms the precise implication:
under the explicit readout-transport and reversal/flow-square hypotheses,
`scalar_obstruction_of_reversal_flow_square` forces
`(exp t - exp (-t)) * z = 0` for every observed scalar. For `t ≠ 0`,
`stageObservationRange_zero_of_reversal_flow_square` forces the range to be
zero, and `no_reversal_flow_square_on_nontrivial_range` rules out the square
given a nonzero range witness. This is a conditional obstruction; the owner
does not establish that every reversal has the readout-transport property or
exhibit a particular nontrivial range and reversal satisfying all premises.

The locked build of
`InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFlowObstructionCompHausAudit`
passed (8,993 jobs). All three audited theorems report only standard
foundational axioms. The stale candidate status is reconciled; the full
counterexample inventory and independent semantic review remain open.

## Spin affine fixed-Cartan mixing counterexample (2026-10-31)

The inventory marks `Physics.SpinAffineCasimirRigidity` for source audit, but
the source and `Canonical.KreinSpinPositiveAudit` already provide a concrete
counterexample and corrected criterion. In the owner's `2 × 2` complex matrix
spin representation, `hyperbolic_counterexample` verifies that the
nontrivial pair `(u,v)=(5/4,3/4)` preserves the ladder commutator while failing
the fixed-Cartan raising relation. Thus the ladder bracket alone cannot
certify preservation of the full spin relations.

The canonical replacement is `fixed_cartan_spin_relations_iff`: for the
stated ansatz, both relations hold exactly when `v = 0` and
`Complex.normSq u = 1`. The separate `mixed_cartan_iff` identifies precisely
which relation detects the unwanted lowering component. These results are
specific to the existing finite spin matrix representation and do not claim a
classification of general operator deformations. The locked build of
`InfoGeometry.Canonical.KreinSpinPositiveAudit` passed (8,952 jobs), and its
printed axiom dependencies for the counterexample and criterion were only
standard foundations. This reconciles the candidate status without adding a
duplicate theorem.

## Projective null-boundary permutation/Jones monodromy obstruction (2026-10-31)

The inventory marks
`Projective.ProjectiveNullBoundaryJonesPermutationObstruction` for source
audit, but its owner and paired audit already formalize the counterexample.
For the presented braid group, the square of the first Artin generator maps
to the identity under the finite permutation shadow, while the Jones
representation sends it to `-I` in `GL₈(ℂ)`. The owner uses this kernel
witness to prove that the Jones representation does not factor through the
permutation shadow. The Cl₅₅ bridge further proves its stated exchange-square
loop and non-factorization results. These theorems refute recovery from that
finite permutation shadow; they do not rule out a richer monodromy/local
system.

The locked builds of
`InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstructionAudit`
and `InfoGeometry.Projective.Cl55ProjectiveNullJonesDeckMonodromyObstructionAudit`
passed (9,308 jobs). Their audited declarations report only standard
foundational axioms. This reconciles the source-audit label without adding
duplicate results; global inventory completeness remains open.

## Klein glide scalar-descent witness (2026-10-31)

The owner `Topology.KleinXiAutomorphyObstructionBridge` already proves that
scalar invariance under the affine glide forces vertical periodicity by twice
the glide parameter, while explicitly making no claim about the completed
zeta function. I added the sharp elementary witness
`verticalCoordinate_not_scalarGlideInvariant`: for every nonzero glide
parameter, the vertical coordinate function fails scalar glide invariance.
This supplies an actual counterexample to unrestricted scalar descent and
confirms that the periodicity obstruction is non-vacuous, without making a
claim about any particular analytic zeta function.

The owner audit now prints the new theorem's axioms. The locked build of
`InfoGeometry.Topology.KleinXiAutomorphyObstructionBridgeAudit` passed (3,097
jobs), and the new theorem uses only standard foundational axioms. The
correction is limited to this affine coordinate action; further analytic
automorphy claims remain unproved.

## Split-sedenion socle lift derivation obstruction and probe correction (2026-10-31)

The inventory marks
`Synthesis.SedenionSocleDirectSumSeparationBridge` for source audit. Its owner
contains an explicit failure of the proposed single-slot lift: the
`K13`-parameter `socleDerivationLift` fails the Leibniz rule on a named
split-sedenion pair, and adding any diagonal `G₂` derivation does not repair
that failure. The exact replacement is
`socleDerivationLift_leibniz_iff_eq_zero`: this lift is a derivation of the
actual split-sedenion product iff its matrix parameter is zero. This is a
classification of that lift family, not of all split-sedenion derivations.

The same owner proves joint zero-map injectivity for the verified diagonal
`G₂` family plus the lift, and supplies a nonzero matrix annihilated by the
first two reconstruction probes but detected by a third. Thus two probes are
insufficient on the unrestricted `3 × 3` matrix space; the stated three-probe
separation and joint injectivity are the corrected results. Locked builds of
`InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridgeAudit` and
`InfoGeometry.Synthesis.ThreeProbeReconstructionAudit` passed (3,137 jobs).
The audit checks the criterion, counterexample, joint injectivity, and probe
witness. This reconciles the inventory label without asserting that the
distinct-carrier 17-parameter product action is a derivation of one shared
algebra.

## Krein adjoint versus ordinary unitary counterexample (2026-10-31)

The inventory marks `Canonical.SpinorialCore.KreinAdjoint` for source audit,
but the owner and core axiom audit already separate the two notions. The
rational `2 × 2` boost preserves the signature form while it does not commute
with the signature matrix and is not ordinarily orthogonal. This refutes the
unqualified claim that preservation of an indefinite form forces commutation
or ordinary unitarity. The exact replacement in the generic owner is
`isIsometry_iff_commute_of_unitary`: form preservation is equivalent to
commutation when both ordinary unitary equations hold. With only the left
isometry equation, `isIsometry_iff_adjoint_mul_commutator_zero` gives the
precise condition that the adjoint annihilates the commutation defect.

The locked build of `InfoGeometry.Canonical.SpinorialCore.AxiomAudit` passed
(8,940 jobs). Its printed dependencies for the boost counterexample and
Krein-adjoint results are only standard foundational axioms. This reconciles
the stale candidate label; it does not identify indefinite and positive
adjoints or make claims beyond the owner’s algebraic hypotheses.

## MDPAS finite cellular non-exactness and global-scope boundary (2026-10-31)

The inventory marks `Physics.MDPASJMSouriauGlobalObstruction` for source audit.
Its owner proves the exact finite statement
`sphereArea_closed ∧ ¬ Exact2 sphereArea` on the minimal cellular `S²`
cochain model (`C¹ = Fin 0 → ℚ`, `C² = Fin 1 → ℚ`). This is a genuine
closed-but-not-exact class in that discrete model, not a proof of smooth de
Rham cohomology of the sphere. The same module's finite symplectic and
Kaluza–Klein identities are separate finite-carrier results; its direct-limit
readback concerns the quotient carrier and compatible identities only.

The associated audit explicitly records the external global computation as a
timeout and states that the finite statements do not supply the missing smooth
or Hilbert-space constructions. The locked build of
`InfoGeometry.Physics.MDPASJMSouriauGlobalObstructionAudit` passed (9,186
jobs); checked declarations report only standard foundational axioms. This
reconciles the candidate status while keeping the global analytic claims open.

## Harmonic rectangle mean-value counterexample and exact criterion (2026-10-31)

The inventory marks the `EmergentGeometry.HarmonicQuadraticRectangle` audit
surface for source review. The owner gives an explicit harmonic counterexample
to extending the disk/circle center mean-value property to general
rectangles: for `quadraticHarmonic z = Re(z²)`, the rectangle with half-width
2 and half-height 1 has normalized average 1 while the center value is 0.
For the full quadratic family
`harmonicQuadratic a b c z = Re(a z² + b z + c)`, the canonical exact formula
is
`average = c.re + a.re * (w² - h²) / 3`; the owner proves equality with the
center value iff `a.re = 0 ∨ w = h` for positive half-width and half-height.
Thus the failure is caused precisely by the anisotropic quadratic term on a
nonsquare rectangle; affine terms do not change the centered average.

The locked builds of `InfoGeometry.EmergentGeometry.HarmonicRectangleTests`
and `InfoGeometry.EmergentGeometry.HarmonicQuadraticRectangleAudit` passed
(3,548 jobs). The audited counterexample and general criterion depend only on
standard foundational axioms. This reconciles the inventory candidate without
claiming a rectangle mean-value theorem for arbitrary harmonic functions.

## Fact/logic/prompt corner algebra and decoder-mask boundary (2026-10-31)

The submitted A₈₆ narrative conflates an additive causal attention mask and
token embeddings with algebraic support in a ring. The repository owner
`Routing.FactLogicBypassAlgebra` formalizes only the latter: three orthogonal
idempotent corners, a fact-diagonal plus globally addressed logic-column plus
prompt-diagonal operator, its composition, and compression away from the fact
corner. It proves `fullOperator_logic_column`, `fullOperator_logic_row`,
`fullOperator_mul`, `withoutFact_fullOperator`, and the nonzero fact-corner
erasure counterexample. These algebraic results do not prove neural-network
equivalence, preservation of names or numbers, benchmark deltas, or the
paper's specific decoder mask.

The source-code orientation in the pasted table is false: the published
`_create_mixed_attention_mask` opens all logic rows to every key and allows
prompt rows to read facts and logic. The pre-existing `fullOperator` is a
different, restricted support model and cannot be cited as a formalization of
that implementation. The owner now also defines `publishedMaskSupport` and
proves `publishedMaskSupport_prompt_fact_block`, identifying the allowed
prompt-to-fact block as `P_p * R * P_f` under orthogonal idempotents. This is
the corrected operator-support statement; it does not prove neural-network
semantics, lossless factual retention, or experimental scores. The updated
locked build of `InfoGeometry.Routing.FactLogicBypassAlgebraAudit` passed
(606 jobs); all six audited declarations depend only on standard foundational
axioms (`propext`).

## Penrose circular-coordinate norm mismatch and Witt-polarized replacement (2026-10-31)

The inventory labels `Twistor.PenroseExterior3PeirceQuadraticAudit` for
source audit. Its concrete `twistorCoordinateZero` has
`twistorRealQuadraticForm = 1` but its image under
`twistorCircularPeirceEquiv` has circular-Zorn reduced norm `0`; hence the
linear carrier equivalence is not a quadratic isometry. This is scoped to that
specific direct coordinate map and does not refute the Penrose/Zorn
null-boundary bridge.

The corrected canonical statement uses Witt-polarized coordinates: the
existing `Twistor.PenroseZornWittBoundary.penroseWittZornMap` proves exact
equality of the Zorn norm and the Penrose split-signature form. The completed
equivalence `Twistor.PenroseWittCompositionCompletion.wittZornEquiv` then
proves norm preservation as `wittZornEquiv_norm`; its transported product
preserves the original twistor quadratic form by `selectedMul_norm`. These
are alternative, map-specific theorems; they do not turn the failing direct
coordinate equivalence into an isometry or identify the transported product
with the native pointwise product on spinor coordinates. The focused locked
build of `InfoGeometry.Twistor.PenroseExterior3PeirceQuadraticAudit` passed
(9,007 jobs, exit 0), verifying the counterexample and its source dependencies.
The corrected owner `InfoGeometry.Twistor.PenroseWittCompositionCompletion`
also passed its focused locked build (8,984 jobs, exit 0), directly checking
`wittZornEquiv_norm` and `selectedMul_norm`.

## Freudenthal mixed-triple obstruction and contact-Lie replacement (2026-10-31)

The source inventory flags `Exceptional.FreudenthalContactRealignmentAudit`
and `Exceptional.FreudenthalSymplecticContactAll` for review. Their owners
exhibit two distinct structures. The legacy `tkkTotalBracket` has a mixed
Jacobi component equal to
`mixedSymplecticBracket D z y x - mixedSymplecticBracket D x y z`; its
vanishing for every triple in a set is equivalent to pairwise vanishing of
the Freudenthal symplectic form there (`tkk_mixed_jacobi_on_iff_pairing_zero`).
The `alphaCharge` and `betaCharge` witnesses prove that the required
mixed-triple identity fails in general and that the corresponding legacy
Jacobiator is nonzero.

The canonical replacement is the separate `symplecticContactBracket` on the
existing five-graded carrier. Its faithful block representation into
`Module.End ℝ (SymplecticContactModule ...)` identifies the bracket with the
associative-operator commutator, yielding the Lie ring/Lie algebra laws and an
injective Lie representation. The contact Euler operator supplies five
adjoint grade spaces and their bracket-addition law. This does not make the
legacy total TKK bracket a Lie bracket or identify it with the contact
bracket. The locked build of
`InfoGeometry.Exceptional.FreudenthalContactRealignmentAudit` passed (8,942
jobs); audited declarations depend only on standard foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`). Existing linter warnings occur
in imported Freudenthal owners. The repository-wide inventory remains open.

## Spin-affine/exterior audit scope reconciliation (2026-10-31)

The inventory flags `Canonical.SpinAffineExteriorAudit`, which is a
transitive axiom-audit module rather than a new counterexample owner. Its
source traces the existing hyperbolic spin-mixing counterexample and its
fixed-Cartan criterion, then audits three separately typed packets: affine
frame recovery, exterior-to-circular CAR intertwining, and negative Clifford
reflection. The source does not identify those carriers except through the
explicit maps and intertwining results. The locked build of
`InfoGeometry.Canonical.SpinAffineExteriorAudit` passed (9,017 jobs); printed
dependencies use standard foundational axioms. Imported owner warnings
remain. This reconciles the audit row without asserting a cross-carrier
equivalence.

## Newly surfaced countermodel owners and focused replay (2026-10-31)

The expanded tracked-tree lexical scan surfaced countermodel declarations in
eight owner files not represented in the prior 168-entry source inventory.
Those files are now recorded with their exact declaration names and source
hashes in `artifacts/counterexample_audit/source_inventory_20261030.json`;
the inventory contains 176 entries. The scan remains lexical and does not
establish semantic completeness.

The owner statements provide the following corrected scopes:

- `Quantum.DikinApolloniusStrictnessAudit` and
  `Quantum.DikinBlahutStrictnessAudit`: factor 1 can preserve a boundary point;
  strict shrinkage follows under a genuine factor `Kc < 1` and positive
  radius. Their `#print axioms` output reports only standard foundational
  axioms.
- `Omega.CircleDimension.MultiPrimeSpectrum`: equal singleton marginals do
  not determine pair-support values; the owner also proves the exact
  piecewise spectrum of the second finite support family.
- `Omega.CircleDimension.ResidualEntropyLowerBound`: the finite-injection
  statement fails when `k > r`; the corrected theorem requires `0 < t` and
  `k ≤ r`.
- `Omega.Conclusion.RanktwoSmithBlindclassBooleanPrimeblockTorsor`: the
  divisor-count statement fails at `(a,b)=(0,0)` under natural-number total
  division; the corrected count assumes both inputs are positive.
- `Omega.POM.A4TCyclotomicAdjacencyInjection`: the proposed target sign pattern
  fails at the order-four specialization; the owner proves a corrected core
  identity for nonzero `v` and the paper specialization for `h ≥ 4`.
- `Omega.POM.A4TNewmanLinearResponseConstant`: the displayed rational formula
  does not imply the octic, as shown at `zStar=2`; the replacement includes
  the Newman-root hypothesis.
- `Omega.RecursiveAddressing.PrefixSiteMinVisibleQuotient`: killing the
  listed `alpha` values and surjectivity of `pi` do not imply factorization
  through `pi`; the canonical quotient uses all visible cocycle values.

A single sequential locked build of all eight owner targets passed in 3,216
jobs. The build emitted existing deprecation and linter warnings; it was not a
warning-free repository build. Only the two Dikin audit modules print axioms
for their named declarations in this batch, and those outputs list standard
foundations. The other targets were kernel-checked by the build, but their
axiom dependencies were not separately audited here. The wider objective of
finding every semantic counterexample and proving every appropriate
replacement remains open.

## Refutation-category source reconciliation and replay (2026-10-31)

The tracked lexical scan's seven `refutation` rows resolve to three actual
counterexample families and four positive/conditional theorem surfaces (the
Xi source contributes two declaration names). The Jordan sign witness, the
`Fin 36` non-affine table refutation, and the exponential-scale recurrence
counterexample are now recorded alongside their exact owner hashes in the
maintained source inventory. The CP-visible contrapositive, Hecke coefficient
evaluation, and Xi divisibility/size implication are recorded as name-based
false positives, not counted as counterexamples. In particular, `2^n` is
recurrent and has infinite range, refuting finite range as a criterion for
C-finiteness.

The six relevant owner modules were kernel-checked in one sequential locked
build (9,287 jobs, exit 0). The umbrella dependency replay emitted numerous
existing linter and deprecation warnings, so this is not a warning-free build
or a per-theorem axiom audit. The source inventory now has 182 owner-file
entries. This closes only the currently scanned countermodel and
refutation-name slices: the scan still has large unreconciled obstruction,
identifiability, and negative-boundary candidate families, and its lexical
rules do not establish semantic completeness.

## Initial obstruction-marker source batch and replay (2026-10-31)

Six newly surfaced obstruction-marker owner files were read and replayed.
Most markers are not counterexamples: the Akivis term is an exact
associator-defect formula under its alternative-law hypothesis; the
cyclotomic Peirce result is an ambient-unit boundary with an exact supported
corner image; the Dihedral result is a conditional order criterion; the two
`muPaper` declarations merely evaluate square-obstructed Möbius values; and
the Krein result assumes an explicit certificate supplying its no-leakage
premises. The genuine counterexample in this batch is the attention trace
claim: `chiral_obstruction` has diagonal `(M₀₀, -M₁₁)`, so positive diagonal
entries do not imply positive obstruction trace. The owner gives the exact
criterion `M₀₀ > M₁₁`, a positive-diagonal zero-trace witness, and keeps the
positive trace theorem scoped to the separate diagonal core.

The six owner targets passed a sequential locked build (9,377 jobs, exit 0).
The build emitted existing warnings in dependencies; it was not warning-free
and did not separately print axioms for every declaration. The maintained
source inventory now has 188 owner-file entries. This is an initial
source-classified slice of the much larger obstruction-marker queue, not a
complete audit of that category.

## Conditional and positive obstruction-owner batch (2026-10-31)

Six additional obstruction-marker owners were source-reviewed and kernel-checked: the Cayley–Hestenes intertwiner bridge, Chiral KMS owner, and four conformal-anomaly owners (degenerate, operator, readout, source). The intertwiner result is conditional on source commutation, alongside unrestricted commutator naturality; KMS chirality is an iff characterization and product closure; conformal zero/block/readout statements retain their explicit hypotheses and definitions. These are scoped positive or conditional results, not counterexamples.

The six targets passed one sequential locked build (9,030 jobs, exit 0). Existing dependency warnings were emitted; this was not warning-free and did not separately print per-declaration axioms. The source inventory now has 194 owner-file entries. The obstruction-marker and other lexical queues remain incomplete, and lexical coverage is not semantic completeness.

## Algebraic counterexample and replacement batch (2026-10-31)

Seven owner/audit modules were reviewed. Two genuine counterexamples were confirmed: a positive-dimensional finite real matrix commutator cannot equal the identity (trace obstruction), and the right E22 tangent equation on off-diagonal Zorn directions holds as an operator only for the zero direction. The Zorn owner supplies an explicit U 0 witness and the valid left E11 replacement. A third concrete finite witness shows entropy change need not equal Massieu-potential change; its owner supplies the entropy expectation formula and KL/Bregman identity. The H3 sparse Jordan pair is explicitly positive (it satisfies the global law), and the full split Albert trace pairing is nondegenerate. Two audit wrappers print standard axiom dependencies.

The five-target locked replay had a module-name typo for the experimental CCR audit target and exited 1 for that missing target; the other four targets replayed. The corrected CCR audit target then built successfully (3,093 jobs); the other batch replay had reached 3,131 jobs. No source edits were needed. The inventory now has 200 owner-file entries. This records a reviewed slice only; the remaining lexical queue is still under audit.

## Analytic, arithmetic, and operator-obstruction batch (2026-10-31)

Six more candidate paths were source-reviewed and kernel-checked. Confirmed counterexamples: the signed-reflection residue assertion fails for 1/z; balanced residues do not make either local pole removable; weakening the primitive-set threshold to x₀>0 fails at x₀=2, x=1, A={2}; and a nonzero ZZ boundary increment in the specified matrix-stage embedding breaks strict commutator transport. Their scoped alternatives are an analytic-extension iff criterion, the strict x₀>2 bound (with the separate large-divisor analytic input left as a Prop), and an iff compatibility criterion requiring zero coupling. The Asano–Ruelle bridge/closure theorems are conditional positive results under their explicit zero-free, nondegeneracy, endpoint, and boundedness assumptions. The algebraic alternatives audit is an axiom-readback wrapper for reusable noncommutative statements, not a counterexample.

All six selected Lake targets passed a sequential locked build (9,014 jobs, exit 0); existing warnings remain. The maintained inventory now has 206 owner-file entries. The scan remains lexical and the full counterexample audit is still incomplete.

## Spectral, commutator, and flow-compatibility batch (2026-10-31)

Six further candidate owners/audits were reviewed. The concrete counterexample is the modular identity-kernel case, which refutes a universal super-Hamiltonian generator equality; the owner gives a corrected equivalence conditioned on the canonical-seed flow equation. A separate reversal-flow obstruction is conditional: the assumed square and readout transport force the observed range to zero at nonzero time. The Fibonacci/Jordan result is finite-carrier only (normality iff zero shear), the kernel-commutator implication retains its explicit bridge premise, the Kitaev boundary trace pairing is nondegenerate on its represented carrier, and Lee–Yang/Asano preparation lemmas explicitly stop before the topological closure step.

All six targets passed the sequential locked Lake replay (9,415 jobs, exit 0), with existing dependency warnings. The source inventory now contains 212 paths. This remains an incremental source audit; the lexical scan still does not establish semantic completeness.

## Carrier, cocone, and grading obstruction batch (2026-10-31)

Six more owner/audit paths were source-reviewed and kernel-checked. Concrete failures: the proposed 3×3/4×4 matrix carrier identifications with Zorn/Albert carriers fail by dimension; native real Zorn multiplication cannot inject multiplicatively into an associative semigroup; a faithful compatible diagonal cocone into two copies of the Cl(1,1) limit fails the colimit uniqueness clause; and a nonzero Cl(5,5) creation word has occupation grade five, outside the proposed grade-two/five-grade window. The exact alternatives are carrier-scoped exclusions, a universal-property counterexample, and an explicit grade-five witness. The BKM positivity obstruction and transported Zorn polar nondegeneracy theorem are conditional/positive results, not counterexamples.

All six targets passed one sequential locked Lake build (9,055 jobs, exit 0). The inventory now contains 218 paths; the remaining lexical candidate families still require source audit.

## Jacobi, normalization, and carrier-metric counterexamples (2026-10-31)

Six more owners/audits were source-reviewed and kernel-checked. Confirmed failures: the legacy Freudenthal five-graded bracket violates Jacobi and the symplectic rank-two operator fails the mixed-triple law (the corrected contact bracket is a separately proved, hypothesis-scoped alternative); the stated quadric logarithmic wedge identity has numerator 52 at a nonisotropic integer triple; the specified Zorn-to-doubled-Krein map is not an isometry at uPlus; and secondary normalization is not additive, with mass-weighted pooling as the corrected identity. The Fisher/para-symmetry obstruction is conditional on nonnegativity and fixed-symmetry hypotheses. The S² result is verified on the explicitly defined minimal CW model; the separate global de Rham computations are timeout records, not proofs.

All six targets passed a sequential locked Lake build (9,395 jobs, exit 0). The inventory now contains 224 paths. This source-level candidate audit remains incomplete, and no claim of semantic exhaustiveness is made.

## Projective, route, and low-dimensional obstruction batch (2026-10-31)

Six more candidate owners/audits were checked. The finite permutation shadow loses braid phase: the first generator square maps to identity under permutation but to −I under the Jones representation; the Q55 result retains its explicit path/Artin-homotopy premises. Concrete routing matrices refute several automatic rules (sibling contrast persistence, support commutation, squared-charge idempotence, and core-transpose identification), with replacement results under synchronized-retraction/factorization hypotheses. The two-dimensional skew-map theorem is an exact one-parameter classification; the Klein glide theorem gives a conditional vertical-period requirement; and the circle-dimension equivalence applies only to its explicitly defined rank/torsion model.

All six targets passed the sequential locked Lake build (9,327 jobs, exit 0). The inventory now contains 230 paths; the remaining lexical queue is incomplete.


## Circle-dimension and quantitative obstruction batch (2026-10-31)

Six further owners were reviewed and kernel-checked. The affine splitting theorem is limited to its explicit affine product model; the null-readout theorem only combines supplied implications; and the Stokes lattice theorem restates its two hypotheses rather than proving a general Stokes result. The ENNReal accumulation theorem proves that a positive per-step lower bound and a finite uniform upper bound are incompatible. The ambiguity-shell owner constructs a periodic nonconstant witness from its residue hypothesis, without establishing an analytic amplitude claim. The CRT owner derives a normalized linear-budget bound from its supplied witness and protocol assumptions, but does not generate those assumptions.

All six targets passed a sequential locked Lake build (9,327 jobs, exit 0), with existing dependency warnings. The inventory now contains 236 paths. The lexical candidate queue remains incomplete and is not a semantic completeness claim.


## Exponent threshold and finite additive ledger batch (2026-10-31)

Two conclusion owners were reviewed and kernel-checked. The circle threshold result is a consequence of its encoded one-circle rank and exponent-gap hypotheses. The finite additive linearization result rules out an injective multiplicative-to-additive map on naturals under the supplied valuation/iteration data and imported finite-ledger lemmas; its conclusion is scoped to that algebraic setup.

Both targets passed a sequential locked Lake build (8,927 jobs, exit 0), with an existing unused-simp warning in a dependency. The inventory now contains 238 paths. The source audit and lexical queue remain incomplete.


## Schur-concavity counterexample and theorem-scope audit (2026-10-31)

Six conclusion owners were checked and kernel-verified. `BlockConsistencyNotSchurConcave` contains a genuine explicit counterexample for its defined list majorization and block response; it also proves the reusable replacement that mutually majorizing inputs must receive equal values under Schur concavity. By contrast, the C6 result uses `PUnit` as every Jacobian carrier and type equivalence as isogeny, so it does not establish geometric nonsimplicity. The Binfold theorem proves a positive-baseline/equivalence witness but does not state or refute uniformization. The Abel–Mertens owner is an alias; the Cdim natural-code and bounded-order results retain their substantial hypotheses.

All six targets passed one sequential locked Lake build (8,954 jobs, exit 0), with existing deprecation and simp warnings. The inventory now contains 244 paths. Audit completeness remains unestablished.


## Finite models, matrix identities, and assumption-only owners (2026-10-31)

Six more owners passed source review and locked kernel checking. The ambiguity Jordan-chain theorem proves existence and uniqueness for its explicit one-dimensional rational recurrence; the anchor theorem proves finite complex-matrix determinant and comparison identities under its rank/weight assumptions. The atomic-surgery tomography and single-congruence results follow from a coefficient function defined by the target residue and power law, so their proofs establish the constructed finite model rather than recover an independently specified process. The LDP owner is a direct consequence of supplied propositions, and the audit-budget owner assumes the exact negated bound it returns.

All six targets passed one sequential locked Lake build (3,175 jobs, exit 0); existing dependency deprecation and simp warnings remain. The inventory now contains 250 paths. The audit remains incomplete.


## Nilpotency, finite encoding, and growth-model batch (2026-10-31)

Six more owners were reviewed and kernel-checked. The nilpotent matrix theorem gives the expected lower bound on vanishing exponent from a sharp power. The balanced natural-number profile proves a finite q-power inequality for q≥1; the BigWitt/Gödel owner proves encoding laws and equal-length recovery within its finite list model. The binary readout injectivity remains conditional on an explicit finite scalar-map injectivity premise. Two genuine counterexamples are model-specific: the Fibonacci-indexed constant-two model refutes its stated uniform near-lossless bound, and the sequences 1, m+1, (m+1)^2 admit no common normalization with three nonzero finite limits. These do not establish claims about unspecified external complexity measures.

All six targets passed a sequential locked Lake build (3,686 jobs, exit 0), with inherited deprecation and style warnings. The inventory now contains 256 paths. The broader source audit remains incomplete.


## Finite cardinality, boundary, and derivation-scope batch (2026-10-31)

Six additional owners were source-reviewed and kernel-checked. The Blackwell-labelled result is the finite pigeonhole theorem for explicit `Fin` carriers. The Born-weight owner constructs normalized squared-norm weights from a nonzero finite vector; despite its name, it invokes no Hardy or fold-expectation result. The boundary dimension theorem is a conditional asymptotic lower bound from its stated volume and Lipschitz premises, while the finite-audit barrier projects an imported complexity trilemma under supplied hypotheses. The parity/Lie repair count is arithmetic on definitions (rank `3−1`, components `2^rank`) and does not construct a Lie repair. The prime-replay theorem is conditional on an assumed strong-subsequence vanishing principle.

All six targets passed one sequential locked Lake build (8,935 jobs, exit 0), with existing style warnings. The inventory now contains 262 paths. The audit remains incomplete.


## Reduction wrappers and finite support/crowding batch (2026-10-31)

Six more owners were reviewed and kernel-checked. The two undecidability theorems are reduction wrappers whose source undecidability and reduction equivalences are assumptions. The carry-support result is a valid finite-mass concentration lemma under total-mass, support, and uniqueness hypotheses. The cdim power-law owner applies finite pigeonhole to a supplied same-cell bound; the geometric estimate is data, not derived. The precision-ledger owner is the direct transitivity consequence of separation and a crowded pair. The Ramanujan center/top owner projects an imported reconstruction after assuming the top coefficient and vanishing-above facts.

All six targets passed a sequential locked Lake build (3,099 jobs, exit 0), with inherited style/deprecation warnings. The inventory now contains 268 paths. The wider candidate audit remains incomplete.


## Prime-ledger and collision-claim scope audit (2026-10-31)

Six more owners were source-reviewed and kernel-checked. The constant-circle-dimension theorem gives a genuine cardinality counterexample to any uniform support-size bound from that invariant; the cofinal-ledger theorem is the standard finite-dimensional rank obstruction. The circuit-output theorem instead uses the decidable predicate `M≤x`, an indicator defined from `C 0`, and a supplied identity/constant model, so it is not a Turing-halting or Renyi-entropy reduction. The collision blowup theorem is an order consequence from assumed divergence and domination. The generating-function radius theorem merely combines its two radius conclusions as hypotheses; its q, tail coefficients, and tail-shape hypotheses are unused. The affine-rank-one theorem is valid conditional algebra from its supplied factorization premise.

All six targets passed one sequential locked Lake build (3,173 jobs, exit 0), with existing deprecation/unused-variable warnings. The inventory now contains 274 paths; source audit completeness remains unestablished.


## Collision, comoving, and compact-kernel model audit (2026-10-31)

Six more owners were reviewed and kernel-checked. The collision minimal-recurrence formula is conditional on a hand-specified sequence profile and an assumed characterization of its minimal order. The numerator owner proves a genuine polynomial root equation and a radius limit for its explicit polynomial. The comoving identifiability theorem only combines supplied propositions; the prefix-frontier theorem imports one identity and assumes its collision witness implication. The compact-Lie kernel is definitionally `Fin n`, so finite-ness is an instance fact rather than a compact-Lie theorem. The phase-ledger incompatibility is a valid arithmetic contradiction between rank one and rank at least two; its phase field plays no role.

All six targets passed one sequential locked Lake build (3,101 jobs, exit 0). The inventory now contains 280 paths. The broader owner audit remains incomplete.


## Finite-support, asymptotic, and topological-group batch (2026-10-31)

Six more owners were reviewed and kernel-checked. The fiber/Lee–Yang encoding is a conditional algebraic bridge from divisor data to imported polynomial/root identities. The Euler-surgery theorem proves only eventual equality outside a finite coefficient change and returns its logarithmic formula as an assumption. The phase/prime-ledger result is the constant-function noninjectivity counterexample. The conductor prefactor theorem proves a genuine asymptotic sandwich invariance; the conductor-two nonrepairability file is only the explicit sequence `2^n` model and disclaims an arithmetic Ramanujan conclusion. The connected/profinite result is a substantive topological-group theorem under its explicit connectedness, total-disconnectedness, and bounded-exponent hypotheses.

All six targets passed one sequential locked Lake build (3,109 jobs, exit 0), with existing deprecation/style warnings. The inventory now contains 286 paths. Audit coverage remains incomplete.

## Consensus, finite-boundary, and arithmetic-model batch (2026-10-31)

Six additional owners were source-reviewed. Five passed the sequential locked Lake build; `ConsensusFunctorSeparatedNotSheaf.lean` failed elaboration at its paper-facing theorem because its proof supplies three conjunction branches for a two-conjunct goal. Its exact finite criterion (`global_readout_iff_pairwise_agreement`) and explicit two-site disagreement witness are distinct claims and should not be conflated with that failed declaration. The outer-boundary owner proves a finite inclusion-exclusion support identity; the weighted-boundary owner proves minimum hitting-set optimality for pairwise-disjoint finite boundaries. The critical-comb owner studies explicitly defined divisibility-indicator averages, not Fourier transforms of independently constructed measures. The critical-kernel owner assumes the inverse-square formula for its output weights, so it is conditional algebraic reconstruction. The delay-three result is a natural-number inequality on definitions, not a model-level delay theorem.

The batch build exited 1 due to the consensus owner failure (five other targets completed; 3,092 prerequisite/replay jobs were reached before failure). The inventory now contains 292 paths. Source audit coverage remains incomplete.

## Finite density, pole-set, and scalar-model batch (2026-10-31)

Six further owners were reviewed and passed the sequential locked build (3,176 jobs). The T₅ root-count owner defines the density as a three-value function, then verifies support and moments; the arithmetic distribution itself is not derived there. The diagonal-rate owner proves correct formulas for its stated scalar-collapse parametrization, which does not meet the noncommutative operator scope. The digital local-factor theorem is a genuine finite-set equivalence between finite pole union with finite multiplicities and finitely many active factors; its unit-circle premise is unused, and it contains no analytic rational-function construction. The even-modulus parity theorem directly unfolds its assumptions. The endpoint eigenpair theorem proves a finite algebraic consequence but assumes the output weights and atlas recovery. The entropy-gap theorem is a valid scalar estimate from supplied bounds, not an operator-algebra result. The inventory now contains 298 candidate paths; coverage remains incomplete.

## Fibadic seed and definition-level claims batch (2026-10-31)

Six additional owner files were source-reviewed. Their exact scopes are recorded in the inventory: prime-axis minimality is definition unfolding; the depth-slope identity is rational cancellation with an unused depth hypothesis; dominant-depth selection is a hard-coded `Fin 3` scalar example; the gcd kernel “spectrum” package unfolds supplied data; the gcd projector identities are divisor-set algebra with an identity readout and unused finite-support premise; and the purported Q₅ realization is defined as an integer root of `X²-X-1`, with a structure-field obstruction rather than a Q₅ carrier. The sequential locked build is still waiting for the shared lock, so these six records remain unverified by Lean in this batch. Inventory count: 304 candidates. Coverage remains incomplete.

Another six source reviews are recorded but also await the shared build lock. The finite-depth chain uses an imported `ZMod` morphism/divisibility criterion and imports its profinite conclusion unchanged. The finite-package undecidability result reduces to finite decidability and a propositional contradiction. The fiber-Walsh theorem is a substantive finite Boolean-cube cancellation identity. The audit-dimension theorem assumes both regime bounds in its data structure. The finite-defect/Toeplitz theorem imports its reconstruction and negative witness and assumes the scale inequality it returns. The holography “triple incompatibility” theorem is propositional logic only. Inventory count: 310 candidates; these records are source-reviewed, not yet kernel-verified.

Six more source reviews are now logged, likewise awaiting the shared lock. The selector result is conditional on an abstract necessary lower bound; the Busy Beaver theorem assumes its code-to-halting-time specification in the data; the complexity trilemma packages imported results; the collision/Hankel theorem defines its “exact rank” witness by setting all rank fields equal to the parameter; the double-obstruction file has an empty data structure and forwards imported claims; and the linear/nonlinear bifurcation combines imported statements with an injectivity bound. Inventory count: 322 candidates. All 24 records added since the last successful batch still need their queued locked-build result before being marked kernel-verified.

Six more owner reviews are logged as pending kernel verification. The “no thermal singularity” statement is finite-sum positivity under explicit positivity/nonemptiness hypotheses. The prime-recognition obstruction is assumed in the protocol structure, and the pullback equality is unused; the adjacent postprocessing result is propositional identity. The fixed-scale moment theorem gives an actual three-moment uniqueness result and a two-moment collision witness. The conditional-expectation theorem proves noninjectivity from a supplied finite-fold collision. The prime-product encoding theorem proves subset/divisibility and intersection/gcd correspondences under injective prime labels. The Boolean-cube result is the elementary partition by fibers of a function. Inventory count: 328 candidates; 30 additions since the last successful build remain pending.

Six further owners were source-reviewed while the lock remains occupied. The golden-resonance maxfiber lift proves divergence for a collision profile and maxfiber sequence chosen by formula, without a fold-map construction. The index-two quotient count is correct finite cardinality. The partition Walsh result aliases its H and W terms and imports the cancellation fact. The projective-simplex theorem is a valid coordinatewise phase quotient result, outside the noncommutative operator scope. The single-pair obstruction uses constant and witnessed equalities defined into the model. The TQFT sectorization theorem assumes its centrality, subalgebra, uniqueness, and partition-function claims. Inventory count: 334; 36 records since the last successful batch remain kernel-unverified.


## Walsh, zero-set, and threshold-claim source review (2026-10-31)

Six more conclusion owners were source-reviewed while the shared build lock remained occupied. The Walsh Gram/fiber theorem is a substantive finite orthogonality and average-energy result. The two zero-divisor files duplicate a definition-level set classification using an imported Fibonacci gcd fact; their Boolean flip witness does not act on kernel elements. The active-Fourier support bound assumes the sum-of-squares identity, the upper-envelope theorem returns its hypotheses, and the PI-degree threshold follows from an assumed iff characterization. These six entries remain pending kernel verification. Inventory count: 340; 42 additions since the last successful batch await locked-build results. Coverage remains incomplete.


## Recurrence, truncation, and finite-decoder source review (2026-10-31)

Six more owners were source-reviewed; all remain pending the locked kernel build. The S₂ and conditional S₃ sequence results are genuine minimal-recurrence arguments in their stated integer/rational models. The Borwein “analytic obstruction” assumes a conjugacy predicate that itself implies positive radius, so it establishes a logical incompatibility rather than an analytic theorem. The even-zeta first-difference result is a valid conditional coefficient-cancellation identity. The sufficient-statistic file proves a finite decoder success bound and a Fibonacci limit for its defined fiber model, without constructing an external fold map. The four-moment rigidity theorem is genuine recurrence identification under its nonzero Hankel determinant premise. Inventory count: 346; 48 records since the last successful batch await locked-build evidence. Coverage remains incomplete.


## Monotone-gate counterexample and finite-model review (2026-10-31)

Six further owners were source-reviewed and are pending locked verification. `FreeEnergyGatesMonotonicityObstruction` contains a genuine finite counterexample pair (NOT and odd parity) to expressibility in its monotone gate closure, with the monotonicity theorem as the canonical replacement. The interval non-approximability claim is conditional on abstract supplied energy/undecidability specifications. The frozen-phase conclusion only returns assumptions and leaves a parameter unused. The regular-simplex file proves finite rational coordinate identities. The three-mode gauge conclusion is the contrapositive of its hypothesis, and the super-Poisson file is a conditional quotient-limit calculation without encoded distributional semantics. Inventory count: 352; 54 source-reviewed additions await locked build evidence. Coverage remains incomplete.


## Global-obstruction and resolution-tower source review (2026-10-31)

Six additional owners were source-reviewed; all await the locked build. The common-clock theorem assumes the clock-to-obstruction implication in its data, the null-remainder theorem assumes the exact readability/obstruction equivalence it concludes by contraposition, and global-spectrum compatibility already includes the global descent conclusion. `GlobalMixedHiddenStateNoFaithfulFiniteAbelianObservation` is a genuine infinite-to-finite noninjectivity result, but its group/observation title adds no structure. The Gödel–Lee–Yang IFS file proves arithmetic seed equalities only. The resolution-tower file proves root-of-unity norm one; its degree identities are definitional and its primitive-root clause is not used. Inventory count: 358; 60 records since the last successful batch await locked-build evidence. Coverage remains incomplete.


## Gödel-prefix, resonance, and halting-model source review (2026-10-31)

Six further owners were reviewed and await locked kernel evidence. The Gödel prefix criterion is a valid encoding-injectivity result, and the golden alternating-constant formulas are algebraically correct but do not establish the broader narrative. `GoldenResonanceIntegerTraceNotL2` has a scope defect: “logarithmic divergence” is defined as positivity at each index, while its non-L² conclusion is obtained by contradiction between two clauses of a hand-built realization predicate; no summability or Parseval result is shown. The exact halting budget theorem returns structure fields, and the valuation/Walsh unification is a finite two-branch toy model. The Hankel file only combines imported owner theorems. Inventory count: 364; 66 additions since the last successful batch await locked-build evidence. Coverage remains incomplete.


## Finite-threshold, hypercube, and coordinate-chart review (2026-10-31)

Six more owners were source-reviewed; all await locked kernel checking. The Hankel finite-modulus owner proves periodicity for a finite permutation and a 2·rank threshold built into its locking predicate; its separate determinant-prime result assumes the determinant progression. The hidden-face classification assumes both substantive threshold premises. Hydrogenic pair collapse is a direct consequence of supplied invariances and a state-pair equation, with an unused nonzero-m premise. `HypercubePhase` is correct finite enumeration for five fixed dimensions. The dense-orbit theorem is an aggregator of independently owned results. The Joukowsky coordinate file proves explicit elementary chart and metric identities in its stated domain. Inventory count: 370; 72 entries since the last successful batch await locked build evidence. Coverage remains incomplete.


## Finite audit, algebraic lifts, and resolvent source review (2026-10-31)

Six further owners were source-reviewed; kernel verification remains queued. The joint finite-audit theorem composes three separately owned results. The Joukowsky lift is a valid finite real quadratic-root/sign-permutation model, not a Galois realization. The fixed-ray RH conclusion depends on both an assumed upper bound and an assumed necessary lower bound. The Kirchhoff “determinant” file is only scalar real algebra under a substitution premise, not a matrix determinant theorem. The layered depth result is a valid contradiction from explicit finite bounds, with a tautological unused branch premise. The Leyang edge result proves a finite-N product/log-derivative formula and does not prove a limit. Inventory count: 376; 78 entries since the last successful batch await locked-build evidence. Coverage remains incomplete.


## Local-field labels, finite cube forms, and S₄ stabilizer review (2026-10-31)

Six more owners were source-reviewed and await the queued build. The Q₅ cubic file verifies finite-field rootlessness and a discriminant calculation, but its extension invariants and cyclic Galois packet are definitions/constants rather than a local-field construction. The hyperbola closure result is a finite-union topological consequence of an imported dense-orbit theorem. The Boolean-cube exact-form identity is a genuine finite result with no Lattès dynamics. The local-doublezero “classification” is an exhaustive two-constructor model with imported seed values. The quadratic-factorization theorem forwards an imported primitive-cover certificate without constructing the cover here. The off-diagonal S₄ stabilizer theorem is a genuine finite permutation result. Inventory count: 382; 84 records since the last successful batch await kernel-build evidence. Coverage remains incomplete.


## Channel reconstruction, derivative, and sequence-source review (2026-10-31)

Six more owners were source-reviewed and remain pending the shared locked build. The Rademacher/circle-ledger theorem proves imported cumulants plus a carrier-cardinality mismatch, not an orthogonality relation. The rho456 file gives valid finite log-derivative formulas, with the normalized “rho” functions defined as the target wall factors. The S₅ two-channel theorem is genuine finite rational linear algebra, including explicit noninjectivity witnesses for each channel separately and uniqueness from both together. The transposition/Jacobian result composes imported owners. The Lk first-zero sequence theorem contains substantive monotonicity and limit arguments for its explicit sinc formula. The Lmax theorem is conditional on an already supplied prime witness. Inventory count: 388; 90 entries since the last successful batch await kernel-build evidence. Coverage remains incomplete.


## Ledger-domain correction and finite-observation source review (2026-10-31)

Six additional owners were reviewed and remain pending locked verification. The macroscopic resonance example defines exactification as identity and chooses its collision profile by formula. The finite-consensus result inherits a global-clock obstruction field. `LocalizedColimitFiniteLedgerLinearizationObstruction` supplies a useful canonical correction: assuming multiplicativity on all naturals forces the ledger to vanish already from 0·n=0, so the prime-product relation is unnecessary; a positive-natural domain would require a different hypothesis. The Čech result only unpacks supplied exactness/implication premises. The localized-solenoid result is a valid finite prime-divisibility criterion but has no solenoid/zeta carrier. The Stokes-nonseparation theorem is a real counterexample in its explicit Fin 2 model, where the observable is defined independent of the point. Inventory count: 394; 96 entries since the last successful batch await kernel-build evidence. Coverage remains incomplete.

## Objective arithmetic, finite Hilbert features, and factor-through counterexample review (2026-10-31)

Six more source files were reviewed; all await the shared locked build. The M₂ conclusion only forwards imported exact-sequence/separation declarations. The metallic-integer result proves a substantive Pareto comparison for its defined real objectives. The latch file checks selected `Nat.clog` values and bounds, not the general transducer theorem in its prose. The mixed-collision owner proves finite power-feature Hilbert identities and equality criteria for normalized NNReal data. The mod-2 owner is a valid finite hard-coded counterexample to score recovery through the specified shadow map. The bad-prime support result merely unpacks its assumed implication into set inclusion. Inventory count: 400; 102 entries since the last successful batch await kernel-build evidence. Coverage remains incomplete.

## Finite group classification, Boolean compilation, and abstract obstruction review (2026-10-31)

Six further owners were source-reviewed; all are pending locked kernel evidence. The rank-two jump result is a genuine classification of homomorphisms on `Equiv.Perm (Fin 2)` to `ZMod 2`. The monotone Boolean owner contains a constructive finite-cube DNF embedding; its “exactly monotone” package is conditional on supplied hypotheses, and the free-energy seed portion is arithmetic only. The barrier/residue result correctly derives a ratio limit from two assumed sharp asymptotics. The two complete-invariant files prove standard abstract undecidability implications from supplied undecidability premises. The total-order-time-functor conclusion is propositional consequence of abstract clock-obstruction assumptions, with no local Cech construction. Inventory count: 406; 108 entries since the last successful batch await kernel-build evidence. Coverage remains incomplete.

## Conditional audit packages and operator-rank claim review (2026-10-31)

Six additional owners were source-reviewed and await the shared build. The universal two-axis obstruction stores its decisive profile split and both impossibility claims as structure fields. The restricted-DPI result unfolds its loss identity and imports the fiber-parity conclusion under supplied component hypotheses. The nonzero-spectrum theorem returns its spectral constancy premise and locally proves injectivity of the window budget on the stated range. The infinite-rank threshold and no-scalar-kernel files are contraposition wrappers over supplied implications. The ordered-Nevanlinna conclusion simply packages a supplied completeness implication and counterexample. Inventory count: 412; 114 records since the last successful batch await kernel-build evidence. Coverage remains incomplete.

## Finite update models, partition codes, and Gibbs bounds review (2026-10-31)

Six further owners were source-reviewed; all await locked kernel verification. The RH-interface conclusion is propositional assumption packaging. The order-parameter theorem proves an equivalence for its explicitly defined finite-update-table notion, using an imported realization theorem; the term “Turing complete” here does not prove unbounded computation. The parameter-blind factorization is conditional scalar algebra. The prime-slice owners prove finite divisibility/support and pair-count identities, plus recovery of non-diagonal labels from all partition codes under injective prime encodings. The finite Gibbs owner proves exact factorization and exponential bounds from a uniform positive gap, but no zero-temperature limit. Inventory count: 418; 120 entries since the last successful batch await kernel-build evidence. Coverage remains incomplete.

## Prefix ambiguity, Fourier toy model, and Poisson-labeled algebra review (2026-10-31)

Six additional owners were source-reviewed. The prefix theorem is a valid abstract paired-readout noninjectivity criterion under deep-collision premises. The periodic-amplitude owner proves Parseval-style energy for its stipulated finite amplitude model, not a transform theorem for independently supplied data. The Pisot file proves a defined harmonic profile is nonsummable but does not connect that profile to coefficients of the imported boundary object, so its L² interpretation exceeds the formal bridge. The quartic null-cone statement is elementary real algebra. The M4 decoder solves assumed polynomial identities. The minimal-Laurent-order owner merely returns its nonvanishing assumptions; its order variable is unused. Inventory count: 424; 126 entries since the last successful batch await kernel-build evidence. The preceding six-owner batch is currently in the sequential locked build. Coverage remains incomplete.

## Moment inversion and polynomial-spectrum label review (2026-10-31)

Six more source files were reviewed while the preceding locked build runs. The Poisson moment owners prove real-algebraic inversion from assumed coefficient equations, with no local derivation of those coefficients from probability data. The polynomial mass theorem is valid for `Polynomial ℕ`, but its “spectral radius” is defined to equal evaluation at 1 rather than obtained from an operator spectrum. The power-divergence owner proves recurrence and strict log-convexity for a stipulated positive two-exponential sequence. The prime-adjunction and prime-log conclusions only apply abstract propositional implications. Inventory count: 430; 132 entries since the last successful batch await kernel-build evidence. Coverage remains incomplete.

## Prime-register and support-chain source review (2026-10-31)

Six additional owners were reviewed while the prior build remains active. The modulus-collapse theorem is a valid conditional consequence of a cofinal badness premise and infinitude of primes. `PrimeRegister.lean` is a 1,231-line owner with substantive finite injection/capacity, side-information, Fibonacci bounds, and list Gödel-encoding results; it also contains tautological seeds and relies on explicit coprimality/base hypotheses for encoding claims. The cross-resolution attractor proves the contraction dynamics but assumes layerwise action agreement. The fixed-rank carrier result proves a genuine noninjectivity theorem for a multiplicative-to-additive natural ledger; its “2-adic” carrier is just a function into integers. The K-stretch result is conditional on supplied density criteria. The omega support chain is the elementary range-chain witness. Inventory count: 436; 138 entries since the last successful batch await kernel-build evidence. Coverage remains incomplete.

## Finite partition plateau and primorial proxy review (2026-10-31)

Six more sources were reviewed; all await kernel evidence. The Smith-partition result uses genuine finite multiset identities imported from owner modules. The codimension-one sequence result is conditional on a functional that is stipulated to read one coordinate. The primorial/Gödel owner proves injectivity under pairwise-coprime bases, but its “infinite prime support” package proves only a finite list of prime examples. The axis-dimension owners prove ceiling properties of definitions, not primorial asymptotics; the second-order paper-facing name is only a proposition definition, while a helper proves its model statement. The principal-shadow owner constructs a genuine nonzero finite-coordinate kernel vector, but its Borel/analytic interpretation is unconnected to the model. Inventory count: 442; 144 entries since the last successful batch await kernel-build evidence. Coverage remains incomplete.

## Finite shadow kernels and field/trace scope review (2026-10-31)

Six further owners were source-reviewed. The fixed-depth shadow result is a genuine rank-nullity theorem for a finite real linear map. The coupling inversion is conditional on a supplied cumulative-product law. The “full matrix” file contains only integer arithmetic for dimension 21, not a matrix algebra. The q-local owner gives a valid finite packet collision for its explicitly defined rational host function, without constructing elliptic curves. The quadratic-field owner defines a discriminant-like function and proves divisibility facts, but its headline ledger theorem is excluded middle and no number field/ramification/étale carrier is formalized. The rank-one owner proves a finite-sum cross-term identity under equal secant hypotheses, but no matrix eigenproblem is stated. Inventory count: 448; 150 entries since the last successful batch await kernel-build evidence. Coverage remains incomplete.

## Finite-rank, assumption wrappers, and quartic arithmetic review (2026-10-31)

Six additional owners were source-reviewed while the shared locked build remains queued. The rank-two owner proves invariance of a gcd/lcm-derived audit tuple; the Readus result packages supplied disjunction/contradiction assumptions. The Jordan-tower file aggregates imported results. The Euler-jet owner proves explicit quartic arithmetic and irreducibility claims, without deriving its polynomial from an operator model. The ground-support theorem is a valid detailed-balance contradiction under positive-flow/zero-reverse-flow hypotheses; the half-entropy owner packages assumed witnesses. Inventory count: 454; 156 entries await locked kernel evidence. Coverage remains incomplete.

## Real-input-40 analytic wrappers and finite synchronization review (2026-10-31)

Six more owners were source-reviewed. The open-strip file proves a golden-ratio quadratic factorization and imports a determinant identity, but merely packages assumed holomorphic/no-zero and quotient conditions. The slope-mismatch theorem is a valid abstract contradiction encoded in structure fields. The synchronization wrapper assembles substantive finite reset/minimality claims from imported owners. The typical-ghost result proves non-reproduction in its explicit cyclic-block model. The UV wall is elementary real algebra. The mod-Gaussian-cubic file proves an exact exponential identity for a stipulated cubic polynomial, with no probability law or convergence theorem. Inventory count: 460; 162 entries await locked kernel evidence. Coverage remains incomplete.

## Recursive-soliton wrappers and finite register obstructions review (2026-10-31)

Six further owners were source-reviewed. The primitive-Ramanujan claim is only the elementary fact that r≥3 cannot divide 2. The recursive-solenoid owner contains constant Bool arithmetic and assumed pcdim values, without solenoids or quotient constructions. The register owner proves substantive prefix properties and a sequential-continuity obstruction for its explicit basis encoding. The rejection normal-form theorem ignores its defect and exclusivity premises and returns only the null disjunction; a truthful replacement should use both classification branches and keep exclusivity separate. The relative-homology wrapper proves finite fiber-cardinality consequences from its data/imports, but constructs no homology groups. The relative-zeta result is algebra for a stipulated Laurent model and constant divisor, not analytic pole-order invariance. Inventory count: 466; 168 entries await locked kernel evidence. Coverage remains incomplete.

## Residue algebra, abstract Renyi obstruction, and sequence-envelope review (2026-10-31)

Six additional owners were reviewed. The Renyi2 theorem is abstract modus tollens with no local sequence/model. The one-functional repair is a genuine unique-solution theorem in a vector space. The pressure-drop identity is finite algebra from supplied weights; its m parameter is unused. The single-coordinate rank result imports a concrete Fibonacci cyclic Fourier theorem and proves its specialization. The slice-rigidity result is algebra on stipulated rational slice equations. The resonance-budget theorem proves a valid partial-square-sum domination obstruction, without constructing an L2 space. Inventory count: 472; 174 entries await locked kernel evidence. Coverage remains incomplete.

## Resonance arithmetic, finite budgets, and support-envelope review (2026-10-31)

Six more owners were reviewed. The resonance window file is finite arithmetic only. The infinite-prime package is a valid Euclid argument from abstract Prime/Good predicates and a finite bad set. The reverse-KL exclusivity proof contains a substantive imported real-logarithm argument. The reversible-bit file proves finite injection/cardinality and Nat.clog facts, with no reversible-machine model. The Perron-named theorem is a conditional slope/counting contradiction. The right-edge file proves finite affine-envelope properties, while one packaged clause is definitional reflexivity; no analytic support function is defined. Inventory count: 478; 180 entries await locked kernel evidence. Coverage remains incomplete.

## Strongly-regular arithmetic and screen-rank abstractions review (2026-10-31)

Six further owners were source-reviewed. The S4 parameters file verifies numerical compatibility but constructs no graph. The polarization file proves nonprincipality of a fixed divisor list and imports the carrier theorem. The scale-kernel file has a valid abstract factorization/blindness lemma; its fourth-order package assumes abstract propositions. The meet/additive theorem is a valid coordinatewise natural-number obstruction. The screen atomic-value owner proves useful finite submodular marginal-rank lemmas under explicit assumptions. The Joukowsky-named owner imports a real finite audit lower bound, but its radial map and reconstruction are both identities and its radialProfile input is unused. Inventory count: 484; 186 entries await locked kernel evidence. Coverage remains incomplete.

## Screen-code, finite-dimensional, and topology owner review (2026-10-31)

Six additional owners were reviewed. The constant-weight code result proves finite basis-exchange facts from imported data. The optimal-audit theorem is rank-nullity plus a finite-dimensional complement decomposition for an arbitrary linear map. The finite-localization owner proves a genuine finite-vs-infinite prime-support contradiction, while its topological-dual interpretation is not constructed. The realizability theorem combines an imported cut-space identity with supplied rank/forest equivalences. The zero-one local-law owner mostly republishes its classification hypotheses. The connected-to-discrete theorem is a valid general topology result, with no screenphase-specific object. Inventory count: 490; 192 entries await locked kernel evidence. Coverage remains incomplete.

## Screenphase and sequence-layer claim review (2026-10-31)

Six further owners were reviewed. The prime-singleton screenphase family has a substantive exact-spectrum separation argument, while its quotient interpretation comes from imported owners. The ninefold-field wrapper proves specialization properties and fixed arithmetic but does not state a non-generation conclusion despite its name. The self-dual Mellin theorem merely returns all three assumptions and supplies no consistency witness. The semantic-equivalence theorem is a valid abstract many-one reduction argument. The sequence-layer asymptotic inequality is elementary and contains no periodic model. The fiber-count/minimal-state package defines the fiber count constantly as one and gives no minimality lower bound or bridge from its ambiguity values; this is a concrete semantic counterexample to its docstring. Inventory count: 496; 198 entries await locked kernel evidence. Coverage remains incomplete.

## Serrin frontier wrappers and finite moment witnesses review (2026-10-31)

Six more owners were reviewed. The thermodynamic-frontier owner imports a singleton collapse, but its pressure and purported dual clauses are definitional identities rather than a Legendre-Fenchel theorem. The exact-screen owner does construct a normalized linear functional recovering scale on an imported ray. The Wulff discriminator owner proves a substantive finite moment collision for order one. The positive-anomaly result is direct from its assumed zero-anomaly implications. The volume-normalization owner defines the normalized class as Unit, making the collapse/embedding claims tautological without a normalization map. The Choi-rank formula is a conditional finite fiber-count identity from an imported collision theorem. Inventory count: 502; 204 entries await locked kernel evidence. Coverage remains incomplete.

## Finite rigidity, register blindness, and moment coarsening review (2026-10-31)

Six more owners were reviewed. The cube-edit theorem is a substantive sharp consequence of an imported isoperimetric bound. The Chebotarev-named wrapper gives an explicit first-register collision and imports the group/density facts. The single-Renyi theorem proves a finite fiber-count rigidity result from a q-moment equality. The singular-ring theorem is arithmetic prime/composition equivalence under an imported faithful semigroup law. The size-bias owner gives explicit logical-independence witnesses for abstract predicates. The squarefree-crowding owner is the ordinary finite pigeonhole collision theorem for a declared cardinality gap. Inventory count: 508; 210 entries await locked kernel evidence. Coverage remains incomplete.

## Canonical finite rejection normal form repair (2026-10-31)

Added `lean/Omega/Conclusion/RejectNullFiniteNormalFormCanonical.lean` with reusable statements that preserve both independent classification disjunctions, derive the six-class disjunction from both, and separately prove pairwise exclusivity within the null and defect families. This repairs the source-reviewed scope defect in `RejectNullFiniteNormalForm.lean`. The new owner has not yet received locked kernel verification because the shared build session is still queued. It is not counted as an inventory candidate.

## Stokes certificates, finite sketch collisions, and sync-kernel owners review (2026-10-31)

Six more owners were reviewed. The Stokes certificate is only the contradiction between a strict inequality and a bound encoded as a field, with no Stokes object. The Schur variance result depends on an assumed hook-gap implication; hNonneg is unused. The isotropic certificate result is a finite injectivity/cardinality contradiction via an imported lower bound. The sublinear Toeplitz result is an abstract eventual-order contradiction. The sync finite-length polynomial is rational algebra with uniqueness imposed pointwise. The sync palindrome module includes a genuine finite disagreement-count/uniformity equivalence, alongside seed-only numerical claims. Inventory count: 514; 216 entries await locked kernel evidence. Coverage remains incomplete.

## Tail limits, computability wrappers, and three-end certificates review (2026-10-31)

Six further owners were reviewed. The sync-tail theorem derives a global-limit contradiction solely from supplied implications/nonconstancy. The temperature-halting theorem is a conditional reduction; the defined schedule does not establish its free-energy branch hypotheses. The Omega uncomputability wrapper leaves its affine identity and log nonzero unused and assumes the computability transfer. The tent-kernel wrapper returns its moment identities from structure fields and proves only rational barycenter algebra. The three-end irreducibility theorem refutes Bool-coded verifier flags using assumed missing witnesses. The joint sufficiency/minimality theorem imports factorization fields and assumes the null/hidden-failure classification rather than deriving it from certificate mechanisms. Inventory count: 520; 222 entries await locked kernel evidence. Coverage remains incomplete.

## Three-end certificates, Toeplitz gauge, and toy RH review (2026-10-31)

Six more owners were reviewed. The three-end orthogonality theorem consumes imported conclusions and aggregate proof fields. The time-register criterion depends on supplied fiber and cohomology hypotheses. The Carath-Pick gauge-blindness file contains a genuine explicit kernel-invariance/noninjectivity witness, with the profinite interpretation imported. The negative-geometry file proves a concrete diagonal Gram sign calculation but imports the wider certificate model. The strictification threshold is assembled from imported prefix-rigidity results plus gauge blindness. The ToyRH file proves correct abstract involution/field identities, without constructing a zeta or RH object. Inventory count: 526; 228 entries await locked kernel evidence. Coverage remains incomplete.

## Further defect, lattice, and finite-audit review (2026-10-31)

Six more owners were source-reviewed. The trivial-twist file explicitly defines a four-value coefficient table whose value at 2 violates the claimed half-bound, without constructing the stated twist or jet bridge. The incommensurable-bases theorem proves that a shared positive vertical period forces a rational logarithm ratio. The two-adic first-deviation theorem is a conditional transfer from supplied depth equivalences and undecidability, not a machine encoding. The unbounded-prime-profile result obtains an infinite common kernel from observations that ignore one coordinate, so the infinite conclusion does not encode prime-profile information. The universal finite-audit theorem is a correct abstract contraposition from an assumed implication to P=NP. The visible-circle theorem only transfers a supplied implication between abstract propositions. Inventory count: 532; 234 entries await locked kernel evidence. Coverage remains incomplete.

## Visibility thresholds, Wallis ledger claims, and finite metric owners (2026-10-31)

Six more owners were source-reviewed. The visible dual-scale threshold is valid arithmetic under its named hypotheses, but feasibility and scale are definitional predicates rather than a constructed audit. The strictification rank theorem transports equalities and a supplied no-second-obstruction proposition. The Wallis finite-ledger theorem gives a substantive general noninjectivity result for multiplicative-to-additive maps on ℕ, while its supposed Wallis coverage is just parity decomposition. The product-threshold owner repeats that ledger proof and adds a Boolean first-difference witness, without constructing a CMV/Toeplitz object. The weak-coherence result proves a conditional finite sum bound on edge-length vectors, not on encoded spanning trees. The weighted free-monoid result proves rigidity for its specific ℕ carrier and golden-ratio distance, not a general monoid theorem. Inventory count: 538; 240 entries await locked kernel evidence. Coverage remains incomplete.

## Weighted completion and finite boundary-channel review (2026-10-31)

Six additional owners were source-reviewed. The weighted completion theorem is a sound abstract consequence of assumed pruning/deletion properties, but has no graph construction. The odd-prime staticization theorem uses only divisibility transitivity and A=-A over ℤ; its prime hypotheses are unused. The F8/F9 orthogonality theorem packages an imported finite boundary result and a definitional alias. The faithful connected-detector theorem is only the contradiction 1=components≥4. The anomaly-completeness result derives non-completability from assumed dimensions and implication. The F8 measurability theorem is a genuine counterexample within its explicit Fin 3 × Bool model, where one readout is constant and parity reads the Bool coordinate; it does not establish the external boundary interpretation. Inventory count: 544; 246 entries await locked kernel evidence. Coverage remains incomplete.

## Boundary invariance, finite-field rigidity, and endpoint claims (2026-10-31)

Six more owners were source-reviewed. The no-equivariant-projector theorem is a valid invariant-image contradiction from a supplied moved-boundary witness; its idempotence hypothesis and any concrete action are unused. The Z6 extension result contradicts an orbit-count equation included in its extension predicate, relying on an imported mismatch. The center theorem proves a substantive (F₂)^8 invariant-subspace dichotomy under closure by every linear endomorphism, stronger than GL8 invariance; it does not instantiate a window-6 center. The choice-free parity theorem classifies three supplied finite tables. The cyclic escort theorem proves limits for explicit scalar sequences without defining the named shell/operator. The endpoint-atom theorem correctly shows exponent-two groups have no nonzero real additive homomorphisms; its imported boundary/anomaly facts are cleared and unused. Inventory count: 550; 252 entries await locked kernel evidence. Coverage remains incomplete.

## Window-6 scale gates, local/global packages, and tensor claims (2026-10-31)

Six further owners were source-reviewed. The first-scale gate is finite computation on a locally defined three-case size function. The inversion/statistical theorem only conjoins imported results. The local-Morita package refutes constant orbit/coset size from supplied 2/3/4 counts, while contractibility and matrix-block clauses are structure fields, not constructions. The long/short-root theorem is finite lookup from twelve assumed values with no root-system action. The low-order tensor result proves the imported dimension-21 divisibility obstruction, without constructing invariant tensors or equivariant maps. The Markov/topological channel theorem is a Fin 2 model of two distinct constant functions, with no chain or topology. Inventory count: 556; 258 entries await locked kernel evidence. Coverage remains incomplete.

## Finite Weyl tables, moment ranks, and abstract obstruction wrappers (2026-10-31)

Six more owners were source-reviewed. The maximal-degree Weyl-breaking file proves a finite subset/orbit-block mismatch on coordinate intervals, with no group action. The exact-replay theorem is propositional contraposition from supplied implications. The moment-tower owner proves explicit rational exponential sums, recurrences, and exact Hankel ranks by a reusable imported theorem. The inverse-limit parity-lift theorem assumes its obstruction as a predicate implication and constructs no inverse system. The no-linear-factorization owner forwards an imported theorem. The root-system/no-free-quotient result uses an Even cardinality predicate plus imported orbit obstructions; it does not construct or map a root system. Inventory count: 562; 264 entries await locked kernel evidence. Coverage remains incomplete.

## Affine predicate tables, finite projectors, and moment inversion (2026-10-31)

Six additional owners were source-reviewed. The odd-prime affine/local/coarse theorem returns supplied predicate classifications and checks two memberships. The one-axis screen theorem rewrites supplied values 32/64/12. The Reynolds-named owner contains a genuine finite partition model: rational fiberwise averages project onto fiber-constant functions, preserve the weighted norm formula, and equal the given polynomial operator; it does not construct a group Reynolds action. The short-root owner proves a genuine explicit 6×6 integer matrix has nonzero square and zero cube, conditional on its displayed entries. The three-moment theorem gives exact inversion and congruence criteria for a finite histogram. The topological-closure owner only conjoins imported cardinality/orbit facts and a boundary witness. Inventory count: 568; 270 entries await locked kernel evidence. Coverage remains incomplete.

## ZG finite-shadow, Markov, and correlation claims (2026-10-31)

Six more owners were source-reviewed. The nonstationary Markov result assumes transition decay in exactly the form used to refute stationarity. The finite-prefix blindness and no-local-dimension-predicate theorems derive valid abstract counterexamples from a realization field that already permits every dimension at each certificate/shadow pair; no concrete ZG process is built. The completeness/factorization theorem combines two imported results. The positive-entropy obstruction is generic implication contradiction from supplied measure hypotheses. The prime-pair correlation theorem is valid rational algebra conditional on divisor equalities, positivity, and hard-core zero pair mass; prime status and the source divisor law are not established there. Inventory count: 574; 276 entries await locked kernel evidence. Coverage remains incomplete.

## Final ZG correlation, finite test, and audit-spectrum review (2026-10-31)

The final three owners in the current candidate snapshot were source-reviewed. The nearest-neighbor nonmultiplicativity result is conditional rational algebra from supplied scaling equations and a zero pair term. The zero-mean residue theorem proves a genuine finite coordinate-detection result using basis probes on complex vectors. The zeta audit/synchronization theorem is an abstract indistinguishability argument whose structure fields already impose equal spectral data and distinct budgets at levels 3 and 4; no zeta object is instantiated. Inventory count: 577; 279 entries await locked kernel evidence. The source snapshot has no remaining unreviewed candidates, but this is not yet a complete repository-wide audit or kernel verification of the pending set.

## Locked-build verification update (2026-10-31)

The previously queued six-module locked Lake build completed successfully (3099 jobs). Those six inventory records are now marked kernel-verified, reducing the pending count to 273. The new `RejectNullFiniteNormalFormCanonical.lean` repair was given the repository-required copyright header and is verified below.

The canonical finite normal-form repair subsequently built successfully with `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock Omega.Conclusion.RejectNullFiniteNormalFormCanonical`. Its proof statements were tightened to remove unused classification assumptions and unused exclusivity hypotheses. The six-module build and this repair build are verified; the remaining inventory candidates are still pending.

A further six-owner locked build completed successfully (8941 jobs): the trivial-twist, incommensurable-bases, two-adic first-deviation, unbounded-prime-profile, universal finite-audit, and visible-circle owners. Their inventory statuses now record kernel verification; 267 candidates remain pending.

The next six-owner locked build also completed successfully (8950 jobs): the three-end certificate, time-register criterion, Toeplitz gauge blindness, negative-geometry split, strictification threshold, and ToyRH sign-center owners. Their statuses are verified; 261 candidates remain pending.

Added `FiniteObservationCollisionObstruction.lean` with general decoder-fiber lemmas, including a valid-domain version and paired observations. Refactored the finite-prefix shadow blindness proof to use this canonical obstruction. These changes are staged and await locked kernel verification; the shared build lane remains occupied by the Curtis–Tits target.

Inventory-status count clarification: 270 of 577 records have a status containing `kernel_verified`, 261 are `source_reviewed_pending_locked_build`, and 46 have other review statuses. A progress update counted only the exact status string `source_reviewed_and_kernel_verified` and reported 18; that was not the total kernel-verified count.

## Expanded tracked-source discovery and decoder-fiber verification (2026-10-31)

The repository's lexical inventory tool was run in tracked mode over the current checkout. It scanned 28,770 Lean files and emitted 13,329 declaration candidates (11,413 named declarations), with zero read errors and seven skipped paths. Of the candidates, 12,368 are classified by the tool as repo-owned, 959 require other-surface review, and two fall in runtime/generated surfaces. This is a substantially broader candidate surface than the curated 577-owner snapshot, but remains lexical navigation evidence: its own limitations include false positives, missed indirect counterexamples, and parser omissions. A matching-name comparison found only 160 of those declarations among the 1,273 names already listed as reviewed replacements, so the curated snapshot cannot be treated as exhaustive coverage of every lexical lead. High-density unmatched files now form a prioritized source-review queue; counts alone do not classify their theorems as counterexamples.

The six-owner build acquired the lock and passed (3,106 jobs), reducing the pending set to 255. The canonical decoder-observation obstruction and its finite-prefix shadow consumer then both built successfully (8,925 jobs). The consumer record and replacement link now cite that kernel evidence. Current curated inventory counts: 277 records with a status containing `kernel_verified`, 254 awaiting locked builds, and 46 with other statuses. The three explicit counterexample modules checked during expanded discovery—`CornerCompressionTraceCounterexample`, `PeirceTangentCounterexample`, and `CharacteristicTwoOverlapCounterexample`—were already present in the curated snapshot with replacement/kernel evidence; their alternatives are the commutator criterion for compression cyclicity, the characteristic-free tangent characterization with its characteristic-two boundary, and the symmetric-support overlap decomposition, respectively.

Initial source triage of the largest unmatched repo-owned lexical clusters is in progress: `Canonical/ConformalAnomalySource.lean` (47 candidate declarations), `Analysis/AsanoContractionNative.lean` (41), and `Topology/MobiusGeometry.lean` (40). Their opening sections were inspected, but full declaration/dependency review remains outstanding; these counts are prioritization signals only.

The explicit owner-name cross-check found two files missed by the 577-file curated inventory: `lean/SelfReference/Counterexamples.lean` and `lean/Omega/Zeta/XiTimePart60abOddModesRecurrenceCounterexample.lean`. Both are now registered as source-reviewed, build-pending records. The SelfReference witnesses are supported by general constructors in `Core.lean` and `Memory.lean`: every `Agent` admits identity-based faithful reflection and lawful state-backed memory, while neither construction asserts operational introspection or persistence across arbitrary transitions. The Xi witness uses the constant-one sequence, a genuine order-one `LinearRecurrence` solution whose odd coefficients never vanish; it refutes eventual odd-mode vanishing as a characterization of ordinary C-finite sequences. Current curated inventory size is 579; 256 records await locked builds, 277 have kernel-marked statuses, and 46 have other statuses.

Both newly registered owners passed the serialized locked build (3,097 jobs). Their records and replacement links now include the verified source hashes and build evidence. Updated counts: 279 kernel-marked, 254 awaiting locked builds, and 46 other statuses, out of 579 records.

The following six pending owners then passed a locked build (8,930 jobs): `EssentialPrimeAxisMinimality`, `FibadicDepthPacketSlopeAtOne`, `FibadicFiniteLayerDominantDepthSelection`, `FibadicFiniteLayerGcdKernelImageSpectrumClosedform`, `FibadicGcdConvolutionDiagonalization`, and `FibadicGoldenExtensionNoIntrinsicQ5Realization`. Their inventory records carry the command and result. Updated counts: 285 kernel-marked, 248 awaiting locked builds, and 46 other statuses, out of 579 records.

A repeatable filename cross-check over `lean/` found 46 modules whose paths contain `counterexample`, `obstructionaudit`, or `obstructionbridge`; all 46 now have records in the 579-file inventory. This closes only the named-owner surface for those three filename patterns. It does not close the broader declaration-level lexical surface or establish that all counterexamples use those names.

The six next pending owners built successfully under the lock (3,145 jobs): `FibadicNaturalDepthChainObstruction`, `FibadicUndecidabilityNotFromFiniteDepthOrFinitePackage`, `FiberHologramIntegralityGlobalWalshConservation`, `FiniteAuditDimensionPhaseTransition`, `FiniteDefectRankVsMacroscopicToeplitzAuditScaleSplitting`, and `FinitePrecisionHolographyTripleIncompatibility`. The output included existing lint and deprecation warnings but exited successfully. Their inventory records now carry kernel evidence. Updated counts: 291 kernel-marked, 242 awaiting locked builds, and 46 other statuses, out of 579 records.

## Continued pending-owner audit (2026-10-31)

While the serialized Curtis–Tits build session remained live, six subsequent pending owners were inspected directly. `StokesExtensionObstructionCertificate` is a strict-versus-weak inequality contradiction with the claimed realizability bound stored as a field, not derived from a Stokes construction. `StrictGapForcesNonhookSchurVariance` combines an imported finite Schur variance decomposition with an explicit hypothesis that a nonzero hook channel forces zero gap; its `hNonneg` premise is unused in this wrapper. `SubcriticalIsotropicMomentCertificatesIncompleteAcrossResolutions` is a finite cardinality collision result using the imported incompressibility lower bound, with arbitrary maps standing in for the named moment sketch and postprocessing. `SublinearToeplitzAuditImpossible` is a valid eventual-inequality contradiction from three supplied asymptotic hypotheses, without a Toeplitz construction. `SyncKernelFiniteLengthSingleCoordinate` proves a concrete rational polynomial identity for `1 + u + u²` and a uniquely specified function, not a general sync-kernel classification. `SyncKernelPalindrome` includes finite matrix entry checks and several literal arithmetic seeds; its tower-uniformity theorem later in the file is a substantive finite combinatorial statement about fiber sizes. These are source-level classifications only; none gains new kernel evidence from this inspection.

The queued six-owner build then acquired the serialized build lock and completed successfully (3,106 jobs): `SyncTailResidueClassLimitLaw`, `TemperatureKernelFreeEnergyHaltingEmbedding`, `TemperatureKernelFreeEnergyOmegaUncomputable`, `TentKernelLocalInvertibility`, `ThreeEndCertificateIrreducibility`, and `ThreeEndCertificateJointSufficiencyMinimality`. Their inventory records now include the exact locked-build command and result. Pending locked-build records decreased from 261 to 255.

The next six reviewed owners also passed the locked build (3,214 jobs): `FinitePrimitiveSurgeryPoleFinitepartTransform`, `FiniteRankAdditiveLedgerPowerTowerCollision`, `FiniteRankAdditiveShadowObstruction`, `FiniteSliceStrictificationUniqueObstructionClass`, `FiniteSpectralMomentFingerprintNotComplete`, and `FiniteStateGateFragmentDecidableOrderGateRole`. Existing deprecation warnings were emitted; the build exited successfully. Their records now carry kernel evidence. Updated inventory counts: 297 kernel-marked, 236 awaiting locked builds, and 46 other statuses, out of 579 records. The wider lexical scan still exceeds the curated inventory, so repository-wide semantic closure is not established.

The following six owners passed the next serialized build (8,953 jobs): `FiniteStateSelectorCannotSustainKernelRh`, `FiniteTestDepthBusybeaver`, `FiniteVerificationClosureComplexityTrilemma`, `FixedResolutionCollisionRationalHankelRank`, `FixedResolutionHolographyDoubleObstructionSynthesis`, and `FixedResolutionLinearVsNonlinearHolographyStrictBifurcation`. The build emitted existing linter/deprecation warnings and exited successfully. Their records now include the exact command and result. Updated counts: 303 kernel-marked, 230 awaiting locked builds, and 46 other statuses, out of 579. Source review indicates several titles overstate their actual scope: the finite-state selector result is a conditional bound argument, the Busy Beaver owner encodes the halting-time equality in its data, the complexity “trilemma” packages imported implications, and the double-obstruction synthesis composes imported results. Kernel success verifies these formal statements, not broader interpretations.

The next six owners passed the locked build (3,121 jobs): `FixedResolutionNoThermalSingularity`, `FixedResolutionPrimeBarrierPostprocessingNeutrality`, `FixedscalePowerSumSharpThresholdMaxfiber`, `FoldCondexpQuantumOperationNoninvertible`, `FoldFiberFaceposetSquarefreeDivisibilityShadow`, and `FoldFiberHologramBooleanCubePartition`. The output contained existing lint and deprecation warnings; the build exited successfully. The inventory now records the command and result for each. Updated counts: 309 kernel-marked, 224 awaiting locked builds, and 46 other statuses, out of 579. In source scope, the fixed-resolution histogram theorem includes a concrete pair colliding on the first two moments and recovery from the first three; the fold-fiber partition statement is a general-function fiber partition identity, while fold noninvertibility requires a collision supplied as data.

Six more pending owners passed a serialized build (3,190 jobs): `FoldGoldenResonanceMaxfiberLift`, `FoldNormalizerIndexTwoQuotients`, `FoldPartitionGlobalWalshBalance`, `FoldQuantumProjectiveSimplexQuotient`, `FoldSinglepairVisibleObstructions`, and `FoldSymtftPartitionFunctionSectorization`. Existing linter/deprecation warnings did not affect the successful result. Their inventory entries now include build evidence. Counts: 315 kernel-marked, 218 awaiting locked builds, and 46 other statuses, out of 579. The previously recorded Fact/Logic audit remains the relevant correction for the user's A86 paste: the published mask support permits prompt-to-fact blocks, while the restricted `fullOperator` model does not; neither algebraic model establishes neural semantics or factual losslessness.

The next six pending owners were re-reviewed directly: `FoldWalshGramSimplexSignatureSection` proves finite Walsh orthogonality and fiber energy identities; `FoldZeroDivisorLatticeInvolution` and its witness module use a definitional zero-set union plus imported spectrum/coset facts, with a separate Bool flip attached as witness; `FoldbinActiveFourierModesDiverge` proves a finite support-cardinality bound from assumed energy and coefficient bounds (not divergence over growing dimensions); `FoldbinFibonacciUpperEnvelopeFiniteContact` simply returns its finite-contact premise; and `FoldbinGroupoidPIDegreeThreshold` derives a threshold from its assumed characterization. Their source-review notes were corrected in the inventory. Kernel replay is still pending: an unrelated `InfoGeometry.Exceptional.CFSGPort.All` build currently occupies the shared lane.

## Asano nondegenerate endpoint counterexample (2026-10-31)

Added `Analysis/AsanoNondegenerateEndpointNecessaryCounterexample.lean` as a
concrete counterexample to dropping the endpoint hypothesis from the
nondegenerate Asano branch. Set `K₁ = ℂ \ {0}`, `K₂ = ∅`, and
`p(z₁,z₂) = 1 + z₁ z₂`. The polynomial is zero-free whenever
`z₁ ∉ K₁` and `z₂ ∉ K₂`, while `D = 1`, `AD - BC = 1`, and the contraction
`1 + z` vanishes at `z = -1`, which is outside the empty signed-product set.
The endpoint disjunction fails because `B = C = 0`. The canonical positive
replacement is the existing endpoint-conditioned localization theorem
`contracted_zero_mem_signedProduct_of_nonDegenerate_endpoint` in
`Analysis/AsanoContractionNative.lean`. The counterexample file is registered
in the curated inventory; its locked kernel build remains pending because the
shared lock is held by the external CFSG build.

A fresh tracked-source lexical scan after adding the witness covered 28,771
Lean files, emitted 13,333 declaration candidates, reported zero read errors,
and listed seven skipped paths. The leading clusters remain
`ConformalAnomalySource` (48), `AsanoContractionNative` (41), and
`MobiusGeometry` (40), followed by `KingdonSplitOctonion` (33). These counts
prioritize review; they are not semantic classifications. The curated ledger
now contains 580 files: 315 kernel-marked, 219 build-pending, and 46 other
statuses.

## Fact/Logic decoder mask matrix witness (2026-10-31)

Added `Routing/FactLogicBypassMatrixCounterexample.lean`, instantiating the published three-track support formula on `Matrix (Fin 3) (Fin 3) ℂ`. Matrix units at `(2,0)`, `(1,1)`, and `(0,0)` witness a nonzero prompt-to-fact block. This refutes the pasted A86 claim that this block is necessarily zero under the published support assumptions. It does not model the additive attention mask or establish neural performance or semantics. The owner theorem `publishedMaskSupport_prompt_fact_block` is the general support identity; the concrete matrix witness passed its locked build (1,203 jobs). The related Asano nondegenerate endpoint witness also passed its locked build (3,102 jobs); both ledger entries now carry build evidence.

## Finite-contact implication countermodel (2026-10-31)

The source theorem `FoldbinFibonacciUpperEnvelopeFiniteContact.lean` includes eventual strict separation as the premise `hfinite_contact` and returns it unchanged. Added `FoldbinFibonacciUpperEnvelopeFiniteContactCounterexample.lean`: equal zero sequences on the theorem's actual `ℕ → ℕ` carrier satisfy the pointwise upper bound but are equal for all indices, so the other premises do not imply finite contact. This is a countermodel to removing that premise, not a refutation of the conditional theorem. The locked build passed (136 jobs); the vacuity linter reported no findings and the axiom index found zero axioms. The replacement statement records the exact conditional boundary.

## Finite monotone-gate expressivity witness (2026-10-31)

`FreeEnergyGatesMonotonicityObstruction.lean` provides a genuine finite result: every gate generated from real coordinates, constants, addition, and `max` is monotone on the Boolean cube after threshold compilation. Its explicit witnesses show that one-bit NOT and two-bit odd parity are not monotone, hence cannot be compiled in this grammar. The locked build passed (3,093 jobs) with an existing `Mathlib.Data.Real.Basic` deprecation warning. This is a scoped finite expressivity theorem, not a claim about unrestricted neural or free-energy models; the inventory now records its kernel evidence.

## Peirce homogenized-channel noninjectivity revalidation (2026-10-31)

The current `PeirceSpine/Homogenized.lean` definitions and their kernel-checked canonical alternatives are grounded in `HomogenizedKernels.lean`: all four channels fail injectivity on any nontrivial ring (the `V` channel under an idempotent hypothesis), while A15 orthogonality is generator-restricted. Repository search found these declarations in the corresponding owner/audit surfaces. The locked `HomogenizedKernelsAudit` build passed (616 jobs); its axiom readback reported only standard foundations. The inventory source hash now matches the revalidated owner.

## Dikin derivative counterexample source revalidation (2026-10-31)

The current Dikin owner and derivative audit were rebuilt after detecting a stale inventory source hash. `DikinBarrierDerivativeBridgeAudit` passed (8,981 jobs) and read back the transformed-barrier self-concordance counterexample alongside the derivative and exact bound-criterion declarations. Existing deprecation/linter warnings remain. The ledger hash was refreshed only after this build.

## Self-dual Mellin periodicity countermodel (2026-10-31)

The source theorem assumes its nonperiodicity conclusion and returns it unchanged alongside two other premises. Added `SelfdualScaleMellinPeriodicityCounterexample.lean`: the zero function `X : ℂ → ℂ` satisfies `X s = X (1-s)`, takes real values on the designated critical-line points, and has nonzero vertical period `T=1`. Thus the first two properties do not imply the third. The locked build passed (814 jobs; an existing Complex import deprecation warning); vacuity scan was clean and the axiom audit found only standard foundational axioms. The original source is now classified as an assumption-repackaging wrapper, and the countermodel is recorded as the canonical scope correction.

## Scale-kernel observation-factorization result revalidation (2026-10-31)

The current `ScaleKernelTreeThirdOrderBlindness` source proves a conditional extensionality result: if a protocol factors through an observation map and two objects have equal observations, their outputs agree, contradicting any supplied faithful separator. Its separate fourth-order package assumes the proposition and implication hypotheses it returns. The owner build passed (3,092 jobs), and the inventory hash and scope status were refreshed. This verifies the conditional formal statements, not a concrete scale-kernel tree or cumulant construction.

## Fold zero-mode involution scope counterexample (2026-10-31)

The `FoldZeroDivisorLatticeInvolution` package attaches a fixed-point-free `Bool` flip to each zero-mode witness, but that flip has no action on the zero-mode index. At `m=0`, the actual owner definition gives an empty spectrum because its index set is `Finset.range 0`, while the separate Bool flip remains an involution. Added `FoldZeroDivisorLatticeInvolutionScopeCounterexample.lean` to establish this precise scope boundary. The locked build passed (3,096 jobs, including both source modules); vacuity check was clean and only standard foundational axioms were present. The canonical correction is to keep the Bool fact separate unless a mode-to-action map is defined and proved.

## Frozen-phase localization countermodel (2026-10-31)

Added `FrozenPhaseLocalizationCounterexample.lean`. The real parameter choice `alphaStar=0`, `alpha2=-1`, `aC=0`, `a=1`, `betaInv=1`, with a piecewise function `hTheta`, satisfies both inequality premises but violates the collapse identity and the beta equation. The source theorem assumes those equations as premises and never uses `h_frozen`; it is therefore conditional assumption transport, not a derivation from the inequalities. The locked build passed (1,960 jobs), the vacuity scan was clean, and the axiom audit found only standard foundations. The inventory records the countermodel and conditional replacement.

## Hydrogenic pair-collapse hypothesis minimization (2026-10-31)

Strengthened `HydrogenicPhaseblindPairCollapse.lean`: the conclusion now holds for every integer `m`; the previous `m ≠ 0` hypothesis was unused. The proof still assumes the state-pair equation and phase/conjugation invariances, and the class-count formula remains an input rather than a derived result. Repository search found no dependents of the theorem. Its locked build passed (3,092 jobs), and the inventory records the current source hash and conditional boundary.

## Finite-support Fourier-mode bound scope counterexample (2026-10-31)

The owner `FoldbinActiveFourierModesDiverge.lean` proves only a per-carrier support lower bound from an assumed coefficient-square sum and `0 ≤ a ≤ 1`; it does not establish divergence over a family of dimensions. Added `FoldbinActiveFourierModesBoundedSupportCounterexample.lean`: on every carrier `Fin (n+2)`, exactly one nonzero nonzero-mode coefficient has square-sum equal to the normalized excess in the owner's hypothesis. The support therefore remains one as carrier sizes grow, showing that the finite bound alone does not force support growth. The locked build passed (3,093 jobs). Axiom readback found only standard foundations; the heuristic vacuity scan reported `simp`/`omega` usages, reviewed as constructive parts of the finite witness. The inventory now has 586 records: 328 kernel-marked, 210 build-pending, and 48 other statuses.

## Finite-contact assumption boundary revalidation (2026-10-31)

Rebuilt `FoldbinFibonacciUpperEnvelopeFiniteContactCounterexample.lean` against its source owner. The theorem's eventual strict-separation proposition is explicitly an input and returned unchanged; the zero-sequence countermodel proves that the remaining abstract premises do not imply it. The locked build passed (136 jobs), the vacuity scan was clean, and the axiom index found no axioms. Updated the source-owner inventory status from build-pending to kernel-verified conditional scope. The inventory now has 586 records: 329 kernel-marked, 209 build-pending, and 48 other statuses.

## PI-degree threshold conditional theorem verification (2026-10-31)

`FoldbinGroupoidPIDegreeThreshold.lean` derives attainment at `D` and exclusion below `D` from the explicit premises `PIdeg = D` and `satisfiesStandard r ↔ D ≤ r`. The Lean statement is valid and adds no counterexample; its title's groupoid/PI-degree context is not constructed in this file. The locked build passed (3,092 jobs). Reclassified it as a kernel-verified conditional order-theoretic result. The inventory now has 586 records: 330 kernel-marked, 208 build-pending, and 48 other statuses.

## Four conclusion-owner scope checks (2026-10-31)

One locked build (3,158 jobs) verified four more pending owners. `FoldbinS2MinimalLinearComplexityThree` is a concrete recurrence/minimal-order result for the defined `momentSum 2` sequence using an imported recurrence; `FoldbinS3MinimalLinearComplexityThree` is conditional on its supplied rational recurrence; `GlobalMixedHiddenStateNoFaithfulFiniteAbelianObservation` is simply infinite-to-finite noninjectivity for an arbitrary function; and `HankelArithmeticTomographyFiniteBadPrimesCompletion` composes four imported theorems under explicit premises. The broader names do not add hidden-state dynamics or tomography constructions. Their ledger entries now state these scopes and include the shared build evidence. The inventory now has 586 records: 334 kernel-marked, 204 build-pending, and 48 other statuses.

## Golden-resonance trace ℓ² counterexample (2026-10-31)

Added `GoldenResonanceIntegerTraceSquareSummableCounterexample.lean`. For the source's exact trace `n ↦ 1/(Int.natAbs n + 1)`, the squared coefficient sequence is summable over `ℤ`, by the exponent-two p-series on its positive and negative tails. The module also constructs a coefficient model equal to that trace and proves its zero mode is one. Thus the source's “logarithmic divergence” predicate (pointwise positivity) is not divergence, while its no-realization claim follows from the contradictory extra requirement that this nonzero zero mode vanish. The locked build passed (3,123 jobs), the vacuity scan was clean, and the axiom index found only standard foundations. Scope is sequence-level ℓ² summability; no periodic function or Parseval theorem is asserted. The inventory now has 587 records: 336 kernel-marked, 203 build-pending, and 48 other statuses.

## Finite Walsh Gram and fiber-energy owner verification (2026-10-31)

The pending `FoldWalshGramSimplexSignatureSection.lean` owner passed its locked build (3,103 jobs). Its verified scope is finite Boolean-word Walsh character orthogonality, the exact Gram identity after removing the empty character, and an average-energy lower bound attained by some nonempty mode on each nontrivial finite fiber. It adds no counterexample; the result is not a general decoder or information-retention theorem. At that point the inventory had 587 records, with 337 kernel-marked, 202 build-pending, and 48 other statuses.

## Borwein local analytic obstruction scope audit (2026-10-31)

`FoldgaugePiBorweinLocalAnalyticObstruction.lean` passed its locked build (3,137 jobs). The theorem only refutes a `formalConjugacy` proposition defined as an implication to positive radius, by applying the imported zero-radius predicate. That imported result assumes a coefficient formula and uniform lower-growth bound in its data structure; this owner constructs no analytic germ, local ring, or conjugacy map. Classified as assumption repackaging, not an analytic obstruction or counterexample. The inventory now has 587 records: 338 kernel-marked, 201 build-pending, and 48 other statuses.

## Even-zeta first-difference remainder cancellation (2026-10-31)

Added `FoldgaugePiEvenzetaRemainderCancellationCounterexample.lean`. Its kernel-checked example has a nonzero coefficient difference at the first retained order (`r = 1`), while choosing the unrestricted remainder difference to cancel the finite-sum term makes the two expanded sequences equal for every truncation parameter. The source's exact difference identity remains correct; only the informal reading as a first nonzero total difference is unsupported absent an asymptotic remainder-dominance condition. The locked build passed (3,096 jobs). Inventory count: 587 candidates, 339 kernel-marked, 200 build-pending, and 48 other statuses.

## Fold-π sufficient-statistic finite-fiber bound (2026-10-31)

`FoldgaugePiSufficientStatisticFiberObstruction.lean` passed its locked build (3,670 jobs). Its finite pigeonhole argument is valid: for the explicitly defined fiber and degree, a residual into `Fin (d + 1)` cannot be injective when the fiber is larger, and deterministic decoding success is bounded by `(d + 1) / fiber-cardinality`. The single-path Fibonacci upper bound tends to zero. The fiber cardinality and degree are defined by Fibonacci and ceiling formulas in this owner; the file does not independently construct a fold map or empirical decoder. Reclassified as a verified finite-model result, not a counterexample. Inventory count: 587 candidates, 340 kernel-marked, 199 build-pending, and 48 other statuses.

## Fold-π rank-two four-moment rigidity (2026-10-31)

`FoldpiRanktwoFourMomentRigidity.lean` passed its locked build (3,092 jobs). Under the explicit assumptions that both real sequences satisfy order-two recurrences, agreement at indices 1–4 and a nonzero Hankel determinant identify the comparison recurrence coefficients; induction then proves equality at every index from 1 onward. This is a valid conditional sequence theorem, not a result for arbitrary sequences without recurrence hypotheses. No counterexample was found to the stated implication. Inventory count: 587 candidates, 341 kernel-marked, 198 build-pending, and 48 other statuses.

## Free-energy interval non-approximability scope audit (2026-10-31)

`FreeEnergyMonotoneHaltingFormulaNonapproximable.lean` passed its locked build (3,092 jobs). The abstract reduction is valid: if a supplied real-valued map takes exactly two separated values according to an undecidable predicate, a uniformly narrow rational interval enclosure decides that predicate. The owner provides no concrete encoding of halting programs into the map. Classified as a verified conditional obstruction with scope limits, not as a constructed computability result. Inventory count: 587 candidates, 342 kernel-marked, 197 build-pending, and 48 other statuses.

## Full-residue regular-simplex finite-coordinate identities (2026-10-31)

`FullResidueRegularSimplexOrbit.lean` passed its locked build (3,092 jobs). It verifies the standard finite rational model: centered coordinate vectors in `Fin m` have Gram entries `δᵣₛ - 1/m`, squared norms `(m - 1)/m`, and pairwise squared distance `2` for distinct indices. The proof is valid for `m > 0`; its scope is the explicit coordinate model, without a general orbit or representation theorem. No counterexample was found. Inventory count: 587 candidates, 343 kernel-marked, 196 build-pending, and 48 other statuses.

## Gauge-anomaly no-three-mode emulator claim scope audit (2026-10-31)

`GaugeAnomalyNoThreeModeEmulator.lean` passed its locked build (3,092 jobs). Its theorem directly contraposes the supplied premise that passing both predicates forces `carrierDim ≥ 4`. The owner defines no gauge-anomaly data, certificate semantics, or emulator model, so this is a verified logical wrapper rather than a constructed dimension obstruction. Inventory count: 587 candidates, 344 kernel-marked, 195 build-pending, and 48 other statuses.

## Gauge-anomaly normalized ratio limit canonicalization (2026-10-31)

`GaugeAnomalySuperpoissonFano.lean` passed its locked build (3,092 jobs). The normalized mean and variance limits imply the variance-to-mean ratio limit, while the owner separately assumes eventual nonvanishing of the mean. Added `GaugeAnomalySuperpoissonCanonical.lean`, proving that this premise follows from convergence of the normalized mean to `4/9` (and eventual positivity of `m`), then reusing the original theorem. The two limit hypotheses alone therefore suffice. This is a canonical strengthening of a valid real-sequence theorem; the source's Fano/super-Poisson interpretation is not represented. The new module passed its locked build (3,093 jobs). Inventory count: 587 candidates, 345 kernel-marked, 194 build-pending, and 48 other statuses.

## Global-clock vanishing assumption audit (2026-10-31)

`GlobalClockVanishing.lean` passed its locked build (3,092 jobs). The conclusion is exactly the contradiction between a nonzero obstruction integer and the structure field asserting that any shared local integer clock forces that integer to vanish. No Čech complex or cohomology class is built. Classified as assumption repackaging, not a cohomological obstruction theorem. Inventory count: 587 candidates, 346 kernel-marked, 193 build-pending, and 48 other statuses.

## Global-null cohomological remainder scope audit (2026-10-31)

`GlobalNullPureCohomologicalRemainder.lean` passed its locked build (3,092 jobs). Its conclusion is classical contraposition of an assumed equivalence between readability and absence of the named obstruction, conditional on local exhaustion. No cohomology carrier, differential, or obstruction class is constructed. Classified as propositional assumption repackaging. Inventory count: 587 candidates, 347 kernel-marked, 192 build-pending, and 48 other statuses.

## Global terminal-spectrum compatibility tautology audit (2026-10-31)

`GlobalTerminalStateForcesGlobalPrimitiveSpectrum.lean` passed its locked build (149 jobs). Its `compatibleGlobalTerminalState` predicate already includes local-to-global spectrum equality and vanishing of both integer obstruction fields. The theorem projects equality and contradicts either nonzero obstruction against the corresponding zero conjunct. Classified as definition-level assumption repackaging; no spectrum or gluing construction is present. Inventory count: 587 candidates, 348 kernel-marked, 191 build-pending, and 48 other statuses.

## Gödel–Leyang IFS theorem-name scope audit (2026-10-31)

`GodelLeyangIFS.lean` passed its locked build (3,092 jobs). Its declarations prove elementary base-2/base-5 arithmetic and logarithm identities; one package declaration is an alias of the seed theorem. The names about IFS dimension, Haar measure, and digit rigidity exceed the statements: no IFS, measure, Hausdorff dimension, or rigidity condition is formalized. Classified as verified scope limits. Inventory count: 587 candidates, 349 kernel-marked, 190 build-pending, and 48 other statuses.

## Gödel–Leyang resolution-tower circle-law scope audit (2026-10-31)

`GodelLeyangResolutionTowerCircleLaw.lean` passed its locked build (3,092 jobs). The only substantive result is the standard fact that a complex root of unity has norm one. The primitive-root exclusion and lower bound on `M` are unused, and tower degree/count equalities are reflexive unfoldings of definitions. No resolution-tower or primitive-root counting theorem is present. Classified as verified scope limits. Inventory count: 587 candidates, 350 kernel-marked, 189 build-pending, and 48 other statuses.

## Gödel prefix arithmetic criterion verification (2026-10-31)

`GodelPrefixArithmeticCriterion.lean` passed its locked build (3,129 jobs). The statement is a valid conditional list-prefix criterion: the imported injectivity theorem for equal-length prime-product encodings recovers the prefix, and `take_append_drop` supplies the extension. Classified as a verified sequence implication, not a counterexample. Inventory count: 587 candidates, 351 kernel-marked, 188 build-pending, and 48 other statuses.

### Halting-time budget exactness verification (2026-10-31)

`Omega.Conclusion.paper_conclusion_halting_time_external_budget_exact` in
`lean/Omega/Conclusion/HaltingTimeExternalBudgetExact.lean` kernel-builds
successfully (locked `lake build Omega.Conclusion.HaltingTimeExternalBudgetExact`,
3092 jobs). The candidate is a tautological data projection: both budget
formulas are fields of `HaltingTimeExternalBudgetExactData`, and the theorem
returns those fields unchanged. It contains no halting-time construction or
external-budget analysis. Marked as kernel-verified tautological packaging, not
as a substantive counterexample theorem. The inventory had 188 candidates
pending locked builds before this verification.

### Alternating-constant convergence inference (2026-10-31)

`Omega.Conclusion.GoldenAlternatingConstantsRecoverPhi` kernel-builds
successfully (locked build, 3092 jobs). Its affine identities and its distinctness
lemma under `a ≠ 1/30` are correct. The source does not formalize a sequence or
prove the claimed two-phase non-convergence consequence. Added
`Omega.Conclusion.not_tendsto_of_distinct_subsequential_limits` in
`lean/Omega/Conclusion/DistinctSubsequentialLimits.lean`: if two subsequences
with index maps tending to `atTop` converge to distinct limits, the original
sequence cannot converge to either limit. The new theorem kernel-builds
successfully (locked build, 8924 jobs).

### Halting/valuation/Walsh ledger unification verification (2026-10-31)

`Omega.Conclusion.paper_derived_halting_valuation_walsh_ledger_unification`
kernel-builds successfully (locked build, 3092 jobs). Its two-constructor
`diverges | haltsAt N` model supports the stated branch equations by case
analysis. In this source, no machine/configuration transition or encoding is
formalized, so these equations do not establish a result about machine
halting or undecidability. The inventory classifies it as a verified finite
model theorem with that scope.

### Hankel finite-modulus threshold verification (2026-10-31)

`Omega.Conclusion.HankelFiniteModSinglevaluedizationShortestLockingThreshold`
kernel-builds successfully (locked build, 3092 jobs). Its periodicity result is
a valid finite-equivalence orbit theorem. The asserted shortest threshold is
built into the definition `locksFutureFrom D n := 2 * D.rank ≤ n`, then follows
from `Nat.find`; it does not formalize a Hankel-window locking or
singlevaluedization criterion. The determinant localization result is separate
and conditional on its supplied determinant progression. The inventory now
records these scopes independently.

### Hidden-face budget threshold classification verification (2026-10-31)

`Omega.Conclusion.paper_conclusion_hidden_face_budget_sharp_threshold_classification`
builds successfully (locked build, 614 jobs). It validly propagates two explicit
premises: injectivity below `2*n`, and a witness at exact distance `2*n`.
It does not prove either premise from hidden-face geometry or an independent
budget construction. Recorded as a conditional threshold transfer theorem.

### Hypercube phase finite enumeration verification (2026-10-31)

`Omega.Conclusion.HypercubePhase` builds successfully (locked build, 3092 jobs).
Its image/value claims are correct finite enumerations in dimensions 4, 6, 8,
10, and 12. Their scope is those listed dimensions; these declarations do not
establish a general-dimensional classification. The inventory records this
scope limit rather than treating finite enumeration as a general theorem.

### JG Gödel dense-orbit aggregation verification (2026-10-31)

`Omega.Conclusion.JGGodelDenseOrbitsOnHyperbolaLeaf` builds successfully
(locked build, 3206 jobs). It is an aggregation theorem that delegates to the
imported log-lattice approximation, two-prime orbit density, and orthogonal
chart declarations; it adds no independent density proof. The dependency replay
reported a deprecated Complex import warning in the chart module, unrelated to
this candidate's theorem validity.

### JG slit orthogonal-coordinate chart verification (2026-10-31)

`Omega.Conclusion.JgSlitUniformizationOrthogonalCoordinates` builds
successfully (locked build, 3201 jobs). It proves the explicit coordinate,
conic-level, and differential identities under its stated positivity and
nonvanishing assumptions. The declarations are chart-level calculations; they
do not by themselves establish global uniformization or surjectivity onto a
slit domain. Build replay reports the deprecated `Mathlib.Data.Complex.Basic`
import warning.

### Joukowsky transport wreath embedding verification (2026-10-31)

`Omega.Conclusion.JoukowskyTransportWreathEmbedding` builds successfully
(locked build, 3167 jobs). It proves a finite embedding and cardinality formula
from explicit quadratic-root lifts and injective sign/permutation tagging under
the stated `w > 2` condition. The formal scope is finite; the source does not
establish global analytic uniformization or an infinite wreath-product result.

### Kernel-RH fixed-ray exclusion verification (2026-10-31)

`Omega.Conclusion.KernelRhOnlyFinitelyOftenOnFixedRay` builds successfully
(locked build, 3093 jobs). It validly derives eventual exclusion along `a*b`
from the strict slope gap, eventual upper bound, and assumed necessary lower
bound. It does not prove those bounds or construct a kernel-RH predicate from
an independent analytic object; classification is conditional.

### Joint finite-audit aggregation verification (2026-10-31)

`Omega.Conclusion.JointFiniteAuditIncompletenessPhasePrefixMultiscale` builds
successfully (locked build, 3095 jobs). It combines imported finite
address-cardinality, finite-codimension interpolation, and prime-avoidance
results, conditional on the supplied injectivity and linear-independence
hypotheses. The candidate does not add an independent multiscale
phase-prefix or incompleteness argument. Dependency replay emits a `letI`
style warning in the interpolation module.

### Kirchhoff Green determinant scalar identity verification (2026-10-31)

`Omega.Conclusion.KirchhoffGreenDeterminantIdentity` builds successfully
(locked build, 3092 jobs). The scalar algebra is valid under `D ≠ 0`,
`vol ≠ 0`, and `dOne = vol`. In this source, the definitions are real-valued
scalar expressions; no graph incidence/Laplacian matrices, Green operator,
cofactor theorem, or rank-one determinant lemma are constructed. The theorem is
therefore recorded as a conditional scalar normal form, not a formal matrix-tree
proof.

### Layered primeslice finite-support depth ceiling verification (2026-10-31)

`Omega.Conclusion.LayeredPrimesliceFiniteSupportDepthCeiling` builds
successfully (locked build, 135 jobs). Its contradiction is valid given finite
support, the supplied active-layer ≤ prime-slice bound, and faithfulness at
every depth. The `branchesAtEveryDepth` premise is defined as `True` and is
unused; the result is an abstract conditional obstruction, not a constructed
primeslice model. This vacuous premise and the true assumptions are captured in
the inventory scope notes.

### Leyang finite Dirichlet resolvent identity verification (2026-10-31)

`Omega.Conclusion.LeyangEdgeLogDerivativeDirichletResolventLimit` builds
successfully (locked build, 3199 jobs). For each finite `N`, away from the first
`N` poles, it proves the truncated product is nonzero and its logarithmic
derivative equals the finite resolvent sum. Despite the name, this declaration
does not prove convergence as `N → ∞` or identify an infinite resolvent limit.
Build replay reports a deprecated Real import warning.

### Leyang Q₅ cubic local-data verification (2026-10-31)

`Omega.Conclusion.LeyangGlobalLocalQ5UnramifiedCubic` builds successfully
(locked build, 8924 jobs). It proves finite polynomial facts (no roots in the
three-element residue carrier and an integer discriminant calculation). The
local degree, ramification index, residue degree, and three-element Galois group
are assigned as model constants; this source does not construct a Q₅ extension
or prove those local-field properties.

### Leyang–Lattes finite hypercube exact-form verification (2026-10-31)

`Omega.Conclusion.LeyangLattesHypercubeExactFormZeroCurvature` builds
successfully (locked build, 3093 jobs). It proves the finite Boolean-cube
potential's coordinate-weight edge increments and zero square boundary for
distinct coordinates. These are valid exact combinatorial identities at the
stated finite carrier; they do not imply broader geometric or arithmetic
claims without a separately proved map.

### Leyang global quadratic-factorization obstruction wrapper (2026-10-31)

`Omega.Conclusion.LeyangNoGlobalQuadraticQuadraticFactorization` builds
successfully (locked build, 3094 jobs). Its conclusion is obtained by duplicating
the imported primitive-certificate obstruction into both components of the
statement. It is valid conditional on that certificate, but contributes no
quartic cover, monodromy action, equivalence, or independent factorization
argument.

### Leyang Rademacher circle anomaly aggregation verification (2026-10-31)

`Omega.Conclusion.LeyangRademacherCircleAnomalyOrthogonalLedgers` builds
successfully (locked build, 3152 jobs). It combines an imported Rademacher
cumulant theorem with a circle-dimension value of 1 and a finite coordinate
carrier cardinality of 21. The “orthogonal” conclusion is only inequality of
these dimensions; no inner product or orthogonal subspaces are constructed.
The dual-extension data is instantiated with an empty set.

### Leyang rho 456 logarithmic-derivative verification (2026-10-31)

`Omega.Conclusion.LeyangRho456LogDerivativeRationalization` builds
successfully (locked build, 3256 jobs). It proves elementary derivatives of
`log |u^4 - 1|` and `log |u^6 - 1|` away from their zeros and applies constant
normalizations. The named rho combinations are defined from those expressions;
no independent spectral, arithmetic, or asymptotic rationalization is proved.

### Leyang S5 two-channel finite completeness verification (2026-10-31)

`Omega.Conclusion.LeyangS5TwoChannelMinimalCompleteness` builds successfully
(locked build, 3092 jobs). It reconstructs a finite seven-coordinate density
vector and supplies explicit witnesses distinguishing two channels at selected
small parameters. Its completeness/minimality scope is that finite observation
model; it does not establish a general S5 representation or channel
identifiability theorem.

### Leyang off-diagonal transposition quotient verification (2026-10-31)

`Omega.Conclusion.LeyangOffdiagonalTranspositionQuotient` builds successfully
(locked build, 3092 jobs). It proves a finite `S₄` stabilizer description for
an ordered distinct pair and uniquely solves a two-equation integer moment
system. These are valid finite permutation and algebra statements; the source
does not construct a curve, Frobenius action, or arithmetic-geometric
realization.

### LK first-zero monotone-approach sequence verification (2026-10-31)

`Omega.Conclusion.LkFirstZeroMonotoneApproach` builds successfully (locked
build, 8924 jobs). It proves strict monotonicity and limits for the explicitly
defined sinc-based real sequence and its reciprocal ratio. These are substantive
real-analysis theorems for those definitions; this file does not identify the
sequence with a first zero of an independently defined L-function or prove a
spectral interpretation. Build reports unused simp-argument warnings.

### Leyang transposition quotient/Jacobian decomposition wrapper verification (2026-10-31)

`Omega.Conclusion.LeyangTranspositionQuotientJacobianDecomposition` builds
successfully (locked build, 3098 jobs). It composes the finite S4 stabilizer
result with an imported quotient/Jacobian/Prym package. The conclusion follows
from those dependencies, while the wrapper adds no independent bridge
 equivalence or geometric construction.

### Lmax finite-primeizability singleton witness verification (2026-10-31)

`Omega.Conclusion.LmaxNotFinitePrimeizable` builds successfully (locked build,
3094 jobs). Given an eligible prime outside `S`, it forms the singleton set
`P = {p}` and delegates the orbit-length/product equality to
`LmaxPrimeProgrammability`. The theorem does not establish its prime-existence
premise or an unconditional global non-primeizability claim.

### Leyang Gödel hyperbola orbit-closure wrapper verification (2026-10-31)

`Omega.Conclusion.LeyangGodelHyperbolaOrbitClosure` builds successfully
(locked build, 3207 jobs). The finite-union closure equality is derived from an
imported two-prime dense-orbit theorem and continuity of the parametrization;
this module adds no density proof. Dependency replay reports a deprecated
Complex import warning in the Joukowsky chart module.

### Leyang local double-zero two-case model verification (2026-10-31)

`Omega.Conclusion.LeyangLocalDoublezeroBinaryClassification` builds successfully in a locked Lake run (3,095 jobs). The owner computes exact rational seed values and rescaling ratios for its two-constructor `sinh`/`cosh` model, then proves exhaustiveness by cases on that inductive type. This verifies the finite model arithmetic only; it does not classify analytic local double zeros.

### Local exactification resonance model verification (2026-10-31)

`Omega.Conclusion.LocalExactificationMacroscopicResonanceSeparation` builds successfully in a locked Lake run (3,172 jobs). The exactified profile and statistics are defined pointwise to equal the original ones, and the divergence conclusion specializes imported collision bounds to a selected profile. This is a model-specific consequence, not a theorem for an independently constructed exactification map. The build replay emitted an existing deprecated `Mathlib.Data.Real.Basic` import warning in `FoldSinglepairVisibleObstructions`.

### Local finite-clock consensus obstruction verification (2026-10-31)

`Omega.Conclusion.LocalFiniteHaltingNoGlobalFiniteConsensus` builds successfully in a locked Lake run (3,093 jobs). A uniform natural time for all local clocks implies the global terminal-readout premise, which the imported theorem rules out under the stated nonzero Cech-H2 obstruction. This is a conditional implication; the owner does not construct the obstruction or formalize computational halting.

### Localized finite-ledger domain audit (2026-10-31)

`Omega.Conclusion.LocalizedColimitFiniteLedgerLinearizationObstruction` builds successfully in a locked Lake run (3,092 jobs). The multiplicativity premise is quantified over all naturals, including zero, so its source establishes the identically-zero ledger consequence; the later prime-product collision statement is redundant under that stronger domain. A positive-input-only variant would be a different contract and is not proved by this owner.

### Localized finite-cover Cech wrapper verification (2026-10-31)

`Omega.Conclusion.LocalizedNoHighCechObstructionFiniteCover` builds successfully in a locked Lake run (3,093 jobs). Its theorem applies user-supplied implications from two exactness propositions to arbitrary target propositions. The chapter-local “no high Cech” predicates are aliases for exactness proxies; this owner does not construct homology carriers or prove exactness from cover geometry.

### Localized solenoid prime-separation equivalence verification (2026-10-31)

`Omega.Conclusion.LocalizedSolenoidCoprimeArtinMazurCompleteness` builds successfully in a locked Lake run (3,093 jobs). For a finite family of bases bounded below by two, it proves equivalence between primewise periodic-count separation, the defined prime-recovery predicate, and gcd-one separation. These are genuine arithmetic equivalences on the owner definitions; this file does not construct a topological solenoid or analytic Artin-Mazur zeta function. The replay emitted one unnecessary-`simpa` linter warning.

### Low-degree Stokes observation collision verification (2026-10-31)

`Omega.Conclusion.LowTotalDegreeStokesFamilyNonseparation` builds successfully in a locked Lake run (8,924 jobs). In its declared `Fin 2` model, the boundary map is injective while the defined low-degree moment and Stokes observables are constant, yielding an explicit collision. This is a genuine finite-observation counterexample; it does not establish a geometric polycube or Stokes theorem.

### M2 level-3 exact-sequence separation wrapper verification (2026-10-31)

`Omega.Conclusion.M2Level3IncidenceExactSequence15Separation` builds successfully in a locked Lake run (3,096 jobs). It projects two conclusions from the imported crossboundary-stability theorem: the exact-sequence proposition and a characteristic-polynomial inequality. The file adds no independent incidence construction or separation proof.

### Metallic integer binary-collapse classification verification (2026-10-31)

`Omega.Conclusion.MetallicIntegerBinaryCollapse` builds successfully in a locked Lake run (3,208 jobs). Under its integer parameter restriction A ≥ 1, the owner proves the objective comparison at A=1 and strict compression/certificate comparisons for each integer A>2 against A=2. This is a positive classification for the imported metallic Perron-root objectives, not a counterexample. The build replay emitted deprecated `Mathlib.Data.Real.Sqrt` imports and an unnecessary-`simpa` warning.

### General binary-state capacity replacement (2026-10-31)

`Omega.Conclusion.MinLatchesLogStates` previously verified only finitely many `Nat.clog` values despite a broad minimum-latches headline. Added general kernel-checked lemmas: `Nat.clog 2 n ≤ m ↔ n ≤ 2^m` and the resulting least-exponent characterization for every natural `n`, including edge cases. The owner now supports an arbitrary-state arithmetic capacity bound, but still does not define Boolean circuits or prove a circuit-realization minimum. The locked build passed (3,092 jobs).

### Mixed-collision finite Hilbert feature characterization verification (2026-10-31)

`Omega.Conclusion.MixedCollisionCharacteristicHilbertGeometry` builds successfully in a locked Lake run (3,158 jobs). For its finite normalized NNReal distribution model and positive exponent, it proves the kernel/feature-map Gram identity, squared MMD equals squared Euclidean feature distance, and Cauchy-Schwarz equality for the kernel is equivalent to equality of the distributions. This is a substantive positive result scoped to the explicit finite feature construction.

### Mod-2 shadow score-recovery obstruction verification (2026-10-31)

`Omega.Conclusion.Mod2ShadowInsufficientForArchimedeanInstability` builds successfully in a locked Lake run (3,092 jobs). The owner exhibits score pairs 12/14 and 13/15 that collide under its mod-2 shadow, then proves that any audit factoring through that shadow cannot recover the full score. This is a valid finite quotient-information obstruction; it does not prove an analytic instability theorem.

### Moment-Hankel bad-prime stiffness inclusion audit (2026-10-31)

`Omega.Conclusion.MomentHankelBadPrimeStiffnessSupport` builds successfully in a locked Lake run (3,092 jobs). Its conclusion is exactly the set-inclusion restatement of the premise that every bad prime has nonzero stiffness. It supplies no independent moment-Hankel or prime-distribution argument.

### Two-sheet monoidal-jump torsion classification verification (2026-10-31)

`Omega.Conclusion.MonoidalJumpA2TorsionClassification` builds successfully in a locked Lake run (3,092 jobs). For the declared homomorphisms `Equiv.Perm (Fin 2) → ZMod 2`, the transposition value determines the map, is 2-torsion, and both values are realized. This is an exact finite-group classification on that model, not a general torsion result.

### Monotone Boolean finite-cube representation verification (2026-10-31)

`Omega.Conclusion.MonotoneBooleanClone` builds successfully in a locked Lake run (3,094 jobs). It constructs, for every monotone Boolean function on `Fin n → Bool`, a DNF whose clauses are satisfying supports, proves each thresholded additive clause score equals its Boolean indicator, and proves the DNF represents the function. This is a general finite combinatorial representation, not a circuit complexity/resource bound. A replayed dependency emitted a deprecated `Mathlib.Data.Real.Basic` import warning.

### Negative-sign barrier asymptotic-ratio verification (2026-10-31)

`Omega.Conclusion.NegativeSignSameBarrierDifferentResidue` builds successfully in a locked Lake run (3,093 jobs). Given the explicit nonzero-parameter conditions and supplied `SharpAsymptotic` hypotheses for scan and time-reversal sequences, it derives the shared logarithmic barrier and limiting ratio `cc / ciota`. It does not prove the asymptotic hypotheses or an unconditional residue statement.

### Complete normal-form decidability obstruction verification (2026-10-31)

`Omega.Conclusion.NoComputableCompleteNormalForm` builds successfully in a locked Lake run (3,092 jobs). It proves the general implication that a sound and complete normal-form function makes its equivalence decidable, so this contradicts an explicitly supplied undecidability premise. The owner does not instantiate that premise with a concrete undecidable relation or prove a reduction.

### Complete-invariant decidability implication scope audit (2026-10-31)

`Omega.Conclusion.NoComputableFinitePrimeCompleteInvariant` builds successfully in a locked Lake run (3,092 jobs). Its proof correctly shows that any complete invariant into a type with decidable equality decides the underlying equivalence, contradicting a supplied undecidability premise. Despite the declaration name, the codomain has no finiteness instance or cardinality premise, and the owner supplies no concrete undecidable relation. The result is a general conditional decidability implication, not a finite-invariant pigeonhole obstruction.

### Faithful total-order time-functor contradiction wrapper audit (2026-10-31)

`Omega.Conclusion.NoFaithfulTotalOrderTimeFunctor` builds successfully in a locked Lake run (3,092 jobs). The result is an abstract contradiction from supplied implications: the faithful-time predicate yields a global clock, while the supplied no-clock premise excludes it under a supplied obstruction witness. This owner does not define the time-functor semantics, construct Cech cohomology, or prove the obstruction premise.

## Two-axis audit abstraction review (2026-10-31)

`Omega.Conclusion.NoUniversalTwoAxisAuditCompletion` builds successfully in a
locked Lake run (3,093 jobs, exit 0). Its conclusion follows from fields of
`TwoAxisAuditCompletionData`: a supplied dichotomy and supplied branch
contradictions under three witness predicates. The module does not construct an
audit scheme, derive those witnesses, or establish them from a concrete model.
This is a valid abstract conditional no-go schema; the source does not prove a
model-specific impossibility result.

## Restricted DPI exactness wrapper review (2026-10-31)

`Omega.Conclusion.NoncontractibleRestrictedDpiExact` builds successfully in a
locked Lake run (3,098 jobs, exit 0). The owner proves the restricted-loss
component by definitional equality and forwards supplied bad-mod-three and
good-component implications to the imported fiber parity/homotopy theorem.
Those implications carry the substantive classification assumptions; this
file does not independently prove a DPI or homotopy classification result.

## Nonzero-spectrum window-length wrapper review (2026-10-31)

`Omega.Conclusion.NonzeroSpectrumCannotRecoverWindowLength` builds in a locked
Lake run (3,095 jobs, exit 0). The theorem returns its invariant-constancy
hypothesis unchanged and proves that the imported ambiguity-shell budget
`m ↦ m - 1` is injective for `m ≥ 3`. The local arithmetic is valid; no
spectral observation map or separate non-identifiability theorem is constructed
in this owner.

## Odd-tail finite-rank threshold wrapper review (2026-10-31)

`Omega.Conclusion.OddtailArithmeticSensitivityInfiniteRankThreshold` builds
successfully in a locked Lake run (3,092 jobs, exit 0). The finite-rank
exclusion follows by contraposing the supplied `hblind` implication, while
non-finiteness of the designated operator is supplied directly as `hinfinite`.
The owner defines no concrete criterion, compressor, RH-equivalence relation,
or operator construction; this is conditional logical packaging.

## Odd-tail scalar-kernel wrapper review (2026-10-31)

`Omega.Conclusion.OddtailNoScalarUnifyingPiKernel` builds successfully in a
locked Lake run (3,093 jobs, exit 0). It derives `¬ scalarKernel` from three
implications and a supplied contradiction among their conclusions. The kernel
and shadow notions are opaque propositions in this owner; their constructions
and incompatibility proof are not developed locally. This is a valid
propositional schema, not a model-specific obstruction theorem.

## Ordered Nevanlinna completeness wrapper review (2026-10-31)

`Omega.Conclusion.OddtailOrderedNevanlinnaCompleteness` builds successfully in
a locked Lake run (3,092 jobs, exit 0). Its theorem returns the supplied
ordered-completeness implication and support-level counterexample unchanged.
The file constructs neither the relevant function objects nor a counterexample;
its formal content is assumption packaging.

## Deep finite-prefix ambiguity criterion (2026-10-31)

`Omega.Conclusion.PcdimLowerboundDeepAmbiguity` builds successfully in a
locked Lake run (3,092 jobs, exit 0). It proves a reusable abstract criterion:
if the auxiliary readout depends on one finite prefix and the primary readout
has a collision at every prefix depth, then the paired readout is not injective.
The proof is substantive and correct under its hypotheses; concrete instances
of those hypotheses remain separate obligations.

## Periodic-amplitude energy identity review (2026-10-31)

`Omega.Conclusion.PeriodicAmplitudeResidueEnergySplitting` builds in a locked
Lake run (3,168 jobs, exit 0). It constructs a finite complex amplitude model,
sets its average to zero, scales nonzero coordinates by `sqrt p`, and proves a
normalized norm-square identity plus positivity from a nonzero coefficient.
This is a valid finite weighted identity; the owner does not define a Fourier
transform or establish Parseval for arbitrary periodic signals. The imported
complex-basic path also emits a deprecation warning.

## Pisot boundary profile non-summability review (2026-10-31)

`Omega.Conclusion.PisotBoundaryShadowNotL2` builds successfully in a locked
Lake run (8,925 jobs, exit 0). It proves that the explicit profile
`n ↦ 1/(|n|+1)` is not summable and forwards a pointwise Fourier identity from
its imported owner. The file does not identify that profile with squared
coefficients of the boundary object, so the advertised `L²` interpretation
needs a separate coefficient-map theorem. The profile-level non-summability
result itself is valid.

## Bivariate quartic null-cone lemma review (2026-10-31)

`Omega.Conclusion.PoissonBivariateQuarticNullConeFdivUniversal` builds
successfully in a locked Lake run (3,092 jobs, exit 0). It proves the exact
real-algebraic equivalence between vanishing of `c * (A^2 + 4 * B^2)` for
nonzero `c` and `A = B = 0`. This is a valid canonical null-cone lemma; the
theorem statement contains no Poisson or divergence structure.

## Poisson Cauchy fourth-moment decoding review (2026-10-31)

`Omega.Conclusion.PoissonCauchyM4Decode` builds successfully in a locked Lake
run (3,092 jobs, exit 0). It algebraically solves the supplied `hA3`, `hB6`,
and `hB8` polynomial identities for `mu4` and, under `mu3 = mu5 = 0`, for
`mu6`, assuming `mu2 ≠ 0`. The inversion is valid; the moment interpretation
and source identities remain hypotheses rather than derived results here.

## Poisson Cauchy minimal Laurent-order claim review (2026-10-31)

`Omega.Conclusion.PoissonCauchyMinimalLaurentOrderIdentifiability` builds
successfully in a locked Lake run (3,092 jobs, exit 0). Its proof simply
returns the assumptions that two coefficients are nonzero; the order parameter
`m` is unused, and no Laurent polynomial or identifiability relation occurs in
the conclusion. A canonical replacement needs an explicit polynomial/support
model and a proved minimal-order criterion.

## Poisson Cauchy moment tomography review (2026-10-31)

`Omega.Conclusion.PoissonCauchyMomentTomography` builds successfully in a
locked Lake run (3,092 jobs, exit 0). It proves explicit real-algebra
inversions recovering `mu2`, `|mu3|`, and `mu4` from stipulated coefficients,
and a two-model identifiability result under positivity and a nonzero
2-by-2 determinant condition. These are substantive conditional theorems; the
coefficient formulas are hypotheses here, not derived from Poisson data.

## Two-KL minimal entropy moment tomography review (2026-10-31)

`Omega.Conclusion.PoissonTwoKlMinimalEntropyMomentTomography` builds
successfully in a locked Lake run (3,094 jobs, exit 0). It applies the imported
CircleDimension moment-tomography theorem to supplied coefficient equations
and uses nonnegativity to select the square-root branch for the variance.
This is a valid corollary; KL divergence and asymptotic coefficient derivation
are not modeled in this conclusion owner. The real-basic import emits a
deprecation warning.

## Window-six full-matrix title scope review (2026-10-31)

`Omega.Conclusion.PushforwardFullMatrix` builds successfully in a locked Lake
run (3,092 jobs, exit 0). It verifies `Nat.fib 8 = 21`, elementary arithmetic
for 21 and 441, the factorization `21 = 3*7`, and nonsquareness of 21 among
integers strictly between 1 and 21. Despite the title and module comment, the
owner defines no 21-dimensional vector space, endomorphism algebra, or
pushforward map. The canonical scope is the finite arithmetic package only.

## Finite q-local wordtrace separation scope review (2026-10-31)

`Omega.Conclusion.QLocalWordtraceNotCompleteForEllipticTraceFamily` builds
successfully in a locked Lake run (3,111 jobs, exit 0). Its trace recurrence
comes from an imported golden-mean matrix identity. The finite packet is
independent of `y` by definition, and the rational function `(y^2+y+1)/(y+1)`
separates the explicit values 0 and 1. This is a valid separation example for
that defined packet and function, but no elliptic curve or elliptic trace
family appears in the owner. The broader arithmetic-geometric interpretation
is therefore not established.

## Polynomial algorithm spectral-radius label review (2026-10-31)

`Omega.Conclusion.PolynomialAlgorithmSpectralRadiusMass` builds successfully
in a locked Lake run (3,093 jobs, exit 0). The coefficient-sum identity and
positivity for nonzero `Polynomial ℕ` are valid. However, the purported
spectral-radius quantity is defined as `f.eval 1`, so its equality with mass is
reflexive; no operator, shift action, or spectrum appears. The imported
shift-commuting polynomial module also encodes addition/composition through
`+ 0` and `* 1`. A canonical statement here is the coefficient-mass identity;
a spectral-radius theorem needs an actual operator model.

## Power-divergence two-exponential recurrence review (2026-10-31)

`Omega.Conclusion.PowerDivergenceSecondorderRecurrence` builds successfully
in a locked Lake run (3,153 jobs, exit 0). For its explicitly defined positive
two-exponential sequence with distinct rates, it proves the closed form, the
characteristic second-order recurrence, and strict log-convexity by factoring
the second difference as a positive mixed term. The theorem is substantive in
that model; deriving the model from a power-divergence measure is outside this
owner.

## Prime-adjunction finite-rank wrapper review (2026-10-31)

`Omega.Conclusion.PrimeAdjunctionNoFiniteRankAdditiveLinearization` builds
successfully in a locked Lake run (3,092 jobs, exit 0). Its conclusion follows
by applying a supplied obstruction to the second conjunct. No prime monoid,
rank notion, or linearization map is formalized in this owner; the schema is
valid but does not establish a concrete finite-rank impossibility result.

## Prime-log infinite-rank register wrapper review (2026-10-31)

`Omega.Conclusion.PrimeLogInfiniteRankRegister` builds successfully in a
locked Lake run (3,092 jobs, exit 0). The proof is exactly the supplied
implication applied to the supplied boundary witness. The route, factor,
prime-log boundary, and finite visibility are abstract predicates; no concrete
prime-log or rank argument is formalized in this owner.

## Prime-modulus finite-exception obstruction review (2026-10-31)

`Omega.Conclusion.PrimeModulusExceptionSchemeCollapse` builds successfully in
a locked Lake run (3,092 jobs, exit 0). It proves that a predicate holding for
every sufficiently large prime except 2 cannot have all non-bad primes contained
in a finite set. The infinitude-of-primes argument is substantive and valid;
the predicate remains abstract, so arithmetic classification is a separate
obligation.

## Prime-register carrier cardinality repair (2026-10-31)

`Omega.Conclusion.PrimeRegister` contained a reflexive theorem for the claimed
truncated-register cardinality. Replaced it with the actual function-space
statement `Fintype.card (Fin k → Fin (E+1)) = (E+1)^k`, proved by `simp`, and
updated its sole downstream use in `RateCdimArithmetic` to state the carrier
cardinality. Both owner targets built successfully in a locked run (3,134
jobs, exit 0). This repairs the finite exponent-vector cardinality claim; the
rest of `PrimeRegister` remains a collection of finite combinatorial and
conditional encoding results, not a general computational model theorem.

## Prime-register cross-resolution contraction review (2026-10-31)

`Omega.Conclusion.PrimeRegisterCrossresolutionRigidityAttractor` builds in a
locked Lake run (3,092 jobs, exit 0). Under `|B^k| < 1`, the affine map has a
unique fixed point and its explicitly defined geometric sequence converges to
that point. The lifted/base action equality is supplied directly in the data
and merely forwarded. Also, the sequence named `iterate` is defined in closed
form; this owner does not prove a recursion identifying it with repeated
application of `Psi`.

## Prime-register additive-ledger obstruction review (2026-10-31)

`Omega.Conclusion.PrimeRegisterFixed2adicAmbientVsFiniteLedger` builds in a
locked Lake run (8,924 jobs, exit 0). It proves that no injective
`f : ℕ → ℕ` can satisfy `f 1 = 0` and `f (m*n) = f m + f n`, using equal
images of powers of 2 and 3 followed by a parity contradiction. It also proves
injectivity of the explicit translation action on `Fin 2 → ℤ`. The phrase
“2-adic ambient” here denotes only that integer function carrier; it is not a
2-adic construction.

## Prime-register K-stretch rigidity bound review (2026-10-31)

`Omega.Conclusion.PrimeRegisterKStretchRigidityLb` builds successfully in a
locked Lake run (3,098 jobs, exit 0). Given supplied necessary/sufficient
density implications, it transfers them to the cdim normalization, derives a
ratio bound when the target cdim is positive, and excludes embeddings when the
target cdim is zero but the source cdim is positive. These conditional real
inequalities are valid; the embedding-to-density premises are not constructed
in this owner.

## Primeslice support-chain countability review (2026-10-31)

`Omega.Conclusion.PrimesliceOmegaSupportChainCountable` builds successfully
in a locked Lake run (3,092 jobs, exit 0). It constructs the chain
`range (N+1)`, proves its cardinality and strict growth, and shows no fixed
finite set contains every chain member. This is a genuine elementary
countability witness; prime-slice-specific structure is not represented in the
owner theorem.

## Finite-multiset entropy plateau review (2026-10-31)

`Omega.Conclusion.PrimeslicePartitionPlateauDyadicSpread` builds successfully
in a locked Lake run (3,097 jobs, exit 0). For a nonempty finite multiset of
naturals, it proves a maximum support value, entropy increments from tail
counts, exact multiplicity curvature via an imported identity, a plateau at
the maximum, and strict growth below it. No dyadic-spread construction is
formalized locally; the imported curvature owner emitted two linter warnings.

## Primitive two-step coordinate blindness review (2026-10-31)

`Omega.Conclusion.PrimitiveTwoStepCodimoneBlindness` builds successfully in
a locked Lake run (3,092 jobs, exit 0). It proves a valid abstract
support-one sensitivity statement: sequences agree off coordinate 2, and a
functional stipulated to read that coordinate linearly changes by `a2*u`.
No primitive-polynomial or codimension-one structure is formalized in this
owner. The source uses a deprecated `if_neg` simp lemma.

## Primorial additive versus Gödel multiplicative encoding review (2026-10-31)

`Omega.Conclusion.PrimorialAdditiveVsGodelMultiplicative` builds successfully
in a locked Lake run (3,092 jobs, exit 0). The multiplicative exponent map is
injective under the stated pairwise-coprime bases-at-least-two hypothesis; the
homomorphism result correctly says an injective homomorphism into a
commutative semigroup forces its source to commute. The package named as an
infinite-prime-support result proves only finitely many small-prime facts, so
it does not prove the named infinitude claim. The canonical statement is the
scoped injectivity theorem plus an explicit prime-support hypothesis for any
future infinite-support conclusion. No owner theorem here proves injectivity
of the mixed-radix map in general dimension; only dimensions zero and one are
covered.

## Primorial axis dimension proxy review (2026-10-31)

`Omega.Conclusion.PrimorialAxisDimensionLaw` builds successfully in a locked
Lake run (3,092 jobs, exit 0). It defines a real logarithmic proxy and takes
its natural ceiling as `k_min`; it then proves the ceiling is the least
natural threshold index and that the rounding error lies in `[0,1)`. These
claims are correct for the stipulated proxy. Despite the paper-facing name,
the owner derives no primorial estimate, asymptotic, or geometric axis
dimension from an independent model.

## Primorial axis second-order proxy review (2026-10-31)

`Omega.Conclusion.PrimorialAxisSecondOrder` builds successfully in a locked
Lake run (3,167 jobs, exit 0). It defines a proxy with a linear term and a
square-root term, proves their exact algebraic split after division by the
chosen logarithm, and proves ceiling minimality for nonnegative parameter
`p`. The exported paper-facing name is a definition of a proposition, not a
theorem deriving it from primorial data. No asymptotic expansion or
primorial-threshold inversion is proved by this owner.

## Finite principal-shadow kernel counterexample review (2026-10-31)

`Omega.Conclusion.PrincipalShadowFiniteOfforiginBorelNotRigid` builds
successfully in a locked Lake run (3,092 jobs, exit 0). For a coordinate
space with more coordinates than the stipulated finite list of constraints,
it constructs a nonzero vector supported at the first unconstrained index.
It separately defines all finite sample data to be zero and the host signature
to be `t ↦ t`. Thus this is a valid coordinate-kernel counterexample to
finite-data rigidity in that constructed model. No Borel transform, analytic
principal-shadow data, or analytic host family is represented, so those
interpretations are not established by this owner.

## Fixed-depth finite linear-kernel review (2026-10-31)

`Omega.Conclusion.PrincipalShadowFixedDepthPointedHostInfiber` builds
successfully in a locked Lake run (3,092 jobs, exit 0). It packages a real
linear map from `Fin N → ℝ` to `Fin (2*n) → ℝ` and uses rank-nullity to show a
nonzero kernel when `2*n < N`. This is a genuine finite-dimensional linear
algebra statement. The owner does not define a principal-shadow analytic
sampling map or a host/in-fiber object; connecting the result to those terms
requires an additional construction and compatibility theorem.

## Principal-shadow mismatch ladder inversion repair (2026-10-31)

`Omega.Conclusion.PrincipalShadowMismatchLadderJacobiCouplingInversion` builds
successfully in a locked Lake run (3,093 jobs, exit 0). The cumulative product
formula and positivity hypotheses yield the first squared coupling and every
later consecutive ratio. The original `Delta 0 = u0` premise was unused, so it
has been removed from the theorem signature. The result remains conditional:
this owner does not construct a Jacobi mismatch ladder or derive the product
formula from one. The old `Mathlib.Data.Real.Basic` import also emits a
deprecation warning.

## Quadratic discriminant radicand-domain counterexample (2026-10-31)

`Omega.Conclusion.QuadraticFieldRamification` now proves the explicit
arithmetic witness `quadDisc 8 ≠ quadDisc 2`; its locked Lake build succeeds
(3,092 jobs, exit 0). Since `ℚ(√8) = ℚ(√2)`, the unrestricted piecewise
function is not a field-discriminant function on arbitrary radicands. The
standard quadratic-field formula requires reducing to a squarefree radicand;
the owner’s formula and divisibility lemmas do not encode that reduction. Its
“minimal prime ledger” theorem is only excluded middle, and the Riccati
ramification declaration is likewise a divisibility disjunction rather than
a field-ramification result. The canonical scope is the exact integer
function and its proved divisibility facts, not field ramification or étale
lifting.

## Rank-one Cauchy orthogonality scope review (2026-10-31)

`Omega.Conclusion.RankoneCauchyOrthogonality` builds successfully in a locked
Lake run (3,092 jobs, exit 0). It proves a finite-sum identity and the
conditional implication that equal Cauchy secant values at distinct
off-diagonal parameters force the associated cross term to vanish. The
candidate vector’s coordinate equation is also verified. However, this owner
does not define the advertised diagonal-plus-rank-one matrix action or prove
that the candidate is an eigenvector of that action. The canonical statement
is the proved finite-sum result; the matrix eigenproblem remains a separate
formalization obligation.

## Rank-two finite audit tuple hypothesis repair (2026-10-31)

`Omega.Conclusion.RanktwoFiniteTruncationCannotSplitBooleanBlindcavity` builds
successfully in a locked Lake run (8,925 jobs, exit 0). Its conclusion is
definitional invariance of a tuple formed from `gcd` and `lcm` when those two
values agree. The four positivity assumptions were unused and have been
removed. This owner does not define a Boolean-blind cavity or prove a finite
truncation separation result; the canonical theorem is the hypothesis-minimal
invariance statement.

## ReadUS null trichotomy wrapper hypothesis repair (2026-10-31)

`Omega.Conclusion.ReadusNullTrichotomyNormalForm` and its sole consumer,
`Omega.Conclusion.ThreeEndCertificateJointSufficiencyMinimality`, both build
successfully in a locked Lake run (3,097 jobs, exit 0). The wrapper returns
the supplied exhaustive disjunction and derives absence of `hiddenFailure`
from the supplied contradiction premise; it does not establish either fact
from a ReadUS model. Three unused mutual-exclusion hypotheses were removed
from the wrapper and consumer. The canonical result is now stated with only
the assumptions its proof actually uses.

## RealInput40 Bowen–Franks/Jordan tower aggregator scope review (2026-10-31)

`Omega.Conclusion.RealInput40BFJordanTowerSeparation` and its dependent
`RealInput40FullEssentialPureZeroSpectrumStripping` build successfully in a
locked Lake run (3,188 jobs, exit 0). The imported Bowen–Franks/K-theory owner
does prove that its concrete `I - A` permutation matrix has a two-sided
integer-matrix inverse. However, the displayed Bowen–Franks order and
Cuntz–Krieger ranks are natural-number constants, and the nilpotent kernel
dimensions are explicit functions with stipulated values; this aggregator
only combines those declarations. The Lean owners do not construct the
Bowen–Franks group or Cuntz–Krieger algebras and do not derive the K-theory
invariants from the matrix. The canonical scope is matrix unimodularity plus
the stated finite function values, not a derived operator-algebraic
classification.

## RealInput40 Euler-jet/Perron quartic scope review (2026-10-31)

`Omega.Conclusion.RealInput40EulerJetZeroTempPerronFieldSplitting` builds
successfully in a locked Lake run (3,096 jobs, exit 0). It proves that the
explicitly defined real coefficients lie in `ℚ(√5)`, that one coefficient is
irrational, and that the specified integer quartic has no factorization into
two monic integer quadratics. These are genuine claims about the declared
numbers and polynomial. The owner does not derive those coefficients or the
quartic from an Euler jet or a Perron operator; that interpretation remains
outside its theorem contract.

## RealInput40 detailed-balance support obstruction review (2026-10-31)

`Omega.Conclusion.RealInput40GroundSupportIrreversibility` builds
successfully in a locked Lake run (782 jobs, exit 0). It proves the valid local
implication that positive stationary mass and a positive forward rate cannot
satisfy detailed balance when the reverse rate is zero; the second theorem
repackages the same contradiction. No transition matrix constraints,
stationary distribution, or self-dual completion are constructed, so the
claim is a conditional detailed-balance obstruction rather than a result
about a specific Markov model. The owner also has a deprecated real import.

## RealInput40 half-entropy/self-duality wrapper review (2026-10-31)

`Omega.Conclusion.RealInput40HalfentropySelfdualityNotDetailedBalance` builds
successfully in a locked Lake run (2 jobs, exit 0). It reuses one supplied
state satisfying assumed self-duality, half-entropy freezing, and
non-detailed-balance predicates to witness two existential propositions. The
proof is correct but entirely hypothesis packaging; no entropy, completion,
or balance structure is defined. The canonical result is the generic
existential-introduction lemma, while the RealInput40 interpretation requires
an independent model instantiating the predicates.


## RealInput40 open-strip single-source scope review (2026-10-31)

`Omega.Conclusion.RealInput40OpenStripSingleSource` and its determinant factorization dependency build successfully in a locked Lake run (3,121 jobs, exit 0). The owner proves the golden-ratio quadratic factorization and imports a polynomial determinant factorization over rational coefficients. Its open-strip assertion is implication packaging: holomorphicity/nonvanishing of `H` and the formula for `zetaHat` over the chosen denominator are supplied as hypotheses and returned as the conclusion. No analytic zeta function is constructed, and the polynomial identity alone does not prove the analytic single-source claim.


## RealInput40 slope-mismatch obstruction scope review (2026-10-31)

`Omega.Conclusion.RealInput40SlopeMismatchContinuousModelObstruction` builds successfully in a locked Lake run (3,093 jobs, exit 0). It proves a valid abstract incompatibility: if all three Boolean flags hold, the supplied endpoint-lock field forces `alphaMax = 1/2`, contradicting the separately supplied mismatch field. The critical slice and semantic flags are structure fields; no continuous model, slope, or extension construction is defined. The canonical scope is the conditional inconsistency lemma, not a constructed continuous-model obstruction. The file also uses a deprecated real import.


## RealInput40 synchronization/zero-spectrum alignment scope review (2026-10-31)

`Omega.Conclusion.RealInput40SyncLengthZeroSpectrumAlignment` builds successfully in a locked Lake run (3,095 jobs, exit 0). The reset-word source gives a genuine finite 40-state transition model whose five zero symbols synchronize the product state, and proves no shorter word synchronizes it. The nilpotent-index owner instead defines essential/full kernel dimensions by explicit piecewise functions. The conclusion combines these facts but does not derive that synchronization length equals a kernel stabilization index; the numerical coincidence is across separate models.


## RealInput40 two-typical ghost non-reproduction scope review (2026-10-31)

`Omega.Conclusion.RealInput40TwoTypicalGhostIrreducibility` builds successfully in a locked Lake run (3,093 jobs, exit 0). It defines a cyclic p-block and trace tower, imports the p-typical Frobenius–Verschiebung identity, and proves that the tower cannot equal a profile required to vanish from index two onward: at index one the tower is `2 * u^2`, nonzero under the stated `u ≠ 0` assumption. This is a genuine finite algebraic non-reproduction theorem for the declared model and profile condition, not a general irreducibility theorem.


## RealInput40 UV activation wall scope review (2026-10-31)

`Omega.Conclusion.RealInput40UVUniversalActivationWall` builds successfully in a locked Lake run (3,092 jobs, exit 0). The substantive statement is the elementary real factorization equivalence `u² v³ (1-v)=0 ↔ v=1` under `u>0`, `v>0`; the remaining conjuncts are numeral arithmetic. It defines no activation model, so the canonical result is a conditional factorization lemma rather than a universal activation theorem.


## RealInput40 gauge-difference cubic scope review (2026-10-31)

`Omega.Conclusion.Realinput40GaugeDifferenceModgaussianCubic` builds successfully in a locked Lake run (3,092 jobs, exit 0). It proves an exact exponential cancellation identity for a stipulated cubic polynomial with fixed rational coefficients and nonzero complex scale. The Gaussian factor cancels the quadratic term after substitution. No probability distribution, moment generating function, convergence, or mod-Gaussian limit is formalized, and the coefficients are assumptions encoded as constants rather than derived cumulants.


## RealInput40 primitive Ramanujan first-two-layers scope review (2026-10-31)

`Omega.Conclusion.Realinput40PrimitiveRamanujanFirstTwoLayers` builds successfully in a locked Lake run (3,092 jobs, exit 0). Its complete content is the elementary divisibility fact that `r ≥ 3` implies `r ∤ 2`. No Ramanujan object or layer structure is defined by this declaration; the canonical statement is just the natural-number lemma.


## Recursive solenoid Lie-shadow scope review (2026-10-31)

`Omega.Conclusion.RecursiveSolenoidLieShadow` builds successfully in a locked Lake run (3,092 jobs, exit 0). Its local proofs are Boolean constant-function equalities and `0 ≠ 1`; the combined pcdim result assumes the two Boolean branch values and derives their inequality. The file defines no solenoid, Lie quotient, profinite kernel, or computability construction. Treat the named topological/halting interpretation as unsupported by this owner unless a separate constructed model supplies the bridge.


## Register prefix-topology extension obstruction review (2026-10-31)

`Omega.Conclusion.RegisterUltrametricLipschitzAndGodelNoRealExtension` builds successfully in a locked Lake run (3,092 jobs, exit 0). This owner contains a genuine concrete theorem: the defined Toeplitz map is prefix nonexpansive, its one-step prefix contraction property is equivalent to zero diagonal coefficient, basis streams converge to zero, and the prescribed unbounded values `n+2` rule out any sequentially continuous real extension at zero. Scope is the explicit product-prefix topology on natural-number streams; no general Gödel coding or metric is formalized.


## Reject-null finite normal-form weakness review (2026-10-31)

`Omega.Conclusion.RejectNullFiniteNormalForm` builds successfully in a locked Lake run (3,092 jobs, exit 0). The proof derives the six-way disjunction solely from `hnull`; the defect premise and all within-family exclusivity hypotheses are unused, and no run/classification datatype is defined. The theorem is valid but weaker than its docstring claim. A canonical coverage statement should use `hnull ∨ hdef`; an exclusivity claim additionally needs cross-family disjointness and a formal run coverage premise.


## Relative-homology corank protocol-null scope review (2026-10-31)

`Omega.Conclusion.RelativeHomologyCorankProtocolNull` builds successfully in a locked Lake run (3,094 jobs, exit 0; one style suggestion). It proves a conditional finite-fiber counting result: under uniform fiber cardinality `2^beta`, positive beta is equivalent to a nontrivial visible fiber; such a fiber cannot be made injective with a `Unit` side register, using the imported register lower bound. At beta zero, all fibers have size one and the screen map is injective. The source does not construct relative homology groups; its relative-Betti predicate is a scalar conditional-entropy alias, so that interpretation needs an external formal bridge.


## Relative zeta quotient critical-order scope review (2026-10-31)

`Omega.Conclusion.RelativeZetaQuotientCriticalOrderInvariance` builds successfully in a locked Lake run (3,093 jobs, exit 0; deprecated import warning). It proves algebra for a stipulated simple-pole-shaped expression and an indicator-valued pole order: division by a nonzero constant rescales the residue and preserves its nonzero status. No analytic zeta functions, Laurent expansion theorem, or analytic pole order are defined. The canonical scope is the model algebra lemma; analytic invariance needs those additional constructions.


## Rényi-2 asymptotic uniformization wrapper review (2026-10-31)

`Omega.Conclusion.Renyi2NoAsymptoticUniformizationSubsequence` builds successfully in a locked Lake run (3,092 jobs, exit 0). Its statement is generic modus tollens over arbitrary propositions. No Rényi functional, sequence, subsequence, or asymptotic condition appears. Keep it as a generic logical lemma or supply the concrete analytic premises; the file alone does not establish the paper-facing asymptotic claim.


## Residue even-window one-functional repair review (2026-10-31)

`Omega.Conclusion.ResidueEvenWindowOneFunctionalRepair` builds successfully in a locked Lake run (3,092 jobs, exit 0). The owner proves a constructive affine linear-algebra result: when `Lambda chi ≠ 0`, exactly one point on the line `b0 + c • chi` has functional value `Lambda target`, with coefficient `(Lambda target - Lambda b0) / Lambda chi`. This is a genuine reusable theorem; the paper-facing even-window residue application still needs a concrete vector-space model and functional instantiation.


## Residue pressure-drop escort identity scope review (2026-10-31)

`Omega.Conclusion.ResiduePressureDropEscortRenyiFreeEnergy` builds successfully in a locked Lake run (3,092 jobs, exit 0). It proves a valid finite normalized power-sum identity from the supplied equations for `Sq`, `SqP`, `p`, and `nu`, using nonzero denominators. The parameter `m` is unused, and no pressure, escort probability law, Rényi entropy, or free-energy function is constructed. Retain the identity with that algebraic scope; the named interpretation needs a concrete model.


## Residue single-coordinate obstruction rank scope review (2026-10-31)

`Omega.Conclusion.ResidueSingleCoordinateObstructionRank` builds successfully in a locked Lake run (3,096 jobs, exit 0; deprecated import and `if_pos`/`if_neg` warnings). It correctly instantiates an imported cardinality result using the Fibonacci gcd identity. The underlying frequencies are defined as a finite arithmetic progression when the quotient is even and empty otherwise, so the cardinality is combinatorial for that defined set. No operator matrix, eigenspace, or independently constructed character basis is formalized; interpreting this as spectral rank needs a proved identification with an actual kernel/eigenspace.


## Residue slice single-orbit/double-slice rigidity review (2026-10-31)

`Omega.Conclusion.ResidueSliceSingleOrbitDoubleSliceRigidity` builds successfully in a locked Lake run (3,092 jobs, exit 0). From explicit rational equations for residues `E*m` and `E*(tau*m)` with `E,m ≠ 0`, it proves invariance under reciprocal reparametrization `(E*u, m/u)`, equality of slices when `tau=1`, and recovery of `tau` from their ratio and of `E,m` by back-substitution. This is valid rational identifiability on the declared structure; a residue-generating model is not built here.


## Resonance budget no-L2-envelope scope review (2026-10-31)

`Omega.Conclusion.ResonanceBudgetNoL2Envelope` builds successfully in a locked Lake run (3,092 jobs, exit 0). It proves a sequence-level finite-sum obstruction: a nonnegative sequence with unbounded partial square sums cannot be pointwise bounded by `K*w` when `K>0` and `w` has uniformly bounded partial square sums. No measure space or L² function-space object is defined, so retain the exact sequence formulation and treat the L² terminology as interpretation only.


## Resonance window arithmetic ledger scope review (2026-10-31)

`Omega.Conclusion.ResonanceWindow` builds successfully in a locked Lake run (3,092 jobs, exit 0). It contains fixed numeral inequalities, `Nat.fib 8 = 21`, `Nat.fib 9 = 34`, and the lcm/universal divisibility facts for 8 and 18. Its function contradiction only rules out a function taking two conflicting values at the same input. No resonance process, terminal-type map, or mod-6 sequence is defined; keep these as arithmetic lemmas unless a concrete model supplies that bridge.


## Resonance window infinite auditable primes scope review (2026-10-31)

`Omega.Conclusion.ResonanceWindowInfinitelyManyFullyAuditablePrimes` builds successfully in a locked Lake run (3,092 jobs, exit 0). It is a correct abstract finite-exception lemma: an abstract Prime predicate with a Euclid property, finitely many bad cases, and a Good implication yields a Good element outside every finite set. The prime notion and audit predicates are hypotheses, not concrete natural-number arithmetic criteria. A paper-facing arithmetic result needs those predicates instantiated and the finiteness/goodness facts proved.


## Reverse-KL single-frequency exclusivity scope review (2026-10-31)

`Omega.Conclusion.ReverseKLSingleFrequencyExclusivity` builds successfully in a locked Lake run (8,926 jobs, exit 0). It proves a substantive scalar rigidity result using the imported expression `-log(1-r^(2n)c²)` and the coefficient profile defined by divisibility: equality at a distinct positive frequency forces `c=0`, hence the profile equals the defined Haar coefficient function. The imported ‘infimum’ is just this explicit scalar formula; no probability measure or Fourier transform construction appears in these owners. Keep the theorem at that scalar scope.


## Reversible auxiliary-bits budget scope review (2026-10-31)

`Omega.Conclusion.ReversibleAuxBitsBudget` builds successfully in a locked Lake run (3,092 jobs, exit 0). It proves the finite encoding-capacity iff (`Fin b` injects into `Fin (2^k)` exactly when `b ≤ 2^k`), standard `Nat.clog` bounds/monotonicity, and numerical seeds. It defines no reversible computation, external budget minimization, or model `b(π)`, so the statement `κ(π)=ceil(log₂ b(π))` is not established by this file.


## RH-sharp Perron-purity scope review (2026-10-31)

`Omega.Conclusion.RhsharpForcesPerronPureQuotient` builds successfully in a locked Lake run (3,093 jobs, exit 0). It proves the scalar critical-slope identity at `eta=sqrt(rho)`, then uses supplied inequalities `b ≤ k_b ≤ survivingExcitations ≤ b-1` to contradict the locally defined integer-count predicate. No RH predicate, Perron operator, quotient, or spectral kernel is defined in this owner; the imported filter theorem also assumes the key bounds. The canonical scope is the conditional counting contradiction.


## Right-edge visible-phases support-function scope review (2026-10-31)

`Omega.Conclusion.RightEdgeVisiblePhasesSupportFunctionClosure` builds successfully in a locked Lake run (3,092 jobs, exit 0). It proves finite affine-envelope facts for a foldr maximum with zero baseline: midpoint convexity, branch attainment, conditional antitonicity, and pairwise branch intersection formulas. The first packaged conjunct is just the defining equation by reflexivity. No geometric support-function carrier is defined, so the canonical scope is the finite affine upper envelope unless a geometric realization is added.


## S4 40-block strongly regular parameters scope review (2026-10-31)

`Omega.Conclusion.S4FortyBlocksStronglyRegularParameters` builds successfully in a locked Lake run (3,092 jobs, exit 0). It proves a Diophantine uniqueness fact for `4λ+9μ=44` under bounds, and checks specified eigenvalue polynomial and multiplicity equations for constants declared in the file. It constructs no graph, group action, adjacency matrix, or strongly regular structure; the canonical scope is an arithmetic compatibility certificate, not a graph existence theorem.


## S4 universal boundary carrier nonprincipal polarization scope review (2026-10-31)

`Omega.Conclusion.S4UniversalBoundaryCarrierNonprincipalPolarization` builds successfully in a locked Lake run (3,093 jobs, exit 0). Non-principality is established by list arithmetic on the stipulated elementary-divisor list `[1,1,1,1,2,2,2,2,2]` and its triple concatenation. Its imported unique-carrier theorem is case analysis over hard-coded finite boundary/rank tables. No curve, degeneration, representation, abelian variety, Prym, or polarization is constructed, so the geometric interpretation is not established by these owners.


## Screen arithmetic shadow additive-linearization obstruction review (2026-10-31)

`Omega.Conclusion.ScreenArithmeticShadowAdditiveLinearizationObstruction` builds successfully in a locked Lake run (3,092 jobs, exit 0). It proves a genuine universal algebra fact: an idempotent binary operation cannot map homomorphically to coordinatewise addition on `Fin k → ℕ` except via the zero map, since evaluating at `(x,x)` gives `n=n+n`. The screen interpretation is not otherwise modeled. This can be generalized to any cancellative additive monoid.


## Screen atomic-value antitone scope review (2026-10-31)

`Omega.Conclusion.ScreenAtomicValueAntitone` builds successfully in a locked Lake run (3,093 jobs, exit 0). It proves generic set-function facts: monotonicity characterizes zero marginal, monotonicity plus unit-step growth characterizes one marginal, and submodularity yields diminishing marginal gains for nested sets. `InClosure` is defined as equality after insertion (zero gain); no concrete fixed-resolution screen or rank function is instantiated in this owner. The abstract finite-submodular result is substantive and reusable.


## Screen Joukowsky additive minimal externalization scope review (2026-10-31)

`Omega.Conclusion.ScreenJoukowskyAdditiveMinimalExternalization` builds successfully in a locked Lake run (3,094 jobs, exit 0). Its imported binary-audit theorem is a genuine finite counting bound: uniform fibers of size `2^β` and joint injectivity require at least β bits. The wrapper’s radial observable and reconstruction are both identity maps, `radialProfile` is unused, and the minimality conjunct is only `card (Fin k)=k`. No Joukowsky transform or profile-dependent externalization is formalized. Keep the finite audit theorem and separate the identity facts from the advertised radial application.


## Screen minimal exact-code constant-weight metric scope review (2026-10-31)

`Omega.Conclusion.ScreenMinimalExactCodeConstantWeightEvenMetric` builds successfully in a locked Lake run (3,093 jobs, exit 0). Its imported `IsBasis` is simply fixed cardinality, so the theorem concerns constant-weight finite subsets: equal-size sets have even symmetric-difference distance, and if distinct sets exist a one-element swap yields a pair at distance two. No matroid or screen-code constraints are formalized. Retain the constant-weight combinatorial result and qualify the stronger labels accordingly.


## Screen optimal audit Kolmogorov isometry scope review (2026-10-31)

`Omega.Conclusion.ScreenOptimalAuditKolmogorovIsometry` builds successfully in a locked Lake run (8,924 jobs, exit 0). For an arbitrary finite-dimensional F₂-linear map, it uses rank-nullity to obtain a noncanonical linear equivalence `V ≃ range(f) × F₂^r`, with `r=finrank ker(f)`, and proves minimality of `r` by dimension. The equivalence comes from `LinearEquiv.ofFinrankEq`; no metric, isometry, or audit observation model is defined. The canonical description is a noncanonical linear splitting plus a dimension lower bound.


## Screen phase object not-finitely-localizable scope review (2026-10-31)

`Omega.Conclusion.ScreenPhaseObjectNotFinitelyLocalizable` builds successfully in a locked Lake run (3,092 jobs, exit 0). It proves that the defined all-prime support for positive rank cannot be contained in any finite ledger, using infinitude of primes. The screen Pontryagin-dual abbreviation is unused; no groups, torsion quotients, localizations, or topological isomorphism invariant are constructed. The canonical conclusion is a set-support mismatch; a group non-isomorphism needs an explicit support-invariance theorem and group constructions.


## Screen realizability cycle-space obstruction scope review (2026-10-31)

`Omega.Conclusion.ScreenRealizabilityCycleSpaceObstruction` builds successfully in a locked Lake run (3,093 jobs, exit 0). The imported trace/cut-space identification is definitional: `fS` is defined as `graphCoboundary (toVertexLabel u)`. The codimension and surjectivity/forest conclusion assumes the dimension formula, surjectivity-dimension equivalence, and numerical forest equivalence as inputs, then derives the arithmetic. No graph chain complex, cycle space, incidence rank, or forest criterion is independently constructed. Treat the theorem as conditional packaging pending those graph-theoretic proofs.


## Screen zero-one local law/effective resistance scope review (2026-10-31)

`Omega.Conclusion.ScreenZeroOneLocalLawEffectiveResistance` builds successfully in a locked Lake run (3,092 jobs, exit 0). It assumes the rank and κ classification by cross/bridge status; three conclusion conjuncts are direct copies of those assumptions. The only derived fact is `κ=0 ↔ rankInc=0`, by contradiction in the cross case. No graph, network, electrical effective resistance, or derivation of the hypotheses is defined. Treat the result as conditional classification packaging.


## Screenphase connected quotient/no binary anomaly register scope review (2026-10-31)

`Omega.Conclusion.ScreenphaseConnectedQuotientNoBinaryAnomalyRegister` builds successfully in a locked Lake run (3,093 jobs, exit 0). It proves the standard general fact that a continuous map from a connected space to a discrete space is constant, hence cannot surject onto a nontrivial discrete space. No screenphase quotient or anomaly-register construction is present; the canonical scope is the general topological obstruction.


## Screenphase countably many nonisomorphic connected shadows scope review (2026-10-31)

`Omega.Conclusion.ScreenphaseCountablyManyNonisomorphicConnectedShadows` builds successfully in a locked Lake run (3,097 jobs, exit 0; existing warnings). It constructs countably many singleton prime ledgers and separates them using a predicate defined as difference of a stipulated exact-order count. The imported ‘surjects’ statement is only an injection `ℚ → ℚ^r` plus a constant circle-dimension definition; `FinitePrimeLocalization` is just `Finset ℕ`. There are no localized groups, surjective homomorphisms, or theorem that the count is invariant under group isomorphism. The supported result is combinatorial ledger separation, not countably many nonisomorphic connected quotients.

## Second-branch ninefold finite-generation label scope review (2026-10-31)

`Omega.Conclusion.SecondBranchNinefoldFieldNotGeneratedByFinitelyManyCubicFibers` passed its locked Lake build (8,928 jobs, exit 0). Its conclusion is a finite-index package of defined root-free mod-3 predicates, nonsquare integer signatures, inequality from a fixed integer, and P9 arithmetic/cardinality facts. The specialization “Galois group is S3” predicate is defined as the root-free predicate plus nonsquareness of a linear integer signature; no field extension or Galois group is constructed. The owner states no field generation relation and does not rule out generation by any finite family. Canonical scope: conditional finite-list arithmetic/predicate packaging, not a finite-generation obstruction.

## Semantic-equivalence undecidability reduction scope review (2026-10-31)

`Omega.Conclusion.SemanticEquivalenceUndecidable` passed its locked Lake build (3,092 jobs, exit 0). It proves the standard reduction-transfer result: a pointwise decider for the target binary relation would decide the source predicate via the supplied equivalence on embedded inputs and a fixed reference. Both source undecidability and the reduction are assumptions; this module defines no concrete language, evaluator, semantic-equivalence problem, reference program, or halting reduction. The canonical result is the abstract reduction theorem, not a concrete undecidability proof.

## Sequence-layer clarity-budget label scope review (2026-10-31)

`Omega.Conclusion.SequenceLayerConstantPeriodicDefectCannotReplaceClarityBudget` passed its locked Lake build (3,092 jobs, exit 0). It proves an elementary tail estimate: for fixed `delta ≥ 0`, eventual positivity of `n`, and `n` eventually above every real bound, `delta / n` is eventually at most each positive tolerance. No periodic defect, sequence-layer model, or clarity-budget structure appears in the statement. The canonical result is the real-sequence estimate; the stronger label is not represented in Lean.

## Sequence-layer finite-state/minimal-state counterexample scope review (2026-10-31)

`Omega.Conclusion.SequenceLayerFiberCountingMinimalStateNotPeriodicallyRecoverable` passed its locked Lake build (3,093 jobs, exit 0). The owner does provide an explicit collision: its periodic signature is constantly zero while its declared ambiguity values distinguish `false` and `true`. It also realizes the stipulated constant-one `fiberCount` with identity transition matrices and matching boundary vectors. This is a valid counterexample to recovery from that signature. However, `fiberCount` is defined constantly as one, the “minimal state count” is just `card (Fin 2)`, and no link from the transition system to an actual fiber-count semantics or lower bound on automaton states is proved. The result should be cited only at the level of the explicit definitions.

## Serrin thermodynamic-frontier affine scope review (2026-10-31)

`Omega.Conclusion.SerrinRealizableThermodynamicFrontierAffine` passed its locked Lake build (3,093 jobs, exit 0). It derives the normalized-image singleton from the imported mean-cone-collapse theorem and carries over the representative identity. The “pressure” is defined as a finite dot product, while its statement repeats that definition; the purported Legendre-Fenchel dual is defined as the indicator of `{v}`, and its theorem clause also unfolds definitionally. No supremum defining a convex conjugate or thermodynamic pressure duality is proved. The canonical content is the normalized-image consequence plus these definitional formulas.

## Serrin exact-screen collapse scope review (2026-10-31)

`Omega.Conclusion.SerrinSupportExactScreenCollapse` passed its locked Lake build (3,093 jobs, exit 0; linter warnings only). For the explicitly defined scalar ray in `ℝ²`, the theorem constructs a linear functional recovering its scale when the generator is nonzero; the zero-generator case is a singleton, so a coordinate projection is injective there too. Its normalized slice is `{ΓWK}` because normalization is defined by `ρ = 1`. The phrase “zero exact screen cost” is defined as subsingleton, so this is not a separate optimization theorem. No PDE-derived Serrin support object is constructed. The canonical scope is exact linear recovery and singleton normalization for a stipulated ray.

## Serrin–Wulff finite-moment discriminator scope review (2026-10-31)

`Omega.Conclusion.SerrinWulffNoFinitePolynomialFluxDiscriminator` passed its locked Lake build (3,095 jobs, exit 0; imported linter warnings). Its imported finite pair consists of distinct subsets of `{0,…,11}` with equal power moments at orders zero and one and unequal order-two moments. The theorem correctly shows that no finite output vector factoring through the order-at-most-one moment map can distinguish that pair. This does not exclude higher-order moments or arbitrary flux families lacking the stated factorization, and the proxies are not constructed from Wulff geometry. The canonical statement is the precise finite moment indistinguishability result.

## Serrin–Wulff positive gauge anomaly implication scope review (2026-10-31)

`Omega.Conclusion.SerrinWulffPositiveGaugeAnomalyExcludes` passed its locked Lake build (3,092 jobs, exit 0). Given an assumed zero value on terminal inputs and an assumed implication from `intrinsic` to zero value, it proves that a positive value excludes `intrinsic`, by contradiction. These are the whole mathematical inputs; no gauge anomaly or Serrin model is constructed. Classified as a valid assumption-driven implication, not an independently established geometric exclusion.

## Serrin–Wulff volume-normalization ledger scope review (2026-10-31)

`Omega.Conclusion.SerrinWulffVolumeNormalizationCutsLedgerObstruction` passed its locked Lake build (3,098 jobs, exit 0). The normalized carrier is defined to be `Unit`; the cardinality, finite-ledger embedding, and unique factorization through a quotient of `Unit` then follow from that definition. There is no normalization map from the prime-register scale family or proof that the original family factors through this singleton. The imported finite-rank non-embedding result remains a separate theorem. The owner establishes singleton/quotient algebra, not that volume normalization removes the original ledger obstruction.

## Single-collapse Choi-rank parameterization scope review (2026-10-31)

`Omega.Conclusion.SingleCollapseChoiRankOneParameterization` passed its locked Lake build (3,094 jobs, exit 0; one style warning). For a finite map whose distinguished fiber has size `t` and all other fibers have size at most one, it proves the `q`-collision moment formula `t^q + (|Ω| - t)` for `q ≥ 2`. The imported Choi-rank theorem identifies this moment with the rank in its explicitly defined scalar direct-sum projector model. The fiber profile is assumed, and no independent classification of channels/folds or richer channel construction is included. Canonical scope: conditional finite fiber-counting and projector-rank identity.

## Single-cube edit rigidity scope review (2026-10-31)

`Omega.Conclusion.SingleCubeEditRigidity` passed its locked Lake build (8,927 jobs, exit 0). From the discrete isoperimetric lower bound, `Dist = F`, `|U △ V| = N`, and `n ≥ 2`, it correctly proves that `Dist < 2n` implies `U = V`, and that equality `Dist = 2n` with `U ≠ V` forces `|U △ V| = 1`. The imported isoperimetric data structure supplies the geometric counting inequalities as fields; the owner does not construct `U,V` as actual polycubes or derive the distance identifications. Canonical scope is conditional finite-set rigidity from the stated bound.

## Single-register Chebotarev completeness scope review (2026-10-31)

`Omega.Conclusion.SingleRegisterChebotarevCannotBeCompleteForDoubleBranchArithmetic` passed its locked Lake build (8,926 jobs, exit 0). It gives a concrete finite projection collision: every certificate reading only the `Fin 10` coordinate identifies `(0,0)` and `(0,1)` despite their distinct `Fin 9` coordinates. This validly shows that this projection is not injective. Its imported direct-product predicate is defined from unequal integer labels and stipulated factorials; its “Chebotarev densities” are rational formulas checked arithmetically. No number fields, Galois groups, Frobenius sets, or Chebotarev density theorem are constructed. Canonical scope: finite projection noninjectivity and arithmetic bookkeeping, not a number-theoretic completeness theorem.

## Single Rényi-moment coarsening rigidity scope review (2026-10-31)

`Omega.Conclusion.SingleRenyiRigidityForCoarsening` passed its locked Lake build (3,092 jobs, exit 0). For finite sets and deterministic maps `Ω → X → Y`, equality of the unweighted `q`th fiber-cardinality moments for `q ≥ 2` forces the coarsening map to be injective on occupied fibers. It then proves equality of every truncated fiber-count sum. This is a substantive finite counting result, not a general Rényi entropy theorem for arbitrary distributions or stochastic channels. Canonical scope: rigidity of deterministic finite coarsenings under equality of one power moment.

## Singular-ring prime composition criterion scope review (2026-10-31)

`Omega.Conclusion.SingularRingPrimeCompositionIrreducibility` passed its locked Lake build (3,094 jobs, exit 0). For its defined maps `z ↦ z^n`, it proves composition corresponds to multiplication of indices and equality of maps forces equal indices; therefore primality of `n ≥ 2` is equivalent to the absence of a factorization with both indices at least two. This is a valid arithmetic/composition criterion. The “singular ring” data only stores a normalization constant and the maps are monomials with denominator one; no singular ring or nontrivial rational-map geometry is constructed.

## Size-bias/visible-anomaly logical-independence scope review (2026-10-31)

`Omega.Conclusion.SizebiasVisibleAnomalyLogicalIndependence` passed its locked Lake build (3,093 jobs, exit 0). On a one-element index set, the explicit zero and one functions witness each direction of non-implication between zero total visible anomaly and zero total size-biased residual. This is a valid finite countermodel for the predicates as defined, which are sums of natural-valued functions. No process generating either quantity is formalized. Canonical scope: logical independence in a one-point finite model.

## Squarefree crowding/phase-cell theorem scope review (2026-10-31)

`Omega.Conclusion.SquarefreeCrowdingKphase` passed its locked Lake build (3,093 jobs, exit 0; one imported style warning). Its theorem is the finite pigeonhole principle for an arbitrary map `Fin (2^m) → Fin (Q^k)` when `Q^k < 2^m`. The Boolean-cube and torus-cell constructions are represented only by their cardinality formulas; no squarefree-ledger encoding, torus partition, or phase map is built. Canonical scope: finite collision under a cardinality inequality.

## Stokes-extension obstruction certificate scope review (2026-10-31)

`Omega.Conclusion.StokesExtensionObstructionCertificate` passed its locked Lake build (3,092 jobs, exit 0). From the field `phaseSamplingUpperBound < sampledImageValue`, it proves that the proposition `sampledImageValue ≤ phaseSamplingUpperBound` is impossible. This is a valid order-theoretic contradiction, but the alleged realizability bound is merely defined and not derived from a Stokes theorem; no extension, filling object, or sampling operation is formalized. Canonical scope: conditional strict-inequality contradiction.

## Strict-gap/S₂ Schur-variance collapse scope review (2026-10-31)

`Omega.Conclusion.StrictGapForcesNonhookSchurVariance` passed its locked Lake build (3,095 jobs, exit 0). In the two-element `S₂` index model, nonnegativity, a positive gap, and the explicit assumption that positive gap kills the split channel imply that channel vanishes; the imported exact variance decomposition then yields zero centered variance. The strict-gap implication is assumed, not derived from a spectral gap theorem. The defined `isNonhook` predicate is false on both indices, making the final filtered sum identically zero. `hNonneg` is used by the helper. Canonical scope: conditional S₂ variance collapse, not general Schur or spectral-gap rigidity.

## Subcritical isotropic-moment certificate scope review (2026-10-31)

`Omega.Conclusion.SubcriticalIsotropicMomentCertificatesIncompleteAcrossResolutions` passed its locked Lake build (8,931 jobs, exit 0). The theorem says that any composite of maps `Fin (2^(mn)) → Fin r_m → Y_m` has a collision when `r_m < 2^(mn)`, by finite-cardinality pigeonhole. Its postprocessing and moment map are arbitrary. The imported boundary-Gödel geometric model defines `DyadicPolycube` as `Unit` and its code/moment maps constantly, so no actual isotropic-moment construction or resolution family is present. Canonical scope: finite injectivity obstruction under a strict cardinality inequality.

## Sublinear Toeplitz audit impossibility scope review (2026-10-31)

`Omega.Conclusion.SublinearToeplitzAuditImpossible` passed its locked Lake build (3,092 jobs, exit 0). It proves that three supplied eventual inequalities—`detect ≤ audit`, `lower ≤ detect`, and `audit < lower`—are inconsistent at a common tail index, so `complete` is false. No Toeplitz operator, audit process, or sublinear growth condition is formalized. Canonical scope: an abstract asymptotic order contradiction.

## Sync-kernel single-coordinate identity scope review (2026-10-31)

`Omega.Conclusion.SyncKernelFiniteLengthSingleCoordinate` passed its locked Lake build (3,092 jobs, exit 0). It verifies the rational identity `Z(u)=u²Z(u⁻¹)` for `Z(u)=1+u+u²`, then proves `(r⁻¹)² Z(r²)=(r+r⁻¹)²−1` for nonzero `r`. The uniqueness of `Q` is imposed directly by the conjunct `∀ s, Q s = s²−1`, so that part follows immediately from the stipulated formula. No sync-kernel object is constructed. Canonical scope: two elementary rational identities and definitional uniqueness.

## Sync-kernel palindrome and tower-defect scope review (2026-10-31)

`Omega.Conclusion.SyncKernelPalindrome` passed its locked Lake build (3,098 jobs, exit 0). Its substantive theorem proves that, for finite `Z` and a nonnegative ordered-pair count, every tower defect vanishes exactly when `fiberSize` is constant on each fiber of `h`. The other declarations check two entries of a fixed matrix square and small arithmetic equalities; the “Edgeworth” checks are integer/natural arithmetic, including natural-number division. No general palindrome, cumulant, Edgeworth expansion, or sync-kernel object is established. Canonical scope: finite fiber-uniformity criterion plus isolated arithmetic/matrix seeds.

## Visible dual-scale audit threshold scope review (2026-10-31)

`Omega.Conclusion.VisibleCompleteDefectAuditDualScaleThreshold` passed its locked Lake build (3,111 jobs, exit 0; dependency warnings). It proves conditional natural-number arithmetic for the definitions `reconstruction feasible ↔ 2κ ≤ N` and `display feasible ↔ C·hminInv ≤ N`: the stated strict lower thresholds are infeasible, and both predicates hold at `max (2κ) (C·hminInv)`. The visible horizon imported here is simply `max (2κ) (2κ)`. The theorem does not establish minimality of the joint maximum or construct either audit task; the negative-direction lower exclusion only covers `N ≤ c·hminInv`. Canonical scope: threshold arithmetic for stipulated predicates.

## Visible strictification obstruction-rank scope review (2026-10-31)

`Omega.Conclusion.VisibleStrictificationFiniteObstructionRank` passed its locked Lake build (3,092 jobs, exit 0). Given three natural-number equalities to `κ`, it derives equality among the indices by transitivity and returns the supplied `noSecondFiniteObstruction` proposition unchanged. No spectral, Toeplitz, Blaschke, or obstruction-rank constructions are defined. Canonical scope: equality transitivity and assumption packaging.

## Wallis finite-additive-ledger theorem scope review (2026-10-31)

`Omega.Conclusion.WallisFiniteAdditiveLedgerImpossible` passed its locked Lake build (3,092 jobs, exit 0). Its substantive theorem proves any `f : ℕ → ℕ` satisfying `f 1 = 0` and `f (mn)=f m+f n` is noninjective: comparing powers of 2 and 3 gives equal values, so injectivity would equate an even power with an odd power. This is a valid multiplicative-to-additive noninjectivity result, but the codomain `ℕ` is infinite, so it is not a finite-codomain impossibility theorem. The “Wallis factor coverage” is only the even/odd decomposition of positive naturals; no distinct Wallis skeleton is formalized.

## Wallis product completion-threshold scope review (2026-10-31)

`Omega.Conclusion.WallisProductCompletionThreshold` passed its locked Lake build (3,092 jobs, exit 0). It repeats the valid noninjectivity proof for a multiplicative-to-additive map `ℕ → ℕ` with `f 1 = 0`. Its Boolean construction witnesses that any stipulated finite prefix can be followed by a first differing bit at index `2κ−1` (with natural subtraction). This is a prefix witness only: no CMV/Toeplitz operator, completion procedure, or link from an operator audit to the Boolean sequence is formalized. Canonical scope: an elementary monoid obstruction and explicit prefix nonuniqueness.

## Weak-coherence chain/tree gap scope review (2026-10-31)

`Omega.Conclusion.WeakCoherenceChainTreeGap` passed its locked Lake build (3,093 jobs, exit 0; deprecated real import and unnecessary-`simpa` warnings). Under the structure’s assumed bounds `κ(d) ≤ κ(1)` for `d ≥ 1` and `κ(d) ≤ κ(2)` for `d ≥ 2`, it proves a componentwise score bound for finite edge-length functions and the exact formal difference `κ(1) - κ(2) = A/(2r)`. The “trees” are only functions `Fin (vertexCount−1) → ℕ`; there is no graph incidence, connectivity, spanning-tree, or optimization model. Canonical scope: a finite edge-list inequality conditional on its kernel bounds.

## Weighted free commutative monoid metric rigidity scope review (2026-10-31)

`Omega.Conclusion.WeightedFreeCmonMetricRigidity` passed its locked Lake build (3,095 jobs, exit 0; unnecessary-`simpa` warnings only). The owner fixes the carrier to `ℕ`, radius `φx`, and distance `φ|x−y|`; within that model it proves the unique center with injective distance profile is zero, all bijective self-isometries are identity, and each pair has a unique sum with additive radius. Canonical scope: one-generator weighted metric rigidity, not a classification for arbitrary weighted free commutative monoids.

## Weighted screen completion/MST theorem scope review (2026-10-31)

`Omega.Conclusion.WeightedScreenCompletionMST` passed its locked Lake build (3,092 jobs, exit 0). The finite-set result is a valid conditional equivalence: `hPrune` supplies a feasible tree subset with no greater cost, and `hDelete` says every feasible non-tree set has a deletable element; from these assumptions it derives MST optimality and inclusion-minimality conclusions. Neither structural hypothesis is proved, and the file defines no graph, cycle, quotient, or pruning algorithm. Canonical scope: an abstract finite-set optimality lemma conditional on pruning and deletion properties.

## Weighted synchronization odd-prime staticization scope review (2026-10-31)

`Omega.Conclusion.WeightedSyncOddprimeUnitrootStaticization` passed its locked Lake build (3,092 jobs, exit 0). The divisibility conclusion follows from the tail premise by exponent comparison and transitivity; `A = -A` over `ℤ` gives `A = 0`. The prime and oddness hypotheses are unused, and no unit-root or weighted synchronization structure appears. Canonical scope: divisibility propagation plus integer self-negation.

## Window6 F8/F9 channel orthogonality scope review (2026-10-31)

`Omega.Conclusion.Window6BoundaryF8F9ChannelOrthogonality` passed its locked Lake build (3,111 jobs, exit 0; existing dependency deprecation/style warnings). This owner packages the imported finite-boundary fiber constancy and parity nonmeasurability result, plus terminal offset/alias equalities by reflexivity. Its substance resides in the imported source modules; this file adds no general channel orthogonality theorem. Canonical scope: the stated finite boundary separation package.

## Window6 faithful connected detector impossibility scope review (2026-10-31)

`Omega.Conclusion.Window6BoundaryFaithfulConnectedDetectorImpossible` passed its locked Lake build (3,092 jobs, exit 0). Its proof is exactly the arithmetic contradiction between `components = 1` and `4 ≤ components`. No detector, faithfulness property, connected graph, or component construction is formalized. Canonical scope: inconsistent natural-number constraints.

## Window6 boundary parity non-completability scope review (2026-10-31)

`Omega.Conclusion.Window6BoundaryParityNeverAnomalyComplete` passed its locked Lake build (3,092 jobs, exit 0). The theorem assumes dimensions 21 and 3 and the implication that completeness would force `21 ≤ 3`, then derives non-completability by arithmetic. The extension-count equality is passed through unchanged; there is no anomaly signature or extension construction. Canonical scope: a conditional contradiction from stipulated dimensions.

## Window6 parity nonmeasurability from F8 scope review (2026-10-31)

`Omega.Conclusion.Window6BoundaryParityNotMeasurableFromF8` passed its locked Lake build (3,092 jobs, exit 0). On the explicit finite carrier `Fin 3 × Bool`, the defined F8 readout is constant and canonical parity is the second coordinate, so parity cannot factor through that readout; the two sheets over any fixed fiber provide the contradiction. Canonical scope: a valid finite factorization obstruction, not a formal model of an external F8 channel.

## Window6 boundary subspace projector obstruction scope review (2026-10-31)

`Omega.Conclusion.Window6BoundarySubspaceNoAutEquivariantProjector` passed its locked Lake build (3,092 jobs, exit 0). Its abstract argument is valid: the range of an equivariant map is invariant, conflicting with the supplied boundary point moved outside. Idempotency is an unused extra hypothesis; no concrete Window6 space, automorphism group, or boundary representation is instantiated. Canonical scope: range invariance for equivariant maps and the resulting abstract obstruction.

## Window6 Z6 global free-extension scope review (2026-10-31)

`Omega.Conclusion.Window6BoundaryZ6NoGlobalFreeExtension` passed its locked Lake build (3,132 jobs, exit 0; imported deprecation/style warnings). The extension predicate itself includes `∃ m, 21*m=64`; the theorem refutes that arithmetic condition via the imported local/global mismatch theorem. No free group action or concrete ambient orbit partition is constructed. Canonical scope: impossibility of the stipulated orbit-cardinality equation.

## Window6 center characteristic rigidity scope review (2026-10-31)

`Omega.Conclusion.Window6CenterCharacteristicRigidity` passed its locked Lake build (3,092 jobs, exit 0; `push_neg` deprecation warnings). It proves that an additively closed subset of `(ZMod 2)^8` containing zero and invariant under every linear endomorphism is either `{0}` or the whole space, using a rank-one map. Invariance under all endomorphisms (including noninvertible maps) is stronger than invariance under `GL(8,2)`; the file does not establish that an external center/action has this property. Canonical scope: the stated finite-dimensional invariant-subspace dichotomy.

## Window6 choice-free parity anchor scope review (2026-10-31)

`Omega.Conclusion.Window6ChoicefreeParityAnchorIsolated` passed its locked Lake build (3,092 jobs, exit 0). Given the stipulated iff and three finite `Delta` tables, it proves uniqueness of the nonzero table entry at index 6 and failure of uniqueness at indices 7 and 8. It does not formalize a general parity construction or a comparison involving choice. Canonical scope: the supplied finite-table classification.

## Window6 cyclic escort dual zero-temperature scope review (2026-10-31)

`Omega.Conclusion.Window6CyclicEscortDualZeroTemp` passed its locked Lake build (3,092 jobs, exit 0; unnecessary sequence-focus warnings). It proves limits `1/9` and `−1/5` for two explicitly defined real sequences with rational-power terms, plus nonvanishing of the positive-branch sequence for positive indices. No cyclic shell, escort operator, or finite model is constructed. Canonical scope: limits of the displayed scalar sequences.

## Window6 endpoint atom and 2-primary ledger scope review (2026-10-31)

`Omega.Conclusion.Window6EndpointAtomNotAdditiveThroughTwoPrimaryLedger` passed its locked Lake build (8,930 jobs, exit 0). The core result is general and valid: every additive homomorphism from an exponent-two additive group to `ℝ` vanishes, since `2 f(g)=0` and `2≠0`. The endpoint consequence follows directly. Imported parity/anomaly theorems are bound then cleared and do not contribute; no extra-axis construction is formalized. Canonical scope: torsion-to-torsion-free homomorphism vanishing.

## Window6 first scale-jump gate scope review (2026-10-31)

`Omega.Conclusion.Window6FirstScaleJumpGateForcing` passed its locked Lake build (3,092 jobs, exit 0). It defines fiber-size values 2, 3, 3 at indices 6, 7, 8 and verifies finite arithmetic for binary readout capacity and `Nat.clog 2`. No fibers, readout map, or gate-forcing mechanism is constructed. Canonical scope: finite table and capacity threshold arithmetic.

## Window6 inversion/linear/statistical triple scope review (2026-10-31)

`Omega.Conclusion.Window6InversionLinearStatisticalTripleSeparation` passed its locked Lake build (8,963 jobs, exit 0; dependency deprecation/style warnings). Its theorem packages imported histogram values, the imported no-linear-factorization result, and an imported capacity/InfoNCE equivalence. No new implication or statistical inversion argument relates these conjuncts. Canonical scope: conjunction of the imported statements.

## Window6 local-Morita/global-orbitability scope review (2026-10-31)

`Omega.Conclusion.Window6LocalMoritaTrivialGlobalNonorbitizable` passed its locked Lake build (3,092 jobs, exit 0). The stipulated fiber sizes 2 and 3 refute a common fiber cardinality, hence both defined constant-size orbit/coset predicates. Positivity and “matrix block” witnesses are supplied as data fields; positivity alone is not contractibility or Morita equivalence. No topology or group action is modeled. Canonical scope: heterogeneous finite cardinalities obstruct a constant-size partition.

## Window6 long-root/projective short-root defect scope review (2026-10-31)

`Omega.Conclusion.Window6LongRootProjectiveShortRootDefect` passed its locked Lake build (3,092 jobs, exit 0). It derives comparisons from six supplied values for each of two `ℕ`-valued functions: a period-three equality for the long table, one short-table inequality, and two equalities. No root system, projective action, or defect construction is formalized. Canonical scope: finite table arithmetic under stipulated values.

## Window6 low-order tensor vacuum scope review (2026-10-31)

`Omega.Conclusion.Window6LowOrderTensorVacuum` passed its locked Lake build (3,093 jobs, exit 0; one imported tactic-style warning). It obtains the parameter 21 from an imported certificate and proves bounded nondivisibility facts. The named “vanishing” predicates are defined as nondivisibility; this owner constructs no tensor representation, invariant tensor, equivariant map, or center action. Canonical scope: bounded arithmetic nondivisibility conditional on the imported dimension certificate.

## Window6 Markov/topological hidden-channel scope review (2026-10-31)

`Omega.Conclusion.Window6MarkovTopologicalHiddenChannelSeparation` passed its locked Lake build (3,092 jobs, exit 0). On `Fin 2`, the defined F8 and F9 channels are constant false and constant true, so they differ. No Markov chain, topology, or channel extraction is modeled. Canonical scope: separation of two constant Boolean functions on a finite carrier.

## Window6 maximal-degree Weyl-breaking scope review (2026-10-31)

`Omega.Conclusion.Window6MaxdegWeylBreaking` passed its locked Lake build (3,098 jobs, exit 0). The explicit subset of `ℕ` has size 9 and intersects the declared short/long intervals in 5 and 4 coordinates, violating the predicate that each interval be wholly included or excluded. The “orbits” are intervals; no Weyl group action or root system is defined. Canonical scope: finite subset counterexample to an orbit-union predicate.

## Window6 exact-replay symmetry-breaking scope review (2026-10-31)

`Omega.Conclusion.Window6MinimalExactReplaySymmetryBreaking` passed its locked Lake build (3,092 jobs, exit 0). It is propositional contraposition from the assumed implication `ExactReplay → BoundaryEquivariant → FourValueBoundaryCompanion` and the assumed negation of that companion. No replay or symmetry structure is formalized. Canonical scope: the conditional logical implication only.

## Window6 moment/Prony rank claim semantic audit (2026-10-31)

`Omega.Conclusion.Window6MomentTowerPronyRankCompression` passed its locked Lake build (3,094 jobs, exit 0; imported unnecessary-`simpa` warning). The ordinary and binary finite exponential-sum formulas, recurrences, Hankel-to-Gram entry identities, and determinant witnesses are genuine algebraic results. However, the “exact Hankel rank” conjunct is not a matrix-rank statement: `fixedResolutionCollisionExactHankelRank` is defined using a data structure whose fields assume the rank and recurrence order equal the atom count, and the imported Prony theorem simply returns those fields. Canonical replacement scope: finite moment formulas/recurrences and Gram factorization; actual Hankel rank requires a matrix carrier and rank proof.

## Window6 inverse-limit cylinder parity lift scope review (2026-10-31)

`Omega.Conclusion.Window6NoInverseLimitCylinderParityLift` passed its locked Lake build (3,092 jobs, exit 0). The theorem simply applies the supplied obstruction implication to refute an object satisfying four predicates. Those predicates are uninterpreted, and the file constructs no inverse system, cylinder maps, involution, or parity lift. Canonical scope: consequence of an assumed obstruction.

## Window6 no-linear-factorization scope review (2026-10-31)

`Omega.Conclusion.Window6NoLinearFactorization` passed its locked Lake build (3,131 jobs, exit 0; imported deprecation/style warnings). The conclusion module forwards to an imported proof that nonzero histogram entries at sizes 2, 3, and 4 contradict a uniform coset-fiber-size predicate. It does not itself construct the fold map; the histogram-to-fold connection must be checked at its owner. Canonical scope here: nonuniform positive fiber sizes obstruct the defined uniform-coset model.

## Window6 root-system/free-quotient scope review (2026-10-31)

`Omega.Conclusion.Window6NotRootSystemNotFreeQuotient` passed its locked Lake build (3,135 jobs, exit 0; imported deprecation/style warnings). The “finite reduced root system cardinality” predicate is defined as `Even`; excluding cardinality 21 and 18+3 is then elementary parity arithmetic, not a theorem about a constructed root system. The free-orbit/coset clauses are imported, with no map from a group action or root system to the 21-point carrier. Canonical scope: parity arithmetic under the stated definition plus imported obstructions.

## Window6 odd-prime affine/local/coarse translation scope review (2026-10-31)

`Omega.Conclusion.Window6OddprimeAffineLocalCoarseTranslation` passed its locked Lake build (3,092 jobs, exit 0). It returns the three supplied predicate equivalences unchanged and derives the stipulated membership/nonmembership facts at 23 and 571. There is no affine map, local/coarse object, or odd-prime construction. Canonical scope: predicate restatement plus finite arithmetic consequences.

## Window6 one-axis screen half-blind rigidity scope review (2026-10-31)

`Omega.Conclusion.Window6OneaxisScreenHalfblindRigidity` passed its locked Lake build (3,092 jobs, exit 0). Its theorems rewrite supplied values 32, 64, and 12 as arithmetic equalities. No screen, one-axis observation map, replay process, or minimality/rigidity argument is formalized. Canonical scope: arithmetic restatement of stipulated values.

## Window6 Reynolds average / zero-mode projector scope review (2026-10-31)

`Omega.Conclusion.Window6ReynoldsAverageZeroModeProjector` passed its locked Lake build (3,092 jobs, exit 0). This is a substantive explicit finite dependent-sum model: fiberwise rational averaging is idempotent with fixed points exactly the fiber-constant observables, the microstate norm descends to a weighted visible norm, and a cubic polynomial selects the same average for fiber sizes 2, 3, 4. It is not a group Reynolds operator or a constructed window process. Canonical scope: finite partition averaging and its projection/norm identities.

## Window6 short-root defect nilpotency scope review (2026-10-31)

`Omega.Conclusion.Window6ShortRootDefectNilpotent` passed its locked Lake build (3,092 jobs, exit 0). For a concrete 6×6 integer matrix equal to the stated two matrix units, it proves `N² = −4 E₄₂ ≠ 0` and `N³ = 0`, a genuine nilpotency-index-three example. The root-theoretic “short-root” interpretation is not formalized. Canonical scope: explicit matrix nilpotency calculation.

## Window6 three-moment spectrum inversion scope review (2026-10-31)

`Omega.Conclusion.Window6ThreeMomentSpectrumInversion` passed its locked Lake build (3,137 jobs, exit 0; imported/style warnings). The exact inversion of three moments on fixed support `{2,3,4}`, the recovery `(8,4,9)` from supplied moments `(21,64,212)`, and the congruence characterization for integral recovered weights are genuine arithmetic results. The support and moments are inputs; the file does not identify an unknown support among arbitrary spectra. Canonical scope: inversion and integrality for the fixed three-atom support.

## Window6 topological closure / anomaly closure scope review (2026-10-31)

`Omega.Conclusion.Window6TopologicalClosureNotAnomalyClosure` passed its locked Lake build (3,151 jobs, exit 0; imported deprecation/style warnings). Its proof assembles imported orbit, coset, boundary, and completion-cardinality facts with `64 − 21 = 43`. The paper-labeled declaration is a proposition-valued `def`, while a separate helper proves it. No mathematical comparison between topological closure and anomaly closure is stated or derived. Canonical scope: conjunction of imported obstructions and finite cardinality data.

## ZG density / stationary finite-order Markov scope review (2026-10-31)

`Omega.Conclusion.ZGDensityNotStationaryFiniteOrderMarkov` passed its locked Lake build (494 jobs, exit 0). The result follows directly from a data field stating that every positive rational `c` fails to be the transition value at some index. The declared Markov order is unused; no transition law, process, or density is constructed. Canonical scope: a sequence with no persistent positive constant value cannot satisfy the defined constant-transition predicate.

## ZG finite-shadow / Euler-factorization scope review (2026-10-31)

`Omega.Conclusion.ZGFiniteShadowCompletenessDoesNotImplyEulerFactorization` passed its locked Lake build (3,096 jobs, exit 0). It combines transition recovery from an assumed cylinder-factor equation and positive zero-state marginals with a concrete nearest-neighbor covariance defect `−p_i p_j π_i π_j` under positivity assumptions. This proves that the specified pair shadow differs from the product of the two specified prime shadows. No Euler product or general factorization principle is formalized. Canonical scope: this finite recovery identity and this explicit nonmultiplicativity witness.

## ZG certificate/shadow local-dimension blindness scope review (2026-10-31)

`Omega.Conclusion.ZGNoNontrivialLocalDimensionPredicateFromFiniteCertificate` passed its locked Lake build (8,926 jobs, exit 0). The Boolean-classifier impossibility follows from the realization field: two inputs can share certificate and shadow while taking opposite values of the target local-dimension predicate. This is a valid conditional observational-collision theorem; the file does not construct a concrete process or certificate model.

## ZG positive-entropy finite-state conclusion scope review (2026-10-31)

`Omega.Conclusion.ZGPositiveEntropyFinitestateObstruction` passed its locked Lake build (3,092 jobs, exit 0). The conclusion follows by applying the supplied incompatibility predicate to the assumed positive-dimension property and the zero-dimension property transported along a hypothetical equality. This is a conditional abstract implication; no entropy or measure construction is present.

## ZG prime-pair shadow correlation scope review (2026-10-31)

`Omega.Conclusion.ZGPrimePairShadowCorrelationLaw` passed its locked Lake build (3,092 jobs, exit 0). Under explicit divisor-cylinder normalization and positive marginal assumptions, it derives the prime and pair rational shadow formulas, covariance defect, and strict negativity when the pair marginal is zero. Canonical scope: this finite rational identity under those assumptions, not a general prime-pair theorem.

## ZG nearest-neighbor nonmultiplicativity scope review (2026-10-31)

`Omega.Conclusion.ZGShadowNonmultiplicativityNearestNeighbor` passed its locked Lake build (3,093 jobs, exit 0). It specializes the verified prime-pair rational identity to a zero pair marginal and derives inequality from the product of prime shadows using the strict covariance sign. This is an imported finite corollary, with no separate process model.

## Zero-mean residue test detection scope review (2026-10-31)

`Omega.Conclusion.ZeroMeanResidueTestsCompleteDetection` passed its locked Lake build (3,093 jobs, exit 0; deprecated `Mathlib.Data.Complex.Basic` import warning). The finite proof uses a basis weight at each nonzero residue to isolate that Fourier coefficient, establishing equivalences with vanishing modes and equal residue limits. The defined q-power factorization predicate is precisely the same nontrivial-mode condition. Canonical scope: this explicit finite Fourier detection model.

## Zeta audit versus synchronization decoder scope review (2026-10-31)

`Omega.Conclusion.ZetaCompleteAuditNotSyncComplete` passed its locked Lake build (3,092 jobs, exit 0). The supplied package makes spectral observations equal at levels 3 and 4 while synchronization budgets are 2 and 3, so no decoder of spectral data alone can recover the budget at all levels ≥3. This is a valid conditional indistinguishability argument; it does not construct a zeta spectrum or synchronization process.

## Fresh tracked-tree candidate delta (2026-10-31)

A fresh tracked-worktree run of `tools/quality/counterexample_inventory.py` scanned 28,789 Lean files (zero read errors; seven skipped paths) and emitted 13,363 lexical declaration rows. Comparing against the prior 587-file ledger found 4,726 candidate files not represented there, most from broad negative-boundary matches. I filtered to repo-owned files with explicit obstruction or identifiability categories: 229 obstruction and 89 identifiability declaration rows, across 195 files (318 declarations total). These are now recorded with hashes and declaration locations as `source_candidate_unreviewed`; no semantic or proof status is inferred. The 11,062 generic negative-boundary rows remain lexical noise pending a stronger filter, and the broad inventory objective remains open.

## G2 quotient representative collision and alignment-package refutation (2026-10-31)

The owner `Algebra.Zorn.G2QuotientCollisionAudit` proves that indices 24 and 45 have the same image in the quotient by the concrete unipotent subgroup, while their residual coordinates are distinct; hence the `Fin 189` quotient representative map is not injective. I added two consequences: neither the abstract nor concrete `FactorizationAlignmentSystem` in `G2FactorizationAlignmentCertificate` can exist, because its fields imply injectivity. The canonical equality test remains `G2NativeQuotientRepresentative.quotientRepresentative_eq_iff`, reducing equality to subgroup membership of the representative difference. The focused locked build passed (9,004 jobs). This is specific to the concrete 189-entry table; it does not establish a general quotient-cardinality claim.

## G2 cell-two residual-coordinate collision and paired replacement (2026-10-31)

`G2ResidualCoordinateCellTwoBoundary` proves that the left-factor residual word has the same value at distinct indices 170 and 185, both in orbit cell 2, and therefore is not injective on that cell. The canonical owner-level replacement uses both gap-witness factors: `G2ResidualPairCoordinateCellTwo.residualPair_injective_on_cell_two` proves injectivity on cell 2, while `G2GapResidualPairCellAssembly.gapResidualPair_injective_on_cell` proves it on every cell. The counterexample owner passed its locked build (8,992 jobs); the all-cell paired replacement passed (9,016 jobs). The residual word remains valid as a one-sided coordinate; only its injectivity claim is refuted.

## G2 explicit root-candidate family overlap (2026-10-31)

`G2TwoExplicitGenerators.candidateRootFamily_not_injective` is an explicit collision: candidate labels 1 and 3 at `true` give the same automorphism, because `cycleConjugatedShort_one_eq_long_zero` identifies the short-family element at index 1 with the long-family element at index 0. This refutes any interpretation of the six labels as six distinct root elements. The owner already calls them candidates and explicitly disclaims distinctness or a completed BN-pair; its precise positive statement is that `cycleConjugatedLong` is injective. Downstream subgroup constructions use the generated set and membership lemmas, not a six-element distinctness theorem. The focused locked build passed (3,095 jobs, exit 0; imported unused-tactic warnings). This is a witnessed overlap, not a refutation of the generated subgroup or of the separately proved lower bound on its cardinality.

## G2 cell-one quotient two-class classification (2026-10-31)

`G2CellOneQuotientRelation` proves a second exact quotient collision in cell 1: indices 73 and 178 have the same coset, alongside the previously recorded 24/45 collision. All four cross-pairs are distinct, and `cell_one_quotient_eq_iff_same_pair` gives the exact equality relation on this cell; its quotient image has exactly two values. The canonical alternative to injectivity is this cell-scoped two-class classification. The 24/45 collision also refutes the generic and concrete global residual-alignment packages in this owner. The statement is specific to cell 1 and the finite 189-entry table. Focused locked build passed (9,023 jobs, exit 0; imported linter warnings).

## G2 global quotient-injectivity route is conditional (2026-10-31)

`G2GAPFlagWitnessAssembly` gives three sufficient-condition theorems for quotientRepresentative injectivity. They require explicit cross-cell disjointness and within-cell residual alignment plus residual-coordinate injectivity; the matrix form also requires an explicit matrix-separation premise. The file does not prove these global premises for the concrete 189-entry quotient table. The already verified 24/45 cell-one collision refutes unconditional injectivity and rules out the associated global alignment package. Canonical scope: keep these as conditional implications; do not promote them to a concrete global injectivity theorem. Focused locked build passed (9,013 jobs, exit 0; imported linter warnings).

## G2 idempotent-to-isotropic-point cardinality obstruction (2026-10-31)

`G2PeircePrefixCarrierFacts.no_injective_nontrivialIdempotent_to_octImIsotropicPoint` is a genuine finite-cardinality obstruction: the source carrier has 72 elements and the isotropic-point carrier has 63, so no injection exists. Its scope is exactly these carriers and does not rule out a larger encoding. The constructive alternative retains all prefix and residual data: `occurringPeirceCode` is injective into a dependent sigma carrier, and the owner proves the resulting cardinal lower bound. Focused locked build passed (8,940 jobs, exit 0; imported linter warnings).

## G2 residual coordinate readback is a conditional criterion (2026-10-31)

`G2ResidualCoordinateReadback.residualWord_injective_on_cell_of_coordinate_separation` assumes coordinate separation for every distinct pair in every cell and then derives injectivity. The owner does not claim the premise, and it fails for the raw residual word on cell 2 (indices 170 and 185). The paired gap-residual coordinate is the verified all-cell injective replacement. Focused locked build passed (8,992 jobs; imported linter warnings).

## G2 paired-coordinate alignment premise is impossible globally (2026-10-31)

`G2GapResidualPairCellAssembly.quotientRepresentative_injective_of_distinct_gapResidualPair_alignment` is conditional. Its premise requires each distinct pair with equal quotient representatives to have equal paired residual coordinates in a common cell. For the concrete table, indices 24 and 45 have equal quotient representatives but unequal paired residual coordinates, so that premise is false. The canonical statements already proved are `quotientRepresentative_not_injective` and `gapResidualPair_injective_on_cell`: quotient collisions exist, while the paired coordinate separates indices within each individual cell. The implication must not be promoted to global injectivity. The unchanged owner’s locked build passed previously (9,016 jobs, exit 0).

## G2 Weyl double-coset injectivity is conditional (2026-10-31)

`G2TitsRepresentativeInjectivity.orbitWeylRepresentative_doubleCoset_injective_of_quotientOrbit_separation` proves injectivity of the 12 Weyl representatives into double cosets under pairwise disjointness of distinct left quotient orbits. It does not assert the separation premise for every pair and does not concern the 189-entry quotientRepresentative function with its known within-cell collisions. The owner proves identity-orbit separation from each other orbit, but not the full premise in this module. Canonical scope remains the conditional implication and that partial separation theorem. Focused locked build passed (8,995 jobs; imported linter warnings).

## Projective/Krein sandbox scope audit (2026-10-31)

The lexical candidate `rayEquiv_separates_antipodal` is correct: under the defined positive-rescaling relation, a nonzero vector cannot be positively rescaled to its negative. The focused audit build passed (3,093 jobs). The module’s broader interpretation needs tighter scope: `RayEquiv` and `RealProjectiveEquiv` are relations on all of V, with no quotient of the punctured carrier constructed; `GL2NDecomposition` stores four natural-number fields and its theorem proves only an arithmetic sum, not a direct-sum decomposition of `gl(2N, ℝ)`; and the ring-only Majorana equations do not include an adjoint operation, so they do not establish self-adjointness. Canonical statement scope is the proved rescaling/ring/arithmetic identities unless those geometric structures are separately constructed.

## Cartan–Souriau covariance candidate and exact kernel criterion (2026-10-31)

`chargeCovariance_posDef_of_separatesDirections` is valid under the owner’s finite family and strictly positive weights; the lexical identifiability flag was not a counterexample. I added `chargeCovariance_quadratic_pos_iff_exists_charge_difference` and `chargeCovariance_positiveDef_iff_separatesDirections`, giving the exact fixed-direction and positive-definiteness criteria. The focused locked build passed (3,094 jobs, exit 0). Existing deprecation and unused-section-variable warnings remain.

## Finite Vandermonde noncollision candidate (2026-10-31)

`PrimonCrystallizationFactIndex.finite_vandermonde_nonzero_iff_injective` is a correct re-export of the Mathlib Vandermonde determinant criterion over a commutative domain. The neighboring theorem identifies the determinant-zero locus with pair collisions. No counterexample was found; the lexical negative-boundary hit is a false positive. Focused locked build passed (9,256 jobs, exit 0; imported warnings).

## Mellin/Dirac readout species separation candidate (2026-10-31)

`readoutSpecies_separate` is the valid disjointness of `Sum.inl` and `Sum.inr`; the adjacent theorems show each tagged injection is faithful. Its scope is separation of tags in an abstract sum carrier, not a constructed separation theorem for concrete Mellin and Dirac spectral readouts. No counterexample was found to the Lean statement. Focused locked build passed (3,095 jobs; two simp-head warnings remain).

## Quasicrystal Vandermonde candidate is a duplicate re-export (2026-10-31)

`QuasicrystalRHExplicitFormula.finite_vandermonde_nonzero_iff_injective` and its zero-locus companion re-export the same Mathlib-backed finite Vandermonde criteria as `PrimonCrystallizationFactIndex`. They are valid over a commutative domain and finite `Fin n` nodes; this lexical match is not a counterexample and not a separate theorem family. Focused locked build passed (9,260 jobs, exit 0; many imported warnings).

## Winding-flux and finite-CCR conjunction is conditional and split-source (2026-10-31)

`Canonical.ApolloniusWindingFluxBridge.winding_quantization_with_finite_ccr_obstruction` is a conjunction, not a deduction of the finite-CCR obstruction from winding quantization. For positive radius, the first conjunct is the circle integral identity giving the logarithmic phase; independently, for `c ≠ 0`, `no_exact_nonzero_scalar_commutator` rules out the designated scalar commutator on the repository’s finite Zorn carrier. Both hypotheses and carriers remain explicit. No counterexample is present in this declaration; the canonical reading is the two separately sourced conditional facts. The locked build of `InfoGeometry.Canonical.ApolloniusWindingFluxBridge` passed (9,295 jobs, exit 0). The wider inventory remains open.

## Berry/QGT projector-agreement candidate is a valid conditional weld (2026-10-31)

The lexical candidate `Canonical.BerryPhase.starCertifiedEinsteinAnomalyQGT_berry_eq_metricOfOperator_liftedProjectorObstructionOperator_of_projectorAgreement` forwards to the owner theorem in `Quantum.GeometricTensorOperatorLift`. The owner proves the equality using the QGT Berry/metric sign conversion and the lifted operator identity, which requires explicit equality of the Moore–Penrose right and left projectors. This is a conditional bridge, not an unconditional projector-agreement theorem and not a counterexample. The focused locked build of `InfoGeometry.Canonical.BerryConnection` passed (4,139 jobs, exit 0).

## Bipolar two-coordinate skew obstruction has the stated finite scope (2026-10-31)

Both lexical candidates `pristine_two_coordinate_obstruction_core` and `pristine_dimension_obstruction_core` forward to `Thermo.BipolarTwoDimensionalSkewObstruction.skew_operator_eq_zero_of_eta_casimir`. The owner carrier is the explicit two-coordinate `Vec2R`; `L` is a linear map from its algebraic covectors to its vectors. Evaluation-skewness and `L etaCovector2 = 0` imply `L = 0`, so also `L thetaCovector2 = 0`. The owner separately proves the nontrivial-theta-lane contradiction. This is a genuine finite-dimensional conditional obstruction, not a claim about unrestricted or higher-dimensional carriers. The shared locked build of the owner and both capstones passed (8,965 jobs, exit 0).

## Bost–Connes Galois separation candidates require separating data (2026-10-31)

In `Canonical.BostConnesSymmetryBreaking`, both lexical candidates are valid generator-level implications. `galois_branches_separate_on_generator` assumes the target cyclotomic generator values differ; `galoisTranslated_readouts_separate_on_generator` assumes the base readout distinguishes those values. The proofs rewrite with the action-on-generator/pullback equations and apply the premise. These do not prove unconditional branch separation, faithfulness from a single readout, or analytic KMS classification. The distinct fixed-every-observable theorem retains its explicit hypothesis. The focused locked build passed (9,000 jobs, exit 0).

## Cantor prefix-cylinder separation is valid at the symbolic-boundary scope (2026-10-31)

`Canonical.CantorCliffordFunctionModelTopological.prefixCylinder_separates` is not a false separation claim. For distinct boundary functions, function extensionality yields a differing coordinate `k`; the prefix of length `k + 1` determined by the first function contains it and excludes the second. The theorem concerns the product boundary `ChiralBoundary` and its finite-prefix cylinders only; it does not establish measure-theoretic, Cuntz-representation, or spectral-triple claims. The focused locked build passed (9,158 jobs, exit 0).

## Catto–Gürsey associator obstruction is stronger than the characteristic-sensitive Jacobiator (2026-10-31)

`Canonical.CattoGurseySplitBasis.no_injective_associative_realization` is a valid counterexample theorem under its exact hypotheses: over any nontrivial commutative coefficient ring, an additive multiplication-preserving injection from the Zorn carrier into an associative ring would force the explicit associator of `u 0, u 1, u 2` to vanish, contradicting `triple_associator = uZero - uStarZero`. This proof does not require `6 ≠ 0`. The downstream `CattoGurseyOctonionicHadronicSuperalgebra.characteristic_three_boundary` separately demonstrates that the commutator Jacobiator can vanish in characteristic three while that associator remains nonzero. The canonical distinction is associativity obstruction versus Jacobiator behavior; one cannot infer associativity from that Jacobiator coefficient. Both owner and downstream module passed the shared locked build (8,936 jobs, exit 0).

## Conformal canopy scalar readout no longer carries an irrelevant KKT premise (2026-10-31)

Review of `ConformalUnification` showed `canopy_obstructionOperatorOwner` genuinely needs the three KKT wing hypotheses, while its scalar-readout conclusion is already an unconditional `ConformalInference` owner theorem. The old wrapper accepted the canopy package but did not use it to prove the scalar equalities. I changed `canopy_obstructionScalarReadout` to take only `CI` and return `CI.obstructionScalarReadout`, and updated both `Cl44BridgeCandidate` consumers. The combined closure retains the KKT package only for the operator-owner conjunct. The locked build of the three audited owners and `Cl44BridgeCandidate` passed (9,392 jobs, exit 0).

The related lexical candidates in `AlgebraicStationarity` and `BogoliubovOptimalTransport` are valid conditional laws: the former assumes exact negative operator agreement; the latter uses certified support and exact alignment characterizations on `CertifiedModularReduction`. Their inventory records now include the successful focused build.

## De Rham obstruction declarations are predicate consequences, not an existence witness (2026-10-31)

In `Canonical.DeRhamSymplecticKKQuantizationLimit`, `IsObstruction α` is defined as closed and not exact in an arbitrary two-step complex with `d₁ ∘ d₀ = 0`. The candidate theorems `obstruction_closed`, `obstruction_not_exact`, and `exact_not_obstruction` correctly unpack this definition; they do not exhibit a non-exact closed current or establish nontrivial cohomology for a concrete de Rham complex. The canonical scope is therefore definition-level logic until an explicit class and no-primitive proof are supplied. The focused locked build passed (3,097 jobs, exit 0).

## Deformed-Idele scalar-node bridge keeps its missing theorem explicit (2026-10-31)

`Canonical.DeformedIdeleDysonBridge.nodes_injective_of_range_defect` derives injectivity by applying the explicit field `range_defect_forces_injective_nodes` in `BranchDefectToDysonNodes`, given a range-projection defect. The subsequent pairwise noncollision, Vandermonde nonvanishing, and Dyson identity depend on that premise. The source documentation correctly says no scalar readout is derived from operator algebra alone. This is a conditional bridge package, not an unconditional spectrum construction; no counterexample is present in the stated theorem. The focused locked build passed (9,188 jobs, exit 0).


## Dilated gap candidates are conditional identities (2026-10-31)

Reviewed both lexical candidates in `Canonical.DilatedGapEquivariance`. The projector result assumes zero `projectorMismatch`; its owner theorem identifies the anomaly exactly as the mismatch commutator with the metric projector, and gives vanishing iff that mismatch commutes with the metric projector. The transported parity/modular residual follows from the seed decomposition under commutation of the phase-linear part with `modular_j`; the stronger owner result kills the seed when the full connection generator commutes with `modular_j`. These are conditional results, not counterexamples or unconditional vanishing claims. The focused locked build passed (4,182 jobs, exit 0).

## Dirac zero-mode candidate is a kernel/injectivity equivalence (2026-10-31)

`Canonical.DiracBerryKeatingFredholmBridge.not_hasZeroMode_iff_injective` is the standard exact linear-map criterion, proved from nontriviality of `LinearMap.ker D`. `kernel_protection_survival` separately requires an injective intertwining map. `zero_free_region_trivial_index` assumes the supplied `RHSpectralDuality` and yields only no zero mode; it does not calculate a Fredholm index. The repository search also found distinct zero-mode constructions, so this candidate supports no repo-wide absence claim. The focused locked build passed (3,093 jobs, exit 0).

## Drazin defect obstruction is exactly a commutation criterion (2026-10-31)

`Canonical.DrazinModularSingularityBridge.defectProjectionObstruction` is defined as the DrazinSupercharge commutator of `Y` with the spectral complementary projector. The candidate iff theorem unfolds this definition and applies `sub_eq_zero`; it is an exact operator criterion with no counterexample, and does not by itself establish a nontrivial singularity or spectral result. The focused locked build passed (4,211 jobs, exit 0).

## Einstein anomaly naming preserves the left/right projector condition (2026-10-31)

`Canonical.EinsteinAnomalyOperator` proves the lifted Einstein anomaly equals the negative lifted right chiral anomaly unconditionally on `CertifiedConformalInference`. The lexical candidate relating it to the left projector obstruction correctly assumes equality of the Moore-Penrose left and right projectors; the owner derives it from the left/right anomaly identification under that premise. This is a valid conditional bridge, not a counterexample. The focused locked build passed (4,111 jobs, exit 0).

## Five-graded packet incidence is a finite-model consequence (2026-10-31)

`Canonical.FiveGradedTwistorIncidence.incident_points_null_separated` correctly transfers incidence with a shared twistor and nonzero primary spinor to null separation. The imported `Twistor.Incidence` owner proves the stronger finite-model equivalence: `q22 (X - Y) = 0` iff a shared twistor exists with nonzero primary spinor. This uses the explicit real 2x2 soldering/determinant model and does not assert a geodesic, manifold, or infinite-dimensional twistor result. The focused locked build passed (3,212 jobs, exit 0).

## G2 orbit candidate gets its sharp abstract-carrier criterion (2026-10-31)

`Canonical.G2LeechCoxeterBoundaryBridge` states injectivity of a primitive-24th-root orbit under a nonzero seed and transfers it to any map satisfying explicit iterate equivariance. I added `planeOrbit_injective_on_range_iff`, proving on the actual complex carrier that first-cycle injectivity is equivalent to seed nonzeroness. The bridge does not construct a Coxeter projection from a Leech lattice; its own source keeps that missing carrier map explicit. The focused locked build passed (9,137 jobs, exit 0).

## Generative inference obstruction is exactly projector commutation (2026-10-31)

`GenerativeInferenceCore.spectralObstruction_eq_zero_iff_projectors_commute` is an exact operator criterion for its `CertifiedChiralSpectralTriple`: the obstruction is the commutator of the spectral and metric projectors. The neighboring `anomalyScale_eq_zero_of_projectors_commute` proves only the forward scalar implication here. A related conformal package has a scalar iff theorem, but the carriers differ, so I do not transfer that converse. Focused locked build passed (4,092 jobs, exit 0).

## Grand synthesis anomaly term is a package norm readout (2026-10-31)

The private `GrandSynthesis.anomalyTerm_eq_projectorObstruction_norm` follows from `SingularTransportSystem.anomalyTerm_eq_boundaryScale` and the boundary owner’s norm identity for the spectral/left-projector commutator. It is a valid exact readout inside a supplied package, not a separately constructed obstruction or counterexample. The module’s radial-closure statements remain conditional on boundary-scale/generator vanishing. Focused locked build passed (4,132 jobs, exit 0).

## Incompressible Cramer-Rao collapse drops a redundant commutation premise (2026-10-31)

The original zero-obstruction/dilation theorem required both right-projector agreement and left-projector commutation. Under the explicit negative-log-volume readout, incompressibility already forces zero chiral scale; the owner theorem then yields left-projector commutation, so the latter premise was redundant. I removed it from the zero-pair theorem and updated its internal callers. The larger semantic-collapse packet retains left commutation because its separate Weyl/KKT semantic conjunct consumes it. Focused locked build passed (4,182 jobs, exit 0).

## Matrix Cuntz obstruction is now stated on the concrete tower carrier (2026-10-31)

`FiniteMatrixCuntzObstruction.no_cuntz2_matrix` is a genuine finite-dimensional trace obstruction: two Cuntz isometry range projections each have trace `n`, while their sum is the identity of trace `n`, contradiction. The `MatrixCuntzStarTower` wrapper was generic in matrix dimension; I added `concreteMatrixStage_cuntz_obstruction` for `MatrixStage k` of size `2^k`. This says nothing against Cuntz families in the categorical/infinite colimit carrier; the imported rectangular branch construction is a distinct replacement. Focused locked build passed (3,687 jobs, exit 0).

## Direct-limit kernel survival is already an algebraic iff (2026-10-31)

The candidate theorem in `Canonical.ModuleCatDirectLimitKernelSurvivalBridge` is supported by `Algebra.DirectLimitSuperClosureLemmas.directLimitOf_eq_iff_of_injective` and its zero-specialized `directLimitOf_eq_zero_iff_of_injective`: under injective bonding ring homomorphisms, a canonical stage image in the algebraic direct limit is zero iff its source is zero. No topology is defined on this carrier; I corrected the stale “topologically protected” wording. A focused locked build was requested but stayed queued on the shared build lock, so this entry records source-level evidence only.

## NC-Zorn alternativity failures are explicit matrix witnesses (2026-10-31)

`Canonical.NCZornAlternativityAudit` computes a specific sigma-minus coordinate of each alternative-law associator. The left defect is `(a*b - b*a)*d`, and the right defect is `d*(a*b - b*a)`; it then specializes to matrix units `E₁₂`, `E₂₁` in `BdGBlock ℚ` with `d = 1`, where the coefficient commutator is nonzero. Thus both global alternative laws fail for this displayed multiplication over that noncommutative coefficient carrier. The theorem does not claim alternativity failure over every coefficient ring, nor sufficiency of coefficient commutativity. A focused locked build was requested but stayed queued on the shared build lock, so this entry records source-level evidence only.

## Projector mismatch is weaker than noncommuting split (2026-10-31)

`ProjectorPair.commutator_ne_zero_implies_projectorMismatch_ne_zero` is a valid one-way implication in any ring: equal projectors necessarily commute. Its converse is refuted by `commuting_projectors_can_have_nonzero_mismatch`, using two distinct complementary idempotents in `Matrix (Fin 2) (Fin 2) ℤ` with zero commutator and nonzero difference. The correct general statement is the one-way implication, not equivalence of mismatch with noncommutativity. Source-level review only; the shared build lock remained unavailable during this pass.

## Weyl holonomy endpoint requires the explicit curvature bridge (2026-10-31)

`PhaseSpaceWeylCausalBridge` transports theorems from `WeylTransportChiralBridge`. Its holonomy equals the projector-obstruction norm only when an explicit `FlatCurvatureProjectorObstructionBridge` and pointwise flatness are supplied; the bridge carries the integral-to-target relation. Flatness alone is not claimed to determine holonomy. The owner also proves zero holonomy iff the spectral and metric chiral projectors commute, and separately identifies the obstruction norm with `chiralScale`. The dilation source identities retain their required projector commutation/agreement hypotheses. No overstrong unconditional statement was found in the reviewed declarations. Source-level review only; build lock unavailable.

## Plabic Gram transport is correctly limited to nonzero eigenvalues (2026-10-31)

`mulVec_gram_eigenvector_injective` and its concrete edge-sum wrapper require a shared eigenvalue `λ ≠ 0`; under that premise, applying `Aᴴ` to equality of transported vectors and cancelling `λ` proves source equality. The owner separately identifies `ker(AᴴA)` with `ker(A)`, so the zero eigenspace is explicitly treated without claiming injectivity there. Adjacent results state geometric eigenspace dimension equality and nonzero characteristic-root multiplicity, without generalizing to generalized eigenspaces or SVD. Source-level review only; no focused build yet.

## Primon/Dirac readout separation is scalar only (2026-10-31)

`dirac_heat_kernel_readouts_separate` is a valid real-scalar consequence of injectivity of `Real.exp`; its theorem in fact needs no positivity of the energies despite the narrower docstring. `primon_thermal_readouts_separate` is likewise valid because `E > 0` makes `β ↦ βE` injective. Neither theorem formalizes a matrix/operator heat kernel or uses primality of the energy parameter; their exact scope is elementary scalar readout separation. Source-level review only.

## Projector obstruction is not itself a dilation (2026-10-31)

`ProjectorNoncommutativityDilationClosure` has a valid ring-level implication from noncommuting idempotents to nonzero mismatch. Its module header correctly states that this alone yields no dilation or conformal closure; those require supplied `DilationClosureData`, transport, and canopy packages. The historical `DGenerator` was merely an alias of `projectorObstruction`, so I revised its docstring to state that it does not itself construct a dilation. Source-level review only; the shared build lock was unavailable.

## Reflexive Klein representation has an explicit nontrivial kernel (2026-10-31)

Under the supplied reflexive-pair relations `d² = B² = 0`, `dBd = d`, and `BdB = B`, the presented glide has infinite order by its integer coordinate in the native semidirect-product model. Its image under `reflexiveKleinRep` has fourth power one, for every scalar unit `t`. Thus the nonidentity fourth power is an explicit kernel element and the representation is not injective. This is conditional on the reflexive-pair data and concerns this representation specifically. Source-level review only; no build result claimed.

## Relational transport obstruction is precisely Jacobi's identity (2026-10-31)

`transportObstruction X Y A` is `[X,[Y,A]] - [Y,[X,A]] - [[X,Y],A]` on the continuous endomorphism Lie algebra. Its zero theorem is exactly the Jacobi identity. This establishes flatness only for the primitive inner-derivation construction defined there, not for any independent geometric connection; the source and dynamics consumer keep that distinction. Source-level review only.

## Singular transport norm theorem is derived in its boundary owner (2026-10-31)

`SingularBoundaryCorrection.boundaryScale_eq_projectorObstruction_norm` unfolds the certified kernel’s `chiralScale` and `chiralAnomaly` definitions and proves the boundary scale is the norm of the spectral/metric left-projector commutator. `SingularTransportSystem` delegates to this theorem; the anomaly scalar equality and transport split are package fields, and radial closure remains conditional on vanishing boundary scale. The norm identity is genuinely derived in the boundary owner, not supplied as a package field. Focused locked build passed (3,848 jobs, exit 0), with existing deprecation and linter warnings.

## Response determinant bridge retains its readout premise (2026-10-31)

`ResponseWeylAnomalyBridge` assumes an explicit equality from the thermodynamic response determinant to the flat Weyl holonomy before identifying the determinant with the projector-obstruction norm. Its nonzero and non-spinodal consequences also depend on that readout; `Spinodal2D` is definitionally determinant zero. No unconditional thermodynamic-to-Weyl identification is made. Source-level review only.

## Spectroscopic gauge obstruction has an exact commutation criterion (2026-10-31)

`gaugeObstruction` is the commutator of the analyzer and observable. I added `gaugeObstruction_eq_zero_iff_commute`, making explicit that its vanishing is equivalent to commutation. The bridge to `CertifiedInverseKernel.chiralAnomaly` continues to require `hAnalyzer`; it identifies the left-projector anomaly only under that equality. Focused locked build passed (4,217 jobs, exit 0), with existing warnings.

## Zorn split-octonion product cannot embed injectively into an associative semigroup (2026-10-31)

The source exhibits a primal basis triple with nonzero associator. If an injective multiplicative map into any semigroup existed, associativity in the target would force the two source bracketings to have equal images, contradicting injectivity. This valid obstruction rules out injective multiplicative realizations in ordinary associative matrix algebras, while allowing noninjective maps and linear carrier equivalences. Source-level review only.

## TKK Möbius/parity separation uses an explicit vector witness (2026-10-31)

`mobius_parity_separate` is the standard extensionality witness principle: disagreement at one vector proves two `Module.End` maps differ. The specialized TKK inversion theorem supplies the necessary fixed negative-grade witness and a positive/negative grade inequality; it does not assert inversion differs from every parity map unconditionally. Source-level review only.

## SO(3) angular momentum now states injectivity directly (2026-10-31)

For nonzero scalar inertia, the existing theorem provides a left inverse to `ω ↦ I • ω`, which implies injectivity. I added `angularMomentum_function_injective` with the direct `Function.Injective` conclusion, derived from that left inverse. The focused locked build passed (3,162 jobs, exit 0); compiler output reported existing linter warnings.

## Theorem-honest kernel bridge scope audit (2026-10-31)

`Canonical.TheoremHonestSpectralKernelToeplitzBridge.intertwining_injective_kernel_survival` is a valid abstract lemma: an injective zero-preserving map that intertwines two endomorphisms carries each nonzero kernel vector to a nonzero kernel vector. The file itself contains only this result and the corresponding kernel-membership preservation lemma. Its header claims formalization of self-adjoint/chiral index, Toeplitz argument-principle zero counting, antiunitary fixed-locus rigidity, and a unified master duality; those claims are not supported by declarations in this file. Repository-wide search found related topic references/declarations, but did not establish that one theorem assembles them. This is a scope/documentation mismatch, not a counterexample to the kernel-survival theorem. Source inspection only; no fresh build was run.

## Thermodynamic Massieu obstruction lexical-hit audit (2026-10-31)

The two obstruction-name hits in `Canonical.ThermodynamicGenerator` are valid conditional operator identities, not counterexamples. `liftedProjectorObstructionMassieuPotential_normalizedInfinitesimalLaw` specializes the generic normalized operator Massieu derivative theorem. `liftedEinsteinAnomalyMassieuExpectation_eq_neg_liftedProjectorObstructionMassieuExpectation_of_projectorAgreement` uses the existing operator equality under explicit Moore–Penrose right/left projector agreement. This sign relation is not stated unconditionally. Source inspection only; no fresh build was run.

## Twistor operatorial-incidence equivalence audit (2026-10-31)

`CertifiedConformalInference.operatorialIncidence_iff_projectorObstructionOperator_zero` is mathematically consistent but redundant: its proposition is identical to the immediately preceding `operatorialIncidence_iff_chiralAnomalyOperator_zero`, and its proof delegates both directions to that result. The incidence predicate is definitionally vanishing of the lifted projector-obstruction operator; `dualSheetLift_eq_zero_iff` supplies the lift-to-base equivalence. Repository search found no other consumers of the duplicate declaration. The canonical reusable statement is the preceding iff theorem, with the lift zero criterion for its operator interpretation. This is a redundant API surface, not a counterexample. Source inspection only; no fresh build was run.

## Fact–Logic support counterexample and exact replacement (2026-10-31)

The finite `M₃(ℚ)` matrix-unit witness in `Routing.FactLogicBypassMatrixCounterexample` shows that the support pattern permits a prompt-to-fact block. The reusable replacement is the exact equation `publishedMaskSupport_prompt_fact_block`, together with the new necessary-and-sufficient criterion `publishedMaskSupport_prompt_fact_block_eq_zero_iff`: the block is zero iff `P_p * R * P_f = 0`. Thus orthogonality of the diagonal track idempotents alone does not force zero leakage when the support expression contains a free prompt-to-fact route. The locked build of the algebra, matrix witness, and axiom audit passed (1204 jobs); new theorem axiom readback reports `[propext]`.

## Cantor-prefix inverse-limit separation audit (2026-10-31)

`prefixLimitCylinderSet_separates` is valid in its stated topological inverse-limit scope and is not a counterexample. Added `prefixLimit_projection_separates`: any distinct points in the `TopCat` limit differ under some finite-prefix projection. The proof uses the existing cylinder-separation theorem and `prefixLimitCylinderSet_eq_projection_fiber`. The locked owner build passed (3125 jobs).

## Finite-cylinder Cantor separation audit (2026-10-31)

`cylinderSet_separates` is a valid separation theorem, not a counterexample. Extracted the core statement as `boundaryPrefix_separates`: distinct binary boundary points differ at a finite prefix. Refactored `cylinderSet_separates` to reuse this criterion. Locked builds of `UHFInductiveColimitBoundaryTopology` and its inverse-limit dependent module passed (3125 jobs).

## Pauli quaternion basis sign audit (2026-10-31)

The literal assignment `i ↦ Iσ₁`, `j ↦ Iσ₂`, `k ↦ Iσ₃` is a concrete finite counterexample to the claimed Hamilton relation `ij=k`: `quaternion_literal_i_j_sign_obstruction` proves the product is `−Iσ₃`. The canonical corrected basis in the same owner is `qI=Iσ₁`, `qJ=Iσ₂`, `qK=−Iσ₃`; the file proves each square is `−1` and the cyclic products `qI*qJ=qK`, `qJ*qK=qI`, `qK*qI=qJ`. The locked owner build passed (3094 jobs); only the existing deprecated complex import warning appeared. Scope is the stated finite matrix assignment, not all quaternion representations.

## Matsubara index-injectivity scope audit (2026-10-31)

`matsubaraFrequency_injective` correctly proves injectivity of `n ↦ (2πn)/β` for `β ≠ 0`, and the owner proves the corresponding zero-mode iff. The former docstring said “discrete/injective,” although this module defines no image topology and proves no topological discreteness. Narrowed the documentation to the algebraic injectivity result. The locked owner build passed (4226 jobs) with existing linter warnings.

## Poisson intensity scale identifiability audit (2026-10-31)

The existing injectivity result is correctly conditional on a nonzero entry of the kernel matrix. Added `poissonIntensity_scale_injective_iff`, the exact criterion: with fixed background, the scale map is injective iff the kernel has a nonzero entry. If the kernel is zero, the intensity map is constant. The source argument is reviewed; the new declaration remains build-pending because the repository locked-build session has not returned a terminal result.

## V4 affine cocycle obstruction scope audit (2026-10-31)

The formula `cocycle_as_triality_obstruction` correctly computes the affine defect as `(2 * θ₂ + 2 * π, 0)`, but the defect is not universally nonzero. Added `cocycle_as_triality_obstruction_eq_zero_iff`: it vanishes exactly when `θ₂ = -π`, for every boundary point. The file separately scopes the available finite V₄ statement and acknowledges the full Weyl decomposition as closure debt. Source-reviewed; new lemma build pending.

## Vandermonde determinant criterion audit (2026-10-31)

`determinant_ne_zero_iff_injective` is a valid domain-level criterion inherited from the Mathlib Vandermonde determinant theorem; its companion collision equivalence is exact. The collision consequence and packet theorem reuse these statements, and arithmetic owners consume the criteria. No counterexample or additional replacement was needed. Source review only.

## Finite D4 character/Vandermonde packet audit (2026-10-31)

`denominator_ne_zero_iff_injective` and the collision criterion are sound packaging: the packet identifies witness nodes with denominator nodes, then reuses the finite Vandermonde owner. Downstream cancellation modules consume these exact criteria. The module explicitly disclaims the full Weyl character formula and quotient regularity. No counterexample found; source review only.

## Weyl/KKT anomaly closure assumptions audit (2026-10-31)

The readout/norm equality is a valid alias through owned identities. Dilation-source identities require the explicit projector compatibility and commutation hypotheses (or their bundled witness); zero-scale collapse uses the existing zero-scale-to-projector-commutation theorem. The transported Einstein nonzero result assumes the source equation and a nonzero obstruction, while its companion proves residual zero iff the chiral projectors commute under that source equation. These are appropriately conditional. No counterexample found; source review only.

## Local Weyl cancellation shadow audit (2026-10-31)

The denominator criterion correctly delegates to the finite D4 Vandermonde packet. Numerator vanishing on collisions is explicitly assumed in the packet, while the quotient is defined only when the denominator is nonzero. The file clearly disclaims quotient regularity and the full Weyl character formula. No counterexample found; the conditional local theorem is accurately scoped. Source review only.

## Weyl transport holonomy bridge assumption audit (2026-10-31)

The flat-holonomy statements are valid compositions, but `FlatCurvatureValueBridge` already assumes both flatness-to-zero-curvature-integral and zero-integral-to-target-holonomy. The projector-obstruction norm endpoint is therefore supplied by the bridge, not derived from flatness alone. Scalar retargeting uses the existing norm identity; the finite-sum constructor carries the same endpoint premise. The exact zero-holonomy iff projector-commutation result is conditional on that bridge. No counterexample to the stated implications; source review identifies a strong assumption that should remain explicit.

## Winding-orbit obstruction faithfulness audit (2026-10-31)

The winding obstruction is the difference of two exponential values. Clock-axis commutation gives zero via integer `2π` periodicity. The reverse equivalence explicitly assumes `IsClockFaithfulExponentialBranch`, defined only as the selected branch equality implying commutation; it does not claim global exponential injectivity. A local gauge certificate supplies this branch premise through its response-faithfulness field. Clock-equilibrium equivalence also uses the owner defect-zero iff commutation theorem. No counterexample found; the reverse implications are properly conditional. Source review only.

## Krein/RH odd-obstruction capstone audit (2026-10-31)

`translated_krein_rh_from_odd_obstruction` is a valid implication from a chart certificate: off-throat zero states produce an obstruction, while zero states also force that obstruction to vanish. Contradiction gives chart-local no-leakage. The theorem does not construct the certificate or prove a concrete spectral chart/classical RH; the module header says so explicitly. No counterexample to the conditional result. Source review only.

## Jordan triple formula exact defect and counterexample witness (2026-10-31)

The owner proves the proposed triple formula defect is `(z*x - x*z)*y`; its pointwise iff and companion all-middle iff give the exact criterion (the latter is endpoint commutation). The invertible-middle criterion also detects commutation. Added `proposed_triple_formula_fails_at_one_of_noncommuting` in `JordanTripleFormulaCriterion`: any noncommuting endpoint pair fails the proposed formula at the unit middle input. This is a general noncommutative counterexample schema. The new corollary awaits the locked build.

## Peirce matrix representation faithfulness audit (2026-10-31)

`representation_injective` correctly requires `X ≠ 0`; the exact `representation_injective_iff` proves this condition necessary and sufficient over a field. Matrix-unit sandwiches recover the coefficients in the nonzero case, while the `(0,1)` matrix unit witnesses kernel when `X = 0`. The module accurately distinguishes the full matrix target from the supported nonunital image. No counterexample found; source review only.

## DAG-Majorana package scope audit (2026-10-31)

`central_residue_binary_for_obstruction_readout` duplicates the preceding `central_residue_binary` theorem, both re-exporting the structure field. The structure assumes the ±1 range; it does not derive a residue law. The old module header claimed a path-to-operator projective representation, but no path map or homomorphism law exists in the owner. Narrowed the module and structure documentation to the actual graph/net/residue package and marked the theorem as a compatibility alias. This is a scope/documentation correction, not a kernel counterexample.

## Positive-slice norm noninjectivity counterexample (2026-10-31)

`positiveSlice_norm_not_injective` gives distinct spatial basis vectors with equal norm at temporal parameter 1. The exact fiber theorem says equality is equivalent to equal squared Euclidean norms: the scalar readout preserves radius and loses direction. The owner also exhibits a Zorn element with negative norm, so positivity is restricted to the declared positive slice. Source-inspected; no fresh build in this turn.

## Epistemic gradient/Dirac prerequisite model audit (2026-10-31)

`dirac_obstruction_is_separate` proves incomparability in the file’s hand-authored finite poset, where the Dirac node is assigned only itself. It does not establish independence in the actual Lean import/declaration graph. Added module and theorem documentation making this model boundary explicit. No false result in the declared order; source scope clarified.

## Chevalley root-subgroup product injectivity audit (2026-10-31)

The positive/negative height declarations correctly specialize the generic ordered-product injectivity theorem. They require a nodup list exactly described by root membership, sign of height, and exclusion of roots twice another root, plus a nontrivial domain with no zero divisors. The proof uses the height filtration and uniqueness of pinned-root parameters; the negative branch reduces to the positive branch at `-height`. These are scoped results, not arbitrary-list injectivity. No counterexample found; source review only.

## Interval projection noninjectivity witness (2026-10-31)

`interval_projection_not_injective` uses the explicit pair `-1` and `0`, both mapping to `0`. The owner also proves the fixed-point iff for `[0,1]`, idempotence, and surjectivity onto that interval. Thus this is the expected information loss outside the projection target, with an exact fixed-point characterization. Source review only.

## Concrete Zorn Cartan weight separation audit (2026-10-31)

`CanonicalZornCartanRootSystem.nativeRootWeights_separate` is valid for the
specified embedded three-coordinate axial Cartan: three explicit entries in
the fourteen-index weight list recover each coordinate, so a nonzero Cartan
vector has a nonzero listed weight. `CanonicalZornSemisimple` consumes this
lemma. This statement is model-specific and does not alone classify abstract
root systems. The repository's downstream `CanonicalZornIsKilling` separately
constructs `canonicalZornRootSystem` using Mathlib's `IsKilling.rootSystem`;
the prerequisite module's header should not be read as saying that downstream
construction is absent. Source reviewed; no counterexample to the candidate.

## Fisher–Souriau positivity under charge separation audit (2026-10-31)

`fisherSouriauQuadratic_pos_of_charge_separates` is a valid conditional
positive-definiteness result. Its hypothesis says every nonzero direction
separates at least one pair of moment-map values; the owner proves the form is
a Gibbs-weighted sum of centered squares and that such a pair forces one
centered value to be nonzero. `CanonicalZornG2CartanMassieuConvexity` supplies
the premise from its explicit charge-affine-nondegeneracy hypothesis. The
result does not claim strict positivity for arbitrary charge data. No
counterexample to the stated implication; source review only.

## Native Clifford representation dimension obstruction audit (2026-10-31)

`splitOctonionLeftCliffordRepresentation_not_injective` follows from the
proved real dimensions 128 for the full Clifford algebra and 64 for the
endomorphisms of the native eight-dimensional Zorn module. The companion
rank-nullity theorem gives kernel dimension at least 64. The owner explicitly
notes that this does not contradict injectivity of the imaginary-generator
map. The conclusion is limited to faithfulness of this full representation;
it is not an obstruction to arbitrary operator representations. No
counterexample to the theorem's stated scope; source review only.

## Chiral null-gauge positive-source obstruction audit (2026-10-31)

`ChiralNullGaugeTests.positive_source_obstruction` specializes the generic
`InnerDivergenceCharge.nonzero_gramian_not_divergence` theorem to the concrete
nonzero matrix `couplingBlock`. The generic proof uses trace zero for finite
sums of commutators and positive trace for a nonzero real Gramian. This
excludes that source from the declared boundary-free finite inner-divergence
form; it does not make a universal claim about boundary terms or other
notions of divergence. No counterexample to the scoped result; source review
only.

## Cole–Fury aggregate readout kernel audit (2026-10-31)

`ColeFuryEmbedding.embed_not_injective` and
`quadrantReadout_not_injective` are witnessed by a nonzero contrast whose
aggregated upper-horizon coordinate is `1 + (-1) = 0`. The companion
`ColeFuryReadoutFibers` module gives the exact readout equality and kernel
criteria. Thus the map is accurately treated as an aggregate linear readout,
not an embedding; multiplication compatibility is separately restricted to
the first-generation subspace. No counterexample to the scoped noninjectivity
claims; source review only.

## Horizon terminal-collapse identifiability audit (2026-10-31)

`PralayaDissolutionDatum.not_injective_of_distinct_memories` assumes the
structure field that every memory maps to one terminal state. Under that
constant-image premise, two distinct memories have equal images, proving
noninjectivity and the companion impossibility of decoding both exactly. This
is a valid conditional consequence; it does not assert that an evaporation
map satisfies the premise. No counterexample to the declared implication;
source review only.

## Jones flat-sector zero-locus audit (2026-10-31)

`JonesObstructionCalibration.flat_obstruction_zero` follows directly from
membership in `Flat`, which is defined as `{x | obstruction x = 0}`. It is
valid but only unpacks the zero-locus definition; it proves no analytic
flatness criterion. The conserved-flow constructor separately takes an
obstruction-preservation premise. No false statement found; source review
only.

## Operator Zorn self-cross obstruction audit (2026-10-31)

`native_self_cross_obstruction` forwards the exact owner criterion
`operatorCross_self_eq_zero_iff`: the self-cross product vanishes exactly when
the three coordinates commute pairwise. The statement is a valid equivalence
on the declared ring carrier, not a blanket noncommutativity claim. No
counterexample to the criterion; source review only.

## Partner generalized-eigenspace injectivity audit (2026-10-31)

`injective_partnerGenEigenspaceMap` restricts `A` to the generalized
eigenspace of `BA`. Under `μ ≠ 0`, a vector in its kernel is also in the zero
generalized eigenspace of `BA`; Mathlib's disjointness of zero and nonzero
generalized eigenspaces forces it to vanish. The companion theorem establishes
surjectivity using invertibility of the restricted `AB`, producing an
isomorphism at finite and maximal depth. This is not global injectivity of A.
No counterexample to the scoped result; source review only.

## Homogenized Peirce channel noninjectivity audit (2026-10-31)

The four declarations in `PeirceSpine.HomogenizedKernels` establish genuine
noninjectivity of the channel maps on any nontrivial ring. Three maps agree
at 0 and 1 directly. For `hProjV`, the proof uses the value at Φ when Φ is
nonzero; when Φ is zero, the A3 identity forces V=0 and the map again agrees
at 0 and 1. The owner correctly describes these as additive channels, not
automorphisms. No counterexample to the scoped results; source review only.

## Signed transport positive-input obstruction audit (2026-10-31)

`skewTransport_positive_input_obstruction` assumes a nonzero square-zero real
matrix `a`. It proves that `a aᴴ` is positive semidefinite while its image
under the declared signed transport is not, using the preceding
`skewTransport_not_positive` theorem. This is a conditional positivity
counterexample; the file does not claim such an `a` exists in every dimension
or infer a complete-positivity result. Source review only.

## Split-octonion left-multiplication nonmultiplicativity audit (2026-10-31)

`nonmultiplicativity_obstruction` uses a concrete nonzero associator: assuming
left multiplication preserves the product for the displayed pair and applying
the operator identity to the third element forces the associator to vanish.
`pseudoReal_nonmultiplicativity_obstruction` transports the same witness
through the faithful matrix-to-linear-map representation. This disproves
multiplication preservation for the stated representation; it does not rule
out faithful linear representations or the separate Clifford square law.
Source review only.

## Split-octonion Peirce–Witt associator audit (2026-10-31)

`peirceWitt_nonassociative_obstruction` re-exports the concrete multiplication
owner's nonzero associator witness for `(up0, up1, down1)`. The bridge states
its Yang–Baxter result only for finite permutation braid-word evaluations
combined with Peirce compression. The obstruction therefore refutes automatic
associative cancellation for this selected triple; it is not a counterexample
to the finite braid rewrite theorem or a claim about all triples. Source
review only.

## MDPASJM direct-limit stage-map injectivity audit (2026-10-31)

`ofStage_not_injective_of_bond_not_injective` is a valid quotient consequence:
if a bonding map identifies distinct elements at a specified stage, the
bonding relation identifies their classes in the set-level direct-limit
carrier, so the canonical stage map is not injective. The theorem assumes an
explicit bond collision and makes no claim that a particular system has one.
The companion direct-limit lift separately states the compatibility condition
for maps out of the quotient. Source review only.

## Signed particle–photon correlation separation audit (2026-10-31)

`correlation_separates_iff` follows from the exact difference formula: the two
sign readouts differ exactly when the dot product is nonzero. The concrete
orthogonal unit vectors in `nonzero_vectors_need_not_separate` are both
nonzero but give equal sign readouts, refuting separation from nonzeroness
alone. This is the stated finite `Vec3R` algebra, not an empirical model
claim. Source review only.

## Quadratic response exact-fiber replacement (2026-10-31)

The response difference factors as `(x-y) * (C - B*(x+y))`. Added
`response_eq_iff`, proving for all real coefficients that two inputs have the
same response exactly when they are equal or their sum is the reflection
center equation `B*(x+y)=C`. This strengthens the existing conditional
noninjectivity witness by describing all fibers, including degenerate
coefficient cases. The source is staged. Kernel verification passed with `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Probability.SimplexQuadraticResponse`; the build emitted existing warnings in unrelated modules.

## Attention kernel-line injectivity audit (2026-10-31)

`kernel_line_injective` is valid: a nonzero direction function has a nonzero
coordinate, and equality along the affine line at that coordinate forces the
real parameters to agree. This injectivity is for the parameterization of a
single line, not for the homogeneous attention decoder; the surrounding owner
states the latter's kernel and affine-independence criteria separately.
Source review only.

## Five-graded spin-obstruction Boolean marker audit (2026-10-31)

`w2_obstruction_cases` is a case split on a stored `Bool`. The owner states
that this field is only a marker, not an actual cohomological
Stiefel–Whitney class; the concrete two-dimensional packet chooses `false` by
construction. Ribbon and trace results are conditional on stored closure
fields. The candidate is valid finite bookkeeping and establishes no
spin-structure classification. Source review only.

## Geometric tensor operator-lift bridge audit (2026-10-31)

The derivative transport candidates require explicit commutation with the
modular gauge part and specialize the general source-channel identity. The
Berry sign and QGT bridge candidates require equality of the Moore–Penrose
left/right projectors; the latter also uses the star-certified carrier and
operator-to-form sign identities. These premises are present in the exact
theorem statements and are used in the proofs. They are conditional transport
identities, not unconditional geometric classification results. No
counterexample to the stated implications; source review only.

## Hestenes–Kähler operator readout bridge audit (2026-10-31)

The bidegree claims unfold parity fields. Incidence vanishing assumes the
operatorial-incidence premise and obtains a zero seed; the Berry readout then
vanishes by linearity. State dynamics split and paired-source cancellation
forward general transport results, with the cancellation premise explicit.
Readout identities are definitional or follow from linearity. The anomaly to
projector-obstruction metric weld requires Moore–Penrose projector agreement
and star certification. These are valid conditional finite operator/readout
identities, not independent Hestenes or topological classification theorems.
Source review only.

## Quantum geometry projector bridge audit (2026-10-31)

The phase-readout theorem identifies the second operator-pair component under the explicit Moore–Penrose projector-agreement premise, by specializing the Hestenes–Kähler bridge. The derivative theorem specializes the comparison-transport derivative law; its seed phase-axis identity is proved by unfolding the seed and applying the channel-phase-axis theorem. Both source statements are valid as conditional/definitional bridge identities. They do not establish the external TCR-Former attention-mask claims or its reported ablation metrics. Source review only.

## Welded projector correlation bridge audit (2026-10-31)

The phase-axis seed identity follows because the channel phase-axis map squares to minus the identity and the seed is its negative image. The welded phase equals the K-shifted two-state correlation under the explicit Moore–Penrose projector-agreement premise; same-state and comparison-state results specialize it. The derivative-at-zero statement specializes the general comparison-transport derivative identity and rewrites the seed phase axis to the lifted obstruction operator. These are valid bridge identities under their stated premises, not topological classification claims. Source review only.

## Finite archetype prerequisite-poset audit (2026-10-31)

The flagged inclusion and branch-incomparability statements reduce by `decide` to the explicit Finset prerequisite assignment. The partial order is lifted from that assignment after proving it injective. The source explicitly limits “causal” to this encoded prerequisite order and disclaims physical causation or downstream analytic/geometric claims. The finite-poset statements are valid within that scope. Source review only.

## Finite-stage mass-predicate persistence audit (2026-10-31)

`obstruction_persists_in_tower` is a valid nonzero-witness transport result via the injective stage inclusion. The predicate itself is only existence of a nonzero matrix; its Planck parameter is unused and it encodes neither a Heisenberg relation nor a spectral gap. `TopologicalMassGapZeroStageAudit` proves there is no witness at stage zero and refutes the universal all-stages mass-gap predicate. This is a valid persistence lemma over an overnamed finite-carrier predicate, with the scope limitation and counterexample made explicit by the owner modules. Source review only.

## Zero-stage mass-predicate counterexample audit (2026-10-31)

The seven flagged claims establish a stage-one nonzero matrix, impossibility at stage zero, propagation along injective inclusions, and the exact characterization `finite_obstruction_class n ↔ 0 < n`. The universal all-stages predicate is therefore false. This is an explicit finite-carrier counterexample to the encoded universal predicate, not a theorem about an actual colimit or spectral mass gap; the owner says so directly. Source review only.

## Twistor mass finite-stage inclusion audit (2026-10-31)

`colimit_injection_preserves_obstruction` is the injectivity-based transport of a nonzero rectangular matrix witness. Its predicate contains no Heisenberg relation, spectral estimate, or colimit-level content, and its universal all-stage variant is false at stage zero as proved by the companion audit. The implication itself is correct under its finite-stage scope. Source review only.

## Two-point averaging noninjectivity audit (2026-10-31)

`twoPointAverage_not_injective` is witnessed by the distinct inputs `[1,-1]` and `0`, both mapped to zero. The exact kernel and reconstruction results in the owner distinguish this averaging map from invertible frame/link transport; gauge covariance is proved separately with transported inputs and links. The counterexample is valid for the stated two-point real averaging map and does not imply a claim about general attention or noncommutative operator maps. Source review only.

## Odd graph reduction noninjectivity audit (2026-10-31)

`reduction_not_injective` has an explicit witness in the actual exterior algebra on one generator: the odd graph differs from the zero graph, but augmentation kills the generator and makes the reductions equal. The proof uses the native exterior-algebra generator, its nonzero/square-zero facts, and graph-map injectivity. The result is valid for nontrivial coefficient rings, including characteristic two, as a base-change noninjectivity statement for this chart. Source review only.

## Split-octonion monopole polynomial audit (2026-10-31)

`stokes_abelian_obstruction_vs_octonionic_monopole` is a valid expansion of the hand-defined split-octonion product and trace: the modeled derivative has zero trace/supertrace and the modeled curvature supertrace is `-4 det`. The owner contains no differential-form complex, integration, bundle, sphere cohomology, or independently established monopole charge. The charge-quantization formula additionally assumes winding and normalization equations. The polynomial identities are kernel-level algebra; the Stokes/monopole interpretation is not established by them. Source review only.

## Dirac/Hopf integer audit examples (2026-10-31)

The flagged `decide` theorem verifies the trace and supertrace vanish for one explicit integer derivative vector. Sibling checks evaluate the Hopf polynomial and modeled curvature supertrace at selected integer vectors. These are correct finite arithmetic instances and sanity checks; they do not independently certify a Stokes theorem, topological charge, or monopole interpretation. Source review only.

## Finite Cuntz trace obstruction audit (2026-10-31)

`cuntz_finite_matrix_trace_obstruction` validly applies cyclicity of the real matrix trace to force `2·card(m)=card(m)`, hence the finite carrier must be empty; the nonempty-carrier corollary follows. The module explicitly avoids claiming an exact O₂ representation on the UHF colimit. A separate noncommutative owner generalizes the obstruction to cyclic additive traces on associative rings. The flagged result is a valid impossibility theorem, not a false claim/counterexample. Source review only.

## Recovered-invariants repeated Cuntz obstruction audit (2026-10-31)

The flagged theorem is a correct cyclic-trace proof of the finite real-matrix Cuntz obstruction, but duplicates `BohmianCuntzHolomovementPoset.cuntz_finite_matrix_trace_obstruction` with the same conclusion. It adds no distinct mathematical result. The surrounding claim correctly limits the obstruction to finite carriers and does not assert an O₂ action on the UHF colimit. Source review only.

## Negative Clifford lift periodicity obstruction audit (2026-10-31)

`negative_lift_periodic_obstruction` is valid: equivariance twice gives a minus sign under the double glide, while the additional periodicity hypothesis gives equality, forcing each complex field value to zero since `2 ≠ 0`. The result is conditional on both equivariance and periodicity and does not classify Pin bundles or assert a nonzero field exists. Source review only.

## Finite twistor incidence/null equivalence audit (2026-10-31)

`incident_points_null_separated` and its iff companion are valid for the declared 2×2 real soldering map: a shared incidence with nonzero spinor makes the difference matrix singular, while determinant zero supplies a nonzero kernel spinor and hence shared incidence. The owner explicitly limits the result to this finite algebraic model and does not construct geodesics or a light-ray manifold. Source review only.

## Infinity-twistor noninjectivity audit (2026-10-31)

`infinityTwistor_not_injective` is valid: contraction with the lower-spinor determinant has the entire upper-spinor plane as its nontrivial radical, and a concrete nonzero vector there maps to zero. The owner gives the exact kernel and correctly distinguishes this degenerate form from an invertible transformation. Its frame-preservation theorem is restricted to determinant-one frames. Source review only.

## Penrose CCR triple and candidate-product obstruction audit (2026-10-31)

`source_triple_and_obstruction` combines a valid CCR-reduced triple-closure theorem with an explicit failure of left alternativity for the proposed scalar/vector product at `k=1/2`. The witness relies on proved products for a fixed pair. The same owner distinguishes this formula from a separately chosen alternative composition product transported from Zorn and proves the products differ. The result is a valid counterexample to the candidate formula, not to the chosen composition algebra; scope is the stated algebraic carrier. Source review only.

## Real infinity-twistor degeneracy audit (2026-10-31)

The real-carrier theorem has the explicit nonzero upper-spinor vector in the exact radical, so the linear map to the real dual is noninjective. The pairing is also identified with the p23 Plücker minor and a native Clifford anticommutator readout. This is a valid degeneracy statement on the intrinsically real carrier, not an invertible origin/infinity transformation. Source review only.

## Rolling-spinor null-separation forwarding audit (2026-10-31)

`twistor_incident_points_null_separated` forwards the existing finite soldering incidence/null-separation theorem through the `twistorIncidenceGeometry.Inc` interface, retaining the nonzero-spinor premise; the common-point result immediately specializes it. This is a valid interface bridge rather than an independent geometric derivation. It stays in the finite `Vec22` model and does not establish a global rolling/twistor equivalence or de Rham result. Source review only.

## Finite pigeonhole noninjectivity audit (2026-10-31)

`not_injective_of_card_lt` is a correct contrapositive of the finite pigeonhole theorem for maps `Fin M → α`. It is a generic collision result; the theorem alone does not establish a model-specific coherence-time lower bound, which depends on the separate counting estimate and decoder-map instantiation. Source review only.

## Log-auditable phase-circle minimality model audit (2026-10-31)

The flagged deficit exclusion is valid Nat arithmetic: both `auditExponent` and `circleDim` are defined by free rank, so a strict lower value cannot equal the target. The attained ‘witness’ is only an equality proposition in this bookkeeping model; there is no phase-circle object or topological realization in the owner. Thus the formal internal minimality statement is correct, while any topological existence/minimality interpretation is not established. Source review only.

## Fibonacci word append injectivity audit (2026-10-31)

`appendFalse_injective` is valid: restriction is a left inverse to appending `false`, so equality after append implies equality before append. This is a routine constructor injectivity lemma, not an obstruction or noninjectivity counterexample. Source review only.

## Artin visible-hull and entropy-shadow synthesis audit (2026-10-31)

The theorem is valid conditional logic, but the data structure carries determinant-minimality content and the imported ‘Chebotarev witness’ is a custom parity selector with term `c·(±1)`, not a prime-counting statement. Also `dominantCoeff` is not related to `dominantChannel` or `dominantHidden`. So the proposition combines independent hypotheses and proves its declared model statement, but it does not derive an entropy/Chebotarev obstruction for that Artin channel. Source review only.

## Solenoid/finite-ledger synthesis scope audit (2026-10-31)

The theorem validly aggregates the generic-monotheticity package and the prime-register package, but the two inputs are independent and no map or relation connects D to E. `SSolenoidGenericMonotheticData` stores propositions/proofs rather than a concrete topological group, and the localization obstruction is a rank-contradiction predicate that ignores its finite set argument. The source proves this bookkeeping conjunction, not a new analytic interaction between a solenoid and an arithmetic ledger. Source review only.

## Finite operation-table count audit (2026-10-31)

The flagged declarations correctly count all binary operation tables on `Fin n` as `n^(n²)`, giving 16 for order 2 and 19,683 for order 3. They explicitly count arbitrary operations and impose no associativity/group axioms, so they should not be read as counts of algebraic structures. The declarations themselves assert no obstruction. Source review only.
\n## Candidate review: window-6 BinFold `SU(5)` obstruction label\n\n`Omega.Folding.BinFold.conclusion_window6_su5_obstruction` follows from the exact finite fiber maximum `cBinFiberMax 6 = 4`; its paper package states that bound and maximum. The owner defines `cBinFold` as `X.ofNat` and fibers by preimages among `range (2^m)`, with finite extrema evaluated by `native_decide`. Consumers use these multiplicities for combinatorial classifications. The inspected owner and references do not define an `SU(5)` factor or prove a relation that would turn the fiber bound into an obstruction to one. Classification: finite combinatorial theorem verified from source; `SU(5)` interpretation unsupported here.\n
## Candidate review: window-6 BinFold `SU(5)` obstruction label

`Omega.Folding.BinFold.conclusion_window6_su5_obstruction` follows from the exact finite fiber maximum `cBinFiberMax 6 = 4`; its paper package states that bound and maximum. The owner defines `cBinFold` as `X.ofNat` and fibers by preimages among `range (2^m)`, with finite extrema evaluated by `native_decide`. Consumers use these multiplicities for combinatorial classifications. The inspected owner and references do not define an `SU(5)` factor or prove a relation that would turn the fiber bound into an obstruction to one. Classification: finite combinatorial theorem verified from source; `SU(5)` interpretation unsupported here.

## Candidate review: Fold constructibility/rigidity/obstruction package

`Omega.Folding.paper_fold_constructibility_rigidity_obstruction` reuses the actual owner results `Fold_surjective`, `Fold_stable`, and `Rewrite.irreducible_eq_of_value_eq`, then specializes the residual-window reachability theorem to a point mass. The residual profile is explicitly chosen as `t * log (fiberMultiplicity y)`; the final bounds express affine interpolation over `t ∈ [0,1]`. The conjuncts are individually supported, but no implication connects them into a trichotomy, and the residual clause is reachability rather than an obstruction. Classification: correct bundled statements, overstated obstruction/trichotomy naming.

## Candidate review: Fold constructibility/rigidity/obstruction package

`Omega.Folding.paper_fold_constructibility_rigidity_obstruction` reuses the actual owner results `Fold_surjective`, `Fold_stable`, and `Rewrite.irreducible_eq_of_value_eq`, then specializes the residual-window reachability theorem to a point mass. The residual profile is explicitly chosen as `t * log (fiberMultiplicity y)`; the final bounds express affine interpolation over `t ∈ [0,1]`. The conjuncts are individually supported, but no implication connects them into a trichotomy, and the residual clause is reachability rather than an obstruction. Classification: correct bundled statements, overstated obstruction/trichotomy naming.

## Candidate review: exponential-scale injectivity and C-finite surrogate

The lexical candidate `fold_bin_gauge_constant_not_c_finite_exponentialScale_injective` is a valid private helper: strict monotonicity of `r ↦ 2^r` implies injectivity. Context and consumer review found a concrete semantic counterexample in `FoldBinGaugeConstantRecurrenceCounterexample.lean`: this same sequence satisfies an order-one `LinearRecurrence` while its range is infinite. The owner’s `isCFinite` predicate is defined as finite range, and its “generating-function rationality” predicate is definitionally set equal to that surrogate. Therefore the helper is sound, while the surrounding claimed finite-range criterion is false for genuine C-finite sequences. Classification: helper verified; contextual surrogate refuted by a repo-owned counterexample.

## Candidate review: noninjectivity of the constrained left shift

`Omega.X.shift_not_injective` is an explicit valid counterexample on `XInfinity`: the all-false sequence and the sequence true only at index 0 both satisfy `No11Inf`, are distinct at coordinate 0, and have equal shifts. The theorem’s scope is exactly the defined left shift on this carrier.

## Candidate review: signed-companion coefficient mismatch at q=6

`paper_signed_companion_fusion_obstruction` proves the literal finite inequality between the encoded second coefficient at q=6 and `lucasNum 6`; unfolding and `norm_num` verify it. The declaration establishes a mismatch in this table entry only. It neither proves a general fusion obstruction nor independently validates the table against an external recurrence source. The neighboring q=2..23 certificate is exhaustive computation over the declared finite table.

## Candidate review: injectivity of the two-prime Euler phase map

`paper_group_jg_two_prime_euler_phase_injective` proves injectivity of the paired map `t ↦ (exp(i t log p), exp(i t log q))` for distinct primes. Its proof turns equality into integer period equations; a nonzero parameter difference forces both integer periods nonzero, giving a rational logarithm ratio, which contradicts the file’s prime-log irrationality lemma (derived from prime-power uniqueness). Scope is the paired phase map on `ℝ`; no single-coordinate injectivity is asserted.

## Candidate review: scale-lift triple obstruction package

`paper_sm_scale_lift_triple_obstruction` is valid as an implication from the supplied `SmScaleLiftTripleObstructionData`: its tail-patch fields contradict the explicit tail witness, its invariant/nontrivial parity fields contradict permutation invariance on `Fin 3`, its injection field contradicts `Fin 3 ↪ Fin 2`, and its `so(10)` rank-retention field contradicts the supplied rank-at-most-one bound. The record has no proved inhabitant or concrete scale-lift model; notably, `intrinsicChirality` already entails an impossible injection. The proof needs only the tail branch to refute the conjunction. Classification: valid conditional packaging with no instantiated joint model; broad trilemma interpretation exceeds this result.

## Candidate review: window-6 pure F8 Markov-obstruction package

`paper_window6_minimal_markov_obstruction_pure_f8_tail` proves finite indicator values at inputs 0 and 21, the identity `21 = fib 8`, and nonmembership of 21 in the computed two-point fiber-direction spectrum `{34,38,62}`. The imported strong-lumpability theorem separately provides the equal-fold/unequal-transition witness for 0 and 21, but this candidate proposition omits that witness and contains no minimal-memory or Markov-obstruction conclusion. Classification: finite components verified; the proposition does not establish the broader obstruction named in its label.

## Candidate review: `Fin 3` parity obstruction and the m=7 carrier

The abstract theorem is correct: a map `Fin 3 → Fin 2` invariant under all permutations is constant, by the explicit swap argument in `BoundaryLayer`. The purported m=7 fiber, however, is only `abbrev ... := Fin 3` inside a structure containing a parity function; there is no map from a concrete boundary carrier or proof that this is the relevant fiber. In the owner `BoundaryLayer`, `cBoundaryCount` counts stable words with both endpoint bits true and `cBoundaryCount_seven` proves its size is 5. Thus the Fin-3 symmetry statement is an available canonical replacement, but its m=7 boundary application lacks carrier alignment (and would conflict if it means the endpoint-boundary carrier).

## Candidate review: determinant-mod-3 edge-flux obstruction

The generic result in `EdgeFluxMod3Obstruction.lean` is sound: if `3 ∣ det E`, reduction modulo 3 is singular and supplies a nonzero left-kernel functional; linearity makes that functional invariant under adding reduced image vectors. The `n=1` specialization is the coordinate projection. Repo-owned search found no concrete Window-6 edge-flux matrix with a proved determinant-divisibility hypothesis; the named theorems remain conditional on an arbitrary E and h. Classification: valid canonical conditional linear-algebra statement; Window-6 application uninstantiated.

## Candidate review: center 2-torsion dimension obstruction at M2

The reusable lemma `no_injective_linearMap_fin_fun_of_finrank_lt` is the standard finite-dimensional rank obstruction and is proved from the Mathlib injective finrank inequality. The paper-facing corollary specializes it to `ZMod 2`, dimension three, under the hypothesis `finrank V ≤ 1`. Repo-owned search found no actual center 2-torsion module or proved dimension bound connected to the named Foldbin M2 object; the declaration quantifies over arbitrary V and assumes the key bound. Classification: generic theorem verified; domain-specific application remains conditional/uninstantiated.

## Candidate review: Window-6 direction-spectrum linear-kernel label

The implication in `Window6DirectionSpectrumLinearKernelObstruction.lean` is true for its stipulated constants `(1,0)`, `(1,1)`, `(2,1)`: pairwise distinctness contradicts a common value. The file neither imports nor maps from the actual Window-6 fiber-direction data, whose computed spectrum consists of naturals `{34,38,62}`; it also defines no linear map or kernel beyond a proposition asserting one common pair. Classification: elementary surrogate implication verified; the advertised Window-6 linear-kernel obstruction is not derived from the actual spectrum.

## Candidate review: F8 repair channel versus boundary parity

The theorem proves distinctness of two functions on the stipulated `Fin 3 × Bool` carrier: the F8 channel is defined as constantly false and canonical parity is defined as the Bool coordinate. The imported no-covariant-extension result follows from the same definitions. The owner calls constancy a paper input and provides no map from this synthetic carrier to a concrete Window-6 boundary system, nor a theorem identifying an actual F8 repair bit with this constant function. Classification: exact abstract channel separation; concrete boundary application unsupported.

## Candidate review: degree-6 visible coefficient isotropy obstruction

For any supplied `Window6VisibleDegree6Data`, the theorem is correct: each support vector has a zero coordinate, forcing the mixed coefficient to vanish; equality with the radial coefficient pair forces λ=0, contradicting the assumed nonzero axis-six mass. This is a valid coefficient obstruction on the abstract structure. Repo-wide search found no concrete Window-6 support/weight construction or consumer instantiating the data record. Classification: conditional algebraic result verified; application to concrete Window-6 visible data is unverified.

## Candidate review: curvature/carry/Z2 propositional schema

The proof of `paper_pom_curvature_carry_defect_z2_obstruction_principle` is valid as propositional logic: both propositions imply a shared obstruction, and that obstruction realizes both. But the three concepts are only unconstrained `Prop` parameters, with no POM carrier or curvature/valuation/Z2 definitions; the assumptions already encode the desired equivalence. Repo-wide search found no instantiating consumer. Classification: valid generic schema, not a formalized mathematical obstruction principle.

## Candidate review: Lucas polynomial for rational golden powers

`paper_derived_fold_golden_rational_power_unit_obstruction` correctly proves that `u = φ^(a/b)` satisfies `u^(2b) - L_a u^b + (-1)^a = 0` and that the constant term is ±1, via the Lucas Binet formula and `φψ = -1`. This is a genuine algebraic-unit polynomial identity for positive b. By itself it proves no transcendence or irrationality claim; its proposition is generic and does not involve a Fold construction. Downstream wrapper theorems use the parity clause together with separate norm computations. Classification: valid generic lemma; derived-fold interpretation requires additional bridge assumptions/results.

## Candidate review: parity split with vacuous mod-3 criterion

The signed-parity identities are sound and come from `FiberArithmeticProperties`. The extra hypothesis `hmod3` equates signed-sum zero with `∃ ℓ : Nat, ℓ % 3 = 1`, but the existential is always true by `ℓ = 1`. Consequently `hmod3` forces every instance to have signed sum zero, and the final equivalence reduces to `A = B ↔ True`; for unbalanced ±1 data the hypothesis is simply impossible. Classification: parity split verified; the claimed mod-3 obstruction is vacuous/overstrong and needs a nontrivial condition depending on the data.

## Ground-truth contract: exact signed-parity balance

Claim: for a finite set S with sgn(x) ∈ {+1,-1}, let A and B count the +1 and -1 fibers. The canonical identities are `2A = |S| + Σ sgn`, `2B = |S| - Σ sgn`, and `A = B ↔ Σ sgn = 0`. Carrier/operations: `Finset α`, integer-valued signs, and integer casts of finite cardinalities. Owner facts: `Omega.parity_split_identity` and `Omega.parity_split_identity_odd` in `FiberArithmeticProperties.lean`; the defective POM wrapper has no external consumer. Gap: the predicate `∃ ℓ : Nat, ℓ % 3 = 1` is always inhabited by 1 and cannot encode a mod-3 condition on S. Adjacent unproved claims: no mod-3 obstruction follows absent a nontrivial data-dependent congruence. Replace the malformed paper-facing wrapper with the exact parity-balance theorem, with a proof derived from the existing owner lemmas.

## Candidate review: occupancy symmetric-quotient RH wrapper

The wrapper is a valid composition of the generic first-variation growth lemma and the excitation-filter logarithmic bound. Its RH-breaking conclusion is conditional on a supplied spectral implication and on an abstract occupancy predicate holding at every order; it does not instantiate a concrete occupancy quotient. The second clause is conditional on the logarithmic inequality supplied in its hypothesis. Classification: sound conditional composition; broad “occupancy obstruction” interpretation is unsupported without a concrete model and spectral bridge. No in-file theorem consumers were found beyond the POM umbrella import.

## Candidate reviews: right-edge, null-readout, and finite-moment wrappers

- `RightEdgeHeightFreezingObstruction`: proves the finite-list maximum bound for a supplied phase and its immediate positive-gap consequence; the lower bound on `a` is unused. It does not prove freezing or asymptotics.
- `NullAsH2Obstruction`: valid conditional implication from assumed transition-triviality and an assumed vanishing predicate to empty global section/fiber and NULL readout. Its `Cech2` carrier and transitions have no cohomological axioms, so this is not an H² theorem.
- `NullAsLocalSectionObstruction`: correctly combines the readout/fiber criterion with uniqueness from injective restriction data; no concrete cover geometry is supplied.
- `ProuhetThueMorseFluxMoments`: the fixed pair `{0,3}` and `{1,2}` is a valid distinct witness matching moments 0 and 1; `n,r` are decorative hypotheses in the package. Its downstream affine-image result proves degree-2 separation, but the source alone is not a general dyadic/polycube or arbitrary-order theorem.

## Candidate reviews: Galois–Möbius arithmetic wrappers

- Real-input relative-gap theorem: positive twist gap and affine transfer inequality are structure inputs; the conclusion is a valid immediate bound, not a derived obstruction. The resonant split field is unused.
- Real-input and weighted “Smith compute” theorems: each proves the gcd-fold of absolute list weights divides every listed weight. Correct, but not a Smith normal form computation.
- Weighted relative-gap theorem: directly returns the uniform-gap field established by the imported gcd-gap result; “removing obstruction” is packaging language.
- Modular cycle theorem: correctly proves potential iff all directed triangle sums vanish on a complete directed graph under skew weights, constructing the potential from a base vertex. General graph versions need more hypotheses.

## Candidate reviews: character-blind and typed-address packages

- The three character-blind Topos declarations assume all equivalences and implication bridges as propositional hypotheses; two are forwarding wrappers. They are valid propositional packages but do not instantiate a topos, kernel, quotient, or gluing construction.
- Typed-address globalization proves global section ⇒ balanced-loop flatness by commutative-group telescoping; its reverse witness is definitional from obstruction := ¬loopFlat. The minimal model has no Cech class.
- Typed-address instantiation extraction copies four structure fields and proves the projections by `rfl`; it is record projection rather than a derived spacetime theorem.

## Candidate reviews: finite symmetry and abstract Zeta wrappers

- The boundary-free involution theorem correctly proves each compatible finite fiber has even cardinality by restricting a free involution; its named Xi/minimum-cover interpretation has no concrete instance here.
- The DFA quantitative package is only a valid real-inequality consequence of supplied recall/precision bounds; it has no DFA or language model.
- The finite-kernel lattice result is sound inside its explicitly defined toy model, comparing a linear assumed bound to a quadratic toy profile.
- The major-arc equivalence loop composes four assumed implications; it contains no analytic/cyclotomic construction.
- The infinite-rank result is the standard contradiction from requiredRank(k) ≥ k, with no concrete ledger instance.
- The transcendence wrapper assumes the key “algebraic quotient is not transcendental” predicate fact; it does not derive it from algebraicity closure.
