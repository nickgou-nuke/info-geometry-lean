# CAR, supercolor, Zorn, and super-Grassmannian gap audit

> Status: **generated/historical report** — source audit and proposed theorem
> contracts; no new Lean declarations.
> Source review: 2026-11-26.
> Upstream baseline:
> [fe24e350b08fdea04f74c0748ef9fd9417c47529](https://github.com/nickgou-nuke/info-geometry-lean/commit/fe24e350b08fdea04f74c0748ef9fd9417c47529).
> All acceptance targets below have status **[bucket_3_open_debt]** until their
> actual owners and proof checks are available.

This is the CAR/operator-geometry companion to the
[historical gap-closure roadmap](HISTORICAL_GAP_CLOSURE_ROADMAP_2026-11-26.md).
It adds the concrete vacuum-supercolor, Zorn quotient, completed CAR,
pure-spinor inverse, and Berezinian obligations. The broader roadmap retains
the project-wide ordering for support logarithms, generators, Sinkhorn,
statistical geometry, and topology.

## Evidence and publication boundary

Baseline links below refer to files present at the reviewed upstream commit.
The finite Fock operator in [PR #463](https://github.com/nickgou-nuke/info-geometry-lean/pull/463)
was inspected at
892baa629fcb56284a92d06c64d0da803b29125c; it remains an open draft stacked on
[PR #462](https://github.com/nickgou-nuke/info-geometry-lean/pull/462).
The algebraic ABS work in
[PR #465](https://github.com/nickgou-nuke/info-geometry-lean/pull/465)
was inspected at 5ee7def6bdeb7a5ddfff95018456427dbe9ddcdf and remains an open
draft. These are dated observations, not merged-baseline claims.

An earlier session reported a 17-file local CAR-lift implementation at commit
1c6e2665b743959a21eb8b5b59b6a3df27c5949f on branch
formalize/grassmann-car-linear-lift, with scoped checks and a root publication
gate blocked by the missing HomotopyHypothesis path dependency. During this
publication, the original checkout and exact source snapshot were unavailable.
GitHub did not resolve that commit or branch, and the surviving checkouts did
not contain the commit. No complete patch or bundle was recovered.

Accordingly, that earlier implementation is **unpublished session evidence**,
not an upstream dependency or a source snapshot supplied by this document.
In particular, the previously reported ExteriorCARLift, sheet-transport, and
assembled imaginary-Clifford declarations must be recovered or implemented
and freshly checked before downstream work relies on them. This publication
preserves the audit; it does not reconstruct accepted Lean proof bodies from
their descriptions.

Source inspection, link verification, hook execution, and Lean elaboration
are separate checks. No new Lean compilation or declaration-level axiom audit
is claimed for this documentation change. Publication checks are recorded in
the pull request.

The historical sources supply precise theories and hypotheses. They do not
support a blanket claim that these programs were abandoned for lack of a
consistent framework. The useful formalization task is to prove the maps and
compatibility statements between their existing constructions.

## Priority within this mathematical lane

| Priority | Gap | First acceptance target |
|---|---|---|
| P0 | Reproducible source and accurate claims | Recoverable dependency pins, source-backed audit imports, and dated proof scope |
| P1 | Exterior lift and continuous quadratic Fock action | Equality of the actual linear maps, then adjoints and spin trace correction |
| P1 | Fock realization of supercolor | Vacuum-compressed operators instantiate the native common-source system |
| P1 | Zorn Clifford image and kernel | Surjectivity onto real endomorphisms and the exact quotient |
| P1 | Completed all-mode CAR | Cross-mode relations and equality of stage representatives on the existing completion |
| P1 | Pure-spinor geometry | General independent-blade annihilator, followed by a transverse-chart inverse |
| P0/P2 | Berezinian interpretation and geometry | Scope correction first; actual derivative, cocycle, line bundle, and class subsequently |
| P2 | Infinite implementation and topological symbols | Real Hilbert hypotheses, domains, norm limits, and continuous bundle constructions |

Use the native real carriers for the concrete constructions. Keep the
positive Hilbert metric, neutral primal/covector pairing, and Krein adjoint
distinct. Historical complex formulations require an explicit real
formulation compatible with the existing doubled/internal-phase structures;
they do not authorize a new scalar complex unit.

## 1. Reproducibility and source provenance

The root configuration in [lakefile.lean](../lakefile.lean) declares path
dependencies. The earlier CAR publication gate stopped at the unavailable
external_refs/homotopy-hypothesis-lean4 directory. Resolve authoritative
dependency sources and revisions while preserving the configured pins and
the existing gate.

There is also a specific source-inventory issue:
[BKMMetriplecticTrajectorySecondLawAudit](../lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawAudit.lean)
imports InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw, but the
reviewed upstream tree has no tracked owner at that path. Its audit references
do not establish availability of those declarations at this revision.

Acceptance requires recoverable dependencies, actual owners for audit imports,
and separate reporting of scoped compilation and root-package acceptance.
Follow [RUNBOOK](../RUNBOOK.md) and the
[canonical pipeline](CANONICAL_AGENT_PIPELINE.md); do not convert an older
scoped result into a current whole-repository certificate.

## 2. Identify the finite quadratic operator with the exterior lift

**Existing owners.**
[CliffordExteriorLift](../lean/InfoGeometry/Clifford/CliffordExteriorLift.lean)
constructs exteriorLift on the full exterior algebra, proves its generator
action, and proves the even derivation identity over a commutative ring.
The pending
[FiniteRealFockQuadraticAdjoint](https://github.com/nickgou-nuke/info-geometry-lean/blob/892baa629fcb56284a92d06c64d0da803b29125c/lean/InfoGeometry/Clifford/FiniteRealFockQuadraticAdjoint.lean)
constructs the continuous real operator

\[
Q_n(M)=\sum_{i,j}M_{ij}C_iA_j
\]

on the positive occupation-basis Fock carrier. It proves transpose-adjoint
transport and self-adjointness for symmetric real matrices, and explicitly
defers its identification with exteriorLift.

**Acceptance target.** With the actual coordinate basis and covector pairing,
prove the finite-basis formula and then

\[
d\Gamma(T)=\sum_i C(Tb_i)A(b^i),\qquad
Q_n(M)_{\mathrm{underlying\ linear\ map}}
=d\Gamma(\mathrm{Matrix.toLin'}(M)).
\]

Reuse the primal/dual sheets and their nondegenerate cross-pairing when
instantiating this formula. Preserve any hypotheses needed to identify the
dual sheet with the actual linear dual. The earlier unpublished formula is
not a substitute for an available, checked owner.

**Spin normalization target.** For the split convention
\(Q(u,\phi)=\phi(u)\), define

\[
\beta(T)=\frac12\sum_i
[\iota(Tb_i,0),\iota(0,b^i)].
\]

Prove basis independence and

\[
\rho(\beta(T))=d\Gamma(T)-\frac12\operatorname{tr}(T)I.
\]

The scalar correction is obtained from CAR; it vanishes when the trace
vanishes. Connect the result to the actual Lie-span and spin-image owners
[CliffordLieAlgebra](../lean/InfoGeometry/Clifford/CliffordLieAlgebra.lean)
and [Cl55SpinBivectorImage](../lean/InfoGeometry/Clifford/Cl55SpinBivectorImage.lean).
An even creation-contraction product need not itself be a pure bivector.
Araki's quadratic-operator treatment makes the normalization and trace issue
explicit [H2].

**Metric target.** The existing
[ExteriorZornCARIntertwiner](../lean/InfoGeometry/Clifford/ExteriorZornCARIntertwiner.lean)
provides a linear equivalence. For adjoints and Moore-Penrose equations,
prove an isometry or explicitly transport the positive metric:

\[
\langle z,w\rangle_{Z,F}
=\langle U^{-1}z,U^{-1}w\rangle_F.
\]

[ZornDoubledGramObstruction](../lean/InfoGeometry/Krein/ZornDoubledGramObstruction.lean)
already proves zornToDoubleKrein_not_norm_isometry.
[SouriauOnsagerBKMParaKahlerObstruction](../lean/InfoGeometry/Canonical/SouriauOnsagerBKMParaKahlerObstruction.lean)
proves the positive BKM anti-invariance obstruction under its stated
hypotheses. These results constrain the metric identification.

## 3. Instantiate supercolor by vacuum compression

**Existing owners.**
[SuperGrassmannianSusy](../lean/InfoGeometry/Core/SuperGrassmannianSusy.lean)
requires Moore-Penrose conditions, \(d_id_j=0\), \(b_ib_j=0\), and
\(b_id_j=0\) for distinct indices in IsSupercolorSystem.
[SupercolorMultiplication](../lean/InfoGeometry/Core/SupercolorMultiplication.lean)
proves the matrix-unit multiplication law when the source \(b_id_i=q\) is
common. The concrete
[Option-indexed matrix example](../lean/InfoGeometry/Core/SupercolorMatrixExamples.lean)
already realizes that system.

**Acceptance target.** On finite real Fock space, with its genuine orthogonal
vacuum projector \(P_0\), set

\[
D_i=C_iP_0,\qquad B_i=P_0A_i.
\]

Prove

\[
B_iD_j=\delta_{ij}P_0,\qquad D_iD_j=0,\qquad B_iB_j=0,
\]

the positive-adjoint Moore-Penrose equations, IsSupercolorSystem, and the
common-source identity. Then identify its vacuum-plus-one-particle realization
with the existing matrix example. The native multiplication theorem gives

\[
(D_iB_j)(D_lB_m)=\delta_{jl}D_iB_m.
\]

Full Fock bilinears retain the quartic correction

\[
(C_iA_j)(C_lA_m)
=\delta_{jl}C_iA_m-C_iC_lA_jA_m.
\]

Thus the matrix-unit corner and the full quadratic Lie action have different
supports. The identity of the color corner is the one-particle projector.

[RegularCARVacuumSeparation](../lean/InfoGeometry/Algebra/Zorn/RegularCARVacuumSeparation.lean)
already constructs the three-mode vacuum projection and proves it differs
from left multiplication by the Zorn pole.
[SupercolorSourceClosure](../lean/InfoGeometry/Core/SupercolorSourceClosure.lean)
also proves orthogonal_absorption_forces_zero: stronger orthogonal extended
SUSY assumptions must not be silently combined with common-source absorption.

## 4. Determine the exact Zorn Clifford quotient and its grading

**Existing owners.**
[SplitOctonionCliffordNoninjective](../lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean)
proves Clifford dimension 128, endomorphism dimension 64, noninjectivity, and
a kernel dimension lower bound.
[SplitOctonionFureyOperatorLift](../lean/InfoGeometry/Lie/SplitOctonionFureyOperatorLift.lean)
identifies the represented Clifford image with the associative algebra
generated by left multiplications.

**Acceptance target.**

\[
\operatorname{range}\rho=\operatorname{End}_{\mathbb R}(Z),\qquad
\dim\ker\rho=64,\qquad
\mathrm{Cl}(Q)/\ker\rho\simeq_{\mathbb R\text{-alg}}\operatorname{End}_{\mathbb R}(Z).
\]

Reuse the general finite-mode generation theorem in
[Cl55SpinorRepresentationGeneration](../lean/InfoGeometry/Clifford/Cl55SpinorRepresentationGeneration.lean)
at three modes and transport through the actual Fock-Zorn equivalence.
Subsequently identify the central volume idempotent selecting the represented
sector, with its sign checked against the ordered generators.

The intended imaginary-coordinate normalization is

\[
Q(t,u,v)=t^2+v\cdot u,\qquad
U^{-1}L_{(t,u,v,-t)}U=-tP+C(u)+A(v^\flat).
\]

The assembled transport formula was part of the unavailable local work and
remains an acceptance obligation for an upstream owner. Under the
positive-square-first convention this quadratic form has signature \((4,3)\).
Relative to the existing Fock parity \(P\), its parity term is even and the
creation/contraction terms are odd. Prove any required graded representation
on the chosen carrier; the seven-generator action cannot simply be declared
odd for this grading.

The existing doubled
[ZornCliffordRepresentation](../lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean)
is a candidate for a full graded continuation with explicit grading
compatibility. Operator representations and their kernels are the relevant
historical distinction [H4]. Existing
[triality](../lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinTrialityClosure.lean)
and [TKK](../lean/InfoGeometry/Canonical/SplitOctonionTKK55LieEquivalence.lean)
owners should consume the exact representation result.

## 5. Complete all-mode CAR on the positive real completion

**Existing owners.**
[RealFockHilbertCompletion](../lean/InfoGeometry/Clifford/RealFockHilbertCompletion.lean)
has isometric stage maps and a dense stage union.
[RealFockCompletedCoordinateAction](../lean/InfoGeometry/Clifford/RealFockCompletedCoordinateAction.lean)
constructs bounded creation and contraction.
[RealFockCompletedSameModeCAR](../lean/InfoGeometry/Clifford/RealFockCompletedSameModeCAR.lean)
proves same-mode CAR, square-zero laws, and Hilbert adjoints.
[RealFockModeCoherence](../lean/InfoGeometry/Clifford/RealFockModeCoherence.lean)
supplies finite cross-mode relations and mode shifts.

**Acceptance target.** For arbitrary mode birth stages, move both labels to a
common upper stage and prove the completed mixed CAR with the corresponding
Kronecker delta, both same-kind anticommutators, and equality of operators
representing the same shifted mode. Use finite-stage identities and density
on the existing completion.

Next prove the finite-support bound

\[
\left\|\sum_i f_iC_i\right\|\le
\left(\sum_i|f_i|^2\right)^{1/2}.
\]

Coordinate bounds alone immediately yield only an \(\ell^1\) estimate.
The \(\ell^2\) bound and stage coherence permit continuous one-particle
smearing, with \(A(f)=C(f)^*\) and
\(\{A(f),C(g)\}=\langle f,g\rangle I\).

An infinite second-quantized operator requires its actual domain. In the
usual full Fock construction \(d\Gamma(I)\) is the number operator, unbounded
across growing particle sectors. A bounded one-particle coefficient alone
does not prove boundedness of its full second quantization.

## 6. Construct the pure-spinor inverse on an actual chart

**Existing owners.**
[Cl55PositiveGrassmannianFockBridge](../lean/InfoGeometry/Clifford/Cl55PositiveGrassmannianFockBridge.lean)
identifies the positive-chart blade annihilator with \(W\times W^\circ\).
[SplitClifford55PureSpinorGrassmannianBridge](../lean/InfoGeometry/Clifford/SplitClifford55PureSpinorGrassmannianBridge.lean)
provides the forward projective map, and
[Pin55ProjectivePureSpinorGrassmannianEquivariance](../lean/InfoGeometry/Twistor/Pin55ProjectivePureSpinorGrassmannianEquivariance.lean)
proves its equivariance. Arbitrary-rank projective frame independence already
exists in
[GrassmannPluckerMeetAndCircleSpace](../lean/InfoGeometry/Projective/GrassmannPluckerMeetAndCircleSpace.lean).

For both targets, let \(L\) be finite-dimensional over \(\mathbb R\), use the
existing split quadratic space \(L\times L^*\) with \(Q(u,\phi)=\phi(u)\),
and the Chevalley action on
\(\operatorname{SpinorSpace}(L)=\Lambda_{\mathbb R}L\).
Here \(\rho(w)\) denotes the generator action \(\rho(\iota(w))\).

**First target.** For an independent real finite frame with nonzero blade
\(\omega=u_1\wedge\cdots\wedge u_k\) and span \(W\), prove

\[
\operatorname{Ann}_\rho(\omega)=W\oplus W^\circ.
\]

Separate creation and contraction by homogeneous degree; use the existing
blade incidence theorem and the covector annihilator. This removes
incidental positive-minor hypotheses.

**Second target.** For a maximal-neutral plane \(W\) transverse to the fixed
primal sheet, define

\[
K_W=\{\psi:\forall w\in W,\ \rho(w)\psi=0\}.
\]

Prove \(\dim K_W=1\) and
\(\operatorname{Ann}_\rho(\psi)=W\) for every nonzero \(\psi\in K_W\).
This constructs a chart-local inverse to the existing forward map.
Check signs if using a finite exterior exponential to construct the witness.

Chevalley III.1.4 gives the historical one-dimensional joint-kernel theorem;
III.1.9 gives the exterior-exponential normal form [H1]. General pure spinors
can involve several exterior degrees. A local inverse does not yet establish
a global smooth or algebraic equivalence or a half-spin component theorem.

## 7. Bind superchart transitions to actual Berezinian geometry

**Existing owners.**
[FreeSupermoduleChart](../lean/InfoGeometry/SuperGrassmannian/FreeSupermoduleChart.lean),
[GraphChartCocycle](../lean/InfoGeometry/SuperGrassmannian/GraphChartCocycle.lean),
[GradedGraphCocycle](../lean/InfoGeometry/SuperGrassmannian/GradedGraphCocycle.lean),
and [GraphTransitionScalarExtension](../lean/InfoGeometry/SuperGrassmannian/GraphTransitionScalarExtension.lean)
have genuine chart, overlap, grading, and scalar-extension identities.
[GraphChartOddRegression](../lean/InfoGeometry/SuperGrassmannian/GraphChartOddRegression.lean)
uses exterior-algebra coefficients and proves distinct odd points can have
the same reduction. Odd coefficient geometry is already present.

**Immediate scope gap.**
[BerezinianSheafStiefelWhitney](../lean/InfoGeometry/SuperGrassmannian/BerezinianSheafStiefelWhitney.lean)
defines stiefelWhitneyW1 by \((n+q:\mathbb Z/2)\) and orientability by
vanishing of that expression. Its theorem statements establish parity
arithmetic, with no base space, transition cocycle, line bundle, or cohomology
class. Retain the arithmetic result while narrowing its geometric
description until the missing construction is supplied.

**Acceptance sequence.** For the existing fractional transition

\[
T'=(c+dT)(a+bT)^{-1},
\]

prove on a suitable finite-dimensional overlap

\[
D\Phi_T(H)=(d-T'b)H(a+bT)^{-1}.
\]

Keep multiplication order. Specialize to a legitimate supercommutative
coefficient realization, identify the even invertible derivative, compute its
Berezinian, and use the existing transition cocycle to construct the actual
line bundle or sheaf. Only then identify a cohomology class and prove when the
arithmetic sign computes it.

The broader graded associative coefficient generality does not itself imply
ordinary Berezinian hypotheses. A local sign need not define a nonzero global
class: the cocycle could be a coboundary. Leites separates Berezinian
multiplicativity, local supergeometry, and gluing [H3].

## 8. Analytic and topological continuation

These milestones extend the broader roadmap rather than replace it.

- **Actual restricted implementation.**
  [RestrictedSheetContinuous](../lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean)
  packages an arbitrary closure-stable SheetRestriction and a doubled-sheet
  lifted operator. Its ShaleStinespringEquiv name does not construct a Fock
  implementer or identify a Hilbert-Schmidt condition. Araki's complex
  self-dual formulation uses a positive complex Hilbert space, an antiunitary
  involution \(\Gamma\), a basis projection
  \(P=P^*=P^2\) with \(\Gamma P\Gamma=I-P\), and a unitary \(V\) with
  \(V\Gamma=\Gamma V\). The criterion is that \((I-P)VP\) be Hilbert-Schmidt
  [H2]. Supply the corresponding real formulation
  on the actual completed CAR representation and its internal phase.
- **Interacting norm limits.**
  [CuntzBoundaryCouplingObstruction](../lean/InfoGeometry/Canonical/CuntzBoundaryCouplingObstruction.lean)
  proves exact compatibility for its specified boundary \(ZZ\) coupling only
  at zero coupling. Seek finite-volume Duhamel estimates and uniform
  compact-time norm limits on local observables for stated interaction
  hypotheses. [LiebRobinsonBounds](../lean/InfoGeometry/Algebra/LiebRobinsonBounds.lean)
  currently proves covariance, not a quantitative propagation estimate.
  The original finite-range norm estimate is the relevant historical target
  [H5].
- **Same-carrier modular identification.**
  [FiniteSeedRepresentedAnalyticKMS](../lean/InfoGeometry/Canonical/FiniteSeedRepresentedAnalyticKMS.lean)
  already proves actual strip properties and constructs the finite-seed KMS
  state. The next identification is between the actual closed Tomita core,
  \(S^*S\), and the implemented dynamics on the original GNS Hilbert carrier.
  [FilteredGNSTomitaModularHilbertCompletion](../lean/InfoGeometry/Canonical/FilteredGNSTomitaModularHilbertCompletion.lean)
  is a separate positive-form completion and requires an explicit comparison.
- **Continuous ABS symbols.** Preserve #465's algebraic symbol result.
  Construct a continuous bundle map invertible on the required boundary,
  then a relative \(KO\) class. With a positive metric,
  \(c(v)=C(v)-A(v^\flat)\) satisfies \(c(v)^2=-\|v\|^2I\), giving invertibility
  for nonzero \(v\). The split square identity alone does not give this
  off-zero conclusion in the presence of nonzero null vectors. ABS separates
  graded modules, difference bundles, and the topological comparison [H6].

## Implementation acceptance

The first focused batch is the finite quadratic/exterior identification and
trace correction, followed by the vacuum-supercolor realization. Completed
all-mode CAR and the independent-blade annihilator are additional contained
targets. The exact Clifford quotient and superchart geometry can proceed in
separate owner-aligned work.

For each target, record the existing carrier, operations, actual hypotheses,
reused declarations, intended equality or equivalence, consumers, and adjacent
claims that remain open. Keep proofs native to Lean/Mathlib, preserve
noncommutative content and real scalar conventions, and use the maintained
serialized verification wrappers. Source review and proposed proof routes do
not close these targets.

## Primary historical references

- **[H1]** Claude Chevalley, *The Algebraic Theory of Spinors* (1954),
  III.1.4 and III.1.9.
  [Original text in collected-works reprint](https://w.rexresearch1.com/SpinorsLibrary/AlgebraicTheorySpinorsCliffordalgebras2.pdf).
  The relevant correspondence assumes finite dimension, nondegeneracy, and
  maximal Witt index.
- **[H2]** Huzihiro Araki, *On Quasifree States of CAR and Bogoliubov
  Automorphisms*, Publ. RIMS 6 (1970/71), 385-442, sections 7-9 and Theorem 7.
  [Publisher PDF](https://content.ems.press/assets/public/full-texts/serials/prims/6/3/2511/online/10.2977-prims-1195193913.pdf).
  Preserve its positivity, conjugation, normalization, and implementation
  hypotheses when formulating a real counterpart.
- **[H3]** D. A. Leites, *Introduction to the Theory of Supermanifolds*,
  Russian Mathematical Surveys 35:1 (1980), 1-64, sections 1.7 and 3.1.
  [Official article and DOI](https://www.mathnet.ru/eng/rm3160).
- **[H4]** J. Schray and C. A. Manogue, *Octonionic Representations of
  Clifford Algebras and Triality*,
  [author preprint](https://arxiv.org/pdf/hep-th/9407179).
  Its compact-signature examples do not by themselves establish a
  split-signature classification.
- **[H5]** E. H. Lieb and D. W. Robinson, *The Finite Group Velocity of
  Quantum Spin Systems*, Communications in Mathematical Physics 28 (1972),
  251-257. [Original paper scan](https://www-thphys.physics.ox.ac.uk/talks/CMTjournalclub/sources/LR.pdf).
- **[H6]** M. F. Atiyah, R. Bott, and A. Shapiro, *Clifford Modules*,
  Topology 3, Supplement 1 (1964), 3-38, sections 9, 11, and 12.
  [Original paper](https://www.math.ens.psl.eu/~benoist/refs/ABS.pdf).
