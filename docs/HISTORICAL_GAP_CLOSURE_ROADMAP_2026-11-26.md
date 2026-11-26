# Historical foundations and urgent gap-closure roadmap

> Status: `generated/historical report` — documentation-only source audit and
> proposed theorem contracts.
> Reviewed: 2026-11-26.
> Baseline: [`fe24e350b08fdea04f74c0748ef9fd9417c47529`](https://github.com/nickgou-nuke/info-geometry-lean/commit/fe24e350b08fdea04f74c0748ef9fd9417c47529).
> Pending work is identified by exact pull-request heads below.
> Proposed milestones have status `[bucket_3_open_debt]`; this report does not
> promote them to Lean theorems or certify a fresh build of the inspected owners.

## Main finding

The most urgent work is to construct the maps, domains, quotients, and limits
that connect existing results. The repository already contains substantial
noncommutative Clifford algebra, real Hilbert-space analysis, GNS and Tomita
constructions, differential calculus, and finite statistical geometry. More
terminology or additional assumption bundles would leave the important gaps
open.

The historical literature supplies precise intermediate problems. Most of
these theories were developed successfully and remain active; they should not
be described collectively as abandoned for lack of a universal framework.
Fortet's early work on the Schrödinger system is a narrower documented case of
neglect: Essid and Pavon's reconstruction discusses difficult exposition and
missing steps in its reception [H3]. That history supports recovering useful
proof methods, without asserting a common historical cause for every field.

The priorities below are engineering judgments about dependency value and
proximity to current owners. The proposed order is a work plan, not a
kernel-derived dependency graph or a claim that all lanes depend on each other.

| Priority | Missing construction | First measurable endpoint |
|---|---|---|
| P0 | Reproducible integration and faithful scope reporting | Exact revision, dependency availability, selected build coverage, and separate archival/maintained-source findings |
| P1 | Support-restricted logarithm | A logarithm on the actual retained subspace and the correct ambient compression identity |
| P1 | Concrete strongly continuous flow and generator | Strong continuity, derivative equality, and the converse domain characterization for `U_unb` and `K_max` |
| P1 | Sinkhorn convergence and information projection | Convergence of the actual iterates to the unique scaled coupling and KL minimizer |
| P2 | Fock/exterior identification | Equality on the full exterior carrier, with Lie commutators and Hilbert adjoints preserved |
| P2 | Statistical Hessian and identifiable quotient | A continuous bilinear Hessian and a positive metric on the quotient by invisible directions |
| P2 | KKS quotient and CE graph integrability | Actual quotient form; graph closure equivalent to a differential closedness condition |
| P2 | ABS module classes and continuous symbols | Actual finite graded-module comparison, followed by continuous sphere/hemisphere constructions |
| P3 | State-derived modular operator, continuous core, and infinite-dimensional bounded phase | Native operator domains and adjoints, crossed-product covariance, and a noncompact Fredholm phase with compact defects |

## Evidence boundary and existing pending work

The audit inspected declarations, imported structures, alternate formulations,
and consumers in both `lean/` and `src/`. It used the repository's
[deep-search protocol](REPO_DEEP_SEARCH_PROTOCOL.md),
[epistemic compilation workflow](../skills/epistemic-compilation/SKILL.md), and
[theorem-contract discipline](ALCHEMICAL_QMS_SOP.md). An absence finding means
that the specified construction was not found in the inspected owners and
searched consumers; it is not an exhaustive nonexistence theorem about every
historical file.

The context preflight used:

```bash
python3 tools/infra/context_preflight.py \
  'Sinkhorn scaling convergence modular logarithm Clifford symbol symplectic reduction' \
  --include-external --json --top 5 --token-limit 7
```

The checkout did not provide current `artifacts/dag/index/decls.jsonl`,
`types.jsonl`, or `manifest.json`, `artifacts/leansearch_local/records.jsonl`,
or `artifacts/raw_infotree`. No fresh global declaration-DAG certificate or
external-reference proof authority is claimed. The conclusions use directly
inspected source and primary literature. No Lean compilation was performed
as part of the read-only mathematical audit.

The following open PRs were checked on 2026-11-26. Their work must be considered
before opening overlapping implementation tasks. Draft status does not mean
the source is absent; an open PR is also not merged baseline functionality.

| PR | Observed state and scope | Exact head |
|---|---|---|
| [#465](https://github.com/nickgou-nuke/info-geometry-lean/pull/465) | Draft; algebraic graded Clifford ABS symbols | `5ee7def6bdeb7a5ddfff95018456427dbe9ddcdf` |
| [#464](https://github.com/nickgou-nuke/info-geometry-lean/pull/464) | Draft; real Bessel–Hagen Maxwell currents | `867f6cca98b25fb76475f638ed9de473652c380c` |
| [#463](https://github.com/nickgou-nuke/info-geometry-lean/pull/463) | Draft; finite real Fock quadratic adjoints and uncertainty; stacked on #462 | `892baa629fcb56284a92d06c64d0da803b29125c` |
| [#462](https://github.com/nickgou-nuke/info-geometry-lean/pull/462) | Draft; real phase observable uncertainty and ordered commutators | `ed3b8e22b61aff0d75ab79525c18779eb01454b0` |
| [#461](https://github.com/nickgou-nuke/info-geometry-lean/pull/461) | Open, non-draft; real Clifford uncertainty and Schwartz wavelet transport | `2f50a6b95eaac927f001047b23356312d6e4b91a` |
| [#456](https://github.com/nickgou-nuke/info-geometry-lean/pull/456) | Open, non-draft; attention Gibbs duality, Fisher geometry, and real-position RoPE | `4ad85fc6e5f2ffb8d178efffecd43922e76b6460` |

Links to baseline owners below are relative to this report's repository tree.
Pending-owner links are fixed to their reviewed PR heads. Recheck source and
PR state when implementing a milestone.

## P0. Make integration evidence reproducible and claims match statements

The pinned environment is Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, as recorded in
[lean-toolchain](../lean-toolchain) and [lake-manifest.json](../lake-manifest.json).
The ordinary publication gate for ABS #465 failed locally because the path
dependency `external_refs/homotopy-hypothesis-lean4` was unavailable. Its focused
source compilation and axiom audit do not repair that dependency or establish
whole-package coverage; #465 records the separate results.

The [observed sorry-gate job for #465](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45842479844/job/139987474906)
ran `python3 tools/quality/repo_lean_scope_audit.py --fail-on tracked` and exited
1. It reported 878 findings in 91 files: all 878 were classified
`forensic_or_fixture`, with zero classified `lake_package` or
`unclassified_nonpackage`. These are the scanner's lexical categories, not
878 established proof holes in maintained mathematical owners and not a
certificate that all maintained proofs are sound.

**Acceptance target.** Reproduce the selected owner checks from the pinned
checkout, record missing dependencies separately from theorem failures, and
adopt an explicit policy for archival fixtures versus promoted owners. Preserve
strict checks for promoted Lean source. Changing a gate's scope needs its own
review; this report proposes no workflow edit or silent relaxation.

In parallel, correct names and prose where a statement establishes a smaller
result: a normalization-step inequality is not convergence, an assumed
logarithm is not a construction, and a function on an ambient carrier is not
yet a quotient form. The following sections identify the missing theorem
instead of inferring failure from a filename.

## P1. Construct logarithms on the actual support

**Existing owners.**
[RealSupportCoercivity](../lean/InfoGeometry/Analysis/RealSupportCoercivity.lean)
constructs `supportProjection` onto `T.kerᗮ`, proves its range, kernel,
idempotency and symmetry, and proves
`gap_defect_positive_iff_support_bound` for arbitrary finite-dimensional real
positive operators. In mathematical notation its conclusion is

$$
(T^2-cT)\geq0\quad\Longleftrightarrow\quad T-cP\geq0,
\qquad P=P_{\ker(T)^\perp}.
$$

[CertifiedInverseKernel](../lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean)
correctly records chosen Drazin and Moore–Penrose inverses with their equations.
The gap is not the existence of that interface.
[CertifiedModularReduction](../lean/InfoGeometry/Canonical/CertifiedModularReduction.lean)
receives `logAdmissible`, `logOn`, and `logDomain` as fields.
`log_defined_on_Δreg` consequently projects supplied data.
`RegularSpectrumPositive` tests the real spectrum of the ambient compression
`P * Δ * P` against the strictly positive half-line.

If `P` has a nonzero kernel, that ambient compression has a zero mode. Strict
positivity of its entire ambient spectrum is different from positivity on
the retained support. This is a mathematical consequence of the displayed
definition, not a newly compiled counterexample in this report.
[PositiveMeasureSpectrum](../lean/InfoGeometry/Canonical/PositiveMeasureSpectrum.lean)
already has a support-sensitive pointwise predicate, while its spectral
discharge still requires ambient strict positivity.
[LogarithmicResolventPositivity](../lean/InfoGeometry/OperatorAlgebra/LogarithmicResolventPositivity.lean)
uses actual native `CFC.log`; functional calculus is therefore already a
reusable resource.

**Next theorem.** On a finite-dimensional real Hilbert space, restrict a
positive `T` to `ker(T)ᗮ`. Prove positivity and invertibility on that carrier,
construct its logarithm `L`, and prove `exp L = T_support`. Handle the zero
support explicitly when a functional-calculus API requires a nontrivial
carrier. For the ambient extension `K` of `-L` by zero, prove

$$P\exp(-K)P=T.$$

The uncompressed identity `exp(-K) = T` is false for singular `T`: the
exponential is the identity on the discarded complement. A rank-deficient
example such as `diag(1,0)` should exercise this distinction.

Connect the nonzero-support construction to the certified modular interface
by actual carrier maps and exponential identities. Its present `logDomain`
and `noLogOnDefect` fields exclude `Δ = 0`; handle that case outside this
interface unless its boundary is deliberately redesigned. Instantiate the
inverse kernel from the chosen positive operator: the existing `cik.A` and
`Δ` fields are independent, so their support alignment cannot be presumed.
Keep positivity/self-adjointness explicit; an arbitrary real operator's real
spectrum can be empty and is not sufficient positive-operator data.
Keep Drazin spectral support and Moore–Penrose metric support distinct until
alignment is proved. Entrywise
positive bistochastic matrices can have deficient rank, so matrix balancing
alone cannot supply a full density inverse. Araki's nonfaithful-state extension
[H4] provides the relevant historical support discipline.

## P1. Prove that the concrete flow has the concrete generator

**Existing owners.**
[UnboundedHilbertResolventAndC0GroupWitness](../lean/InfoGeometry/OperatorAlgebra/UnboundedHilbertResolventAndC0GroupWitness.lean)
contains the real `ℓ²` flow `U_unb`, its group and isometry laws, `D_fin_dense`,
the maximal domain `D_max`, `K_max`, `K_max_skew_symmetric`,
`K_max_is_unbounded`, and genuine two-sided resolvent identities.
Its `C0GroupGenerator` record does not require strong continuity or an equation
identifying the derivative of `U` with `K`. Thus its `unboundedC0Group`
constructor does not establish those analytic facts.

[TripotentUnboundedResolventFlow](../lean/InfoGeometry/OperatorAlgebra/TripotentUnboundedResolventFlow.lean)
has a separate generator contract with `hasDerivAt_gen`,
`mem_domain_of_hasDerivAt`, and `gen_eq_of_hasDerivAt`. Its
`c0_group_commute_implies_domain_intertwining` uses those fields substantively.
That contract itself does not include density, isometry, or explicit
all-vector strong continuity; preserve those as separate concrete results.

**Next theorem.** For the existing `U_unb` and `K_max`, prove

$$
\forall x,\ \operatorname{Continuous}(t\mapsto U_t x),
\qquad
\forall x\in D_{\max},\ \left.\frac{d}{dt}U_t x\right|_{t=0}=K_{\max}x.
$$

Prove the converse domain characterization: if the strong derivative at zero
exists, then `x ∈ D_max`, with the displayed derivative. Instantiate the
existing derivative contract and consume its domain-intertwining theorem.
Finite-support approximation and control of the `ℓ²` tails are a proposed proof
route. The continuity required is on each vector, not operator-norm continuity
of the group. This is the specific analytic obligation behind the classical
one-parameter-group framework [H5].

## P1. Prove Sinkhorn convergence and the KL projection theorem

**Existing owners.**
[SinkhornFoundation](../lean/InfoGeometry/Canonical/SinkhornFoundation.lean)
constructs row/column normalization, admissible steps, and trajectories.
`trajectoryLyapunovNext_eq_zero` states that the phase-aligned residual after
normalizing that phase is zero. `trajectoryLyapunov_monotone` compares that
post-step residual with the corresponding pre-step residual. It does not
prove that both marginal errors tend to zero or that the trajectory converges.
The same owner explicitly proves the post-step zero identity before the
inequality. Its stronger convergence docstring should be corrected when this
owner is next edited.

`sinkhornStep_regularizedObjective_monotone`, its entropic OT and Bayesian
aliases, and `schroedingerBridgeStep_monotone` compare these phase residuals;
they do not establish descent of the actual entropic objective.
[FiniteLogSinkhorn](../lean/InfoGeometry/Routing/FiniteLogSinkhorn.lean)
provides an explicit log-space recurrence, factorization, and column
normalization with an appropriately bounded scope.
[PoissonSinkhornDualCertificate](../lean/InfoGeometry/Inference/PoissonSinkhornDualCertificate.lean)
has useful finite Gibbs inequalities but receives a doubly stochastic coupling
rather than constructing the coupled optimizer. Searches also inspected
alternating-projection and topological normalization owners and their consumers.

**Next theorem.** Begin with nonempty finite index sets, an entrywise strictly
positive kernel `K`, and strictly positive target marginals with equal mass.
Construct the alternating updates and prove:

1. A scaled coupling `P* = diag(u) K diag(v)` exists with the prescribed marginals.
2. The coupling `P*` is unique; the scaling factors are unique up to the
   appropriate reciprocal scalar gauge in this positive setting.
3. The actual matrix iterates tend to `P*` in the finite-dimensional topology.
4. `P*` is the unique minimizer of the generalized KL divergence to `K` over
   the feasible couplings, with its information-projection identity.

For example, with the standard generalized finite KL convention, the expected
identity for feasible `P` is

$$D(P\Vert K)=D(P\Vert P_*)+D(P_*\Vert K).$$

State the zero-entry convention and marginal constraints explicitly. Then
extend to kernels with structural zeros under the appropriate support and
feasibility conditions. Sinkhorn–Knopp's square bistochastic total-support
criterion [H1] must not be transplanted unmodified to arbitrary masked,
rectangular, or nonuniform-marginal problems. Disconnected support also changes
the gauge freedom. Csiszár's information-projection framework [H2] and the
reconstruction of Fortet's proof [H3] provide concrete proof routes.

These results would justify the stochastic and optimization interpretation.
Identifying the iteration parameter with a modular or physical time remains
a separate construction and theorem.

## P2. Identify finite Fock operators with exterior derivations

**Existing owners.** Pending [FiniteRealFockQuadraticAdjoint at #463](https://github.com/nickgou-nuke/info-geometry-lean/blob/892baa629fcb56284a92d06c64d0da803b29125c/lean/InfoGeometry/Clifford/FiniteRealFockQuadraticAdjoint.lean)
uses the existing positive finite exterior Fock model and constructs the
quadratic operators and adjoint identity

$$Q(M)=\sum_{i,j}M_{ij}C_iA_j,\qquad Q(M)^\dagger=Q(M^{\mathsf T}).$$

Here `C_i` acts after coordinate contraction `A_j`.
[CliffordExteriorLift](../lean/InfoGeometry/Clifford/CliffordExteriorLift.lean)
already constructs `exteriorLift`, its action on generators, and its derivation
law. The missing step is equality of the two constructions on their actual
shared exterior carrier.

**Next theorem.** With `T_M(v) = M.mulVec v`, prove that the underlying linear
map of `fockQuadraticCLM n M` equals `CliffordExteriorLift.exteriorLift T_M`.
Prove the equality in every exterior degree, exercising the vacuum, degree
one, and degree two, and derive

$$[Q(M),Q(N)]=Q(MN-NM).$$

Second quantization here is a Lie-algebra representation. The associative
identity `Q(MN) = Q(M)Q(N)` is not the target. Include an explicit pair of
noncommuting symmetric real `2 × 2` matrices and retain the nonzero commutator
on the one-particle sector. A later nonzero phase-commutator expectation also
needs a suitable doubled state with both real legs populated.

Pending #462 already proves real phase Robertson–Schrödinger uncertainty for
Hilbert-self-adjoint observables that individually commute with the internal
phase. It does not assume that the observables commute with each other. Reuse
that theorem and #463's adjoint result through the new identification.

Any later Fock-to-Zorn transport needs a positive-metric isometry or a proved
pulled-back metric law, together with the required phase and grading
intertwining. An algebraic linear equivalence alone does not transport a fixed
Hilbert adjoint unchanged. Hilbert adjoint, Krein adjoint, grading, and internal
square-minus-one phase remain separate structures.

Pending #461 also contains genuine Schwartz integration by parts and a
conditional wavelet transport theorem. The next wavelet milestone is an
actual admissible real analysis transform, its norm identity, and the needed
intertwining derived from its integral definition. Maximal self-adjoint
closures and a full general wavelet theorem are additional obligations.

## P2. Construct the statistical Hessian on the identifiable quotient

**Existing owners.** Pending [AttentionQueryGeometry at #456](https://github.com/nickgou-nuke/info-geometry-lean/blob/4ad85fc6e5f2ffb8d178efffecd43922e76b6460/lean/InfoGeometry/Canonical/AttentionQueryGeometry.lean)
has a genuine log-partition potential, Fréchet first derivative, directional
second derivatives, and a Fisher variance expression. For nonzero inverse
temperature, its null directions are exactly those on which every key
functional has the same value.

**Next theorem.** Construct the full continuous bilinear second Fréchet
derivative and identify it with the Fisher covariance. Define

$$N=\bigcap_{j,k}\ker(K_j-K_k)$$

and construct a positive definite metric on `E / N`, retaining the nonzero
temperature hypothesis. The probabilities and Hessian descend to the
quotient. The log-partition potential itself changes by a common linear term
along `N`; subtract a reference-key linear functional, or state the affine
gauge, before claiming that the potential descends.

This is the appropriate statistical input for the dual affine/Hessian program
of Amari and Shima [H6, H7]. A further compatible almost-complex structure,
closed two-form, and integrability theorem are required for a Kähler claim.

There is an immediate scope check in `SinkhornFoundation`: its
`kahlerPotentialRN` is the negative sum of log row sums and log column sums.
Its restriction to doubly stochastic matrices is identically zero. Therefore
that restricted function cannot produce a positive intrinsic Hessian metric
on nonzero tangent directions of the Birkhoff manifold. This is an inference
from the formula, not a new Lean theorem in this report.
[ProjectiveHessianMetricJClosure](../lean/InfoGeometry/Geometry/ProjectiveHessianMetricJClosure.lean)
and [KahlerSouriauInformationBridge](../lean/InfoGeometry/QuantumGeometry/KahlerSouriauInformationBridge.lean)
provide useful compatibility interfaces; their supplied structures should be
connected to the actual statistical metric rather than used to assume it.

## P2. Build the KKS quotient and differential graph integrability

### The actual KKS radical quotient

[SouriauKKSForm](../lean/InfoGeometry/Canonical/SouriauKKSForm.lean)
constructs `kksForm μ X Y = μ ⁅X,Y⁆`, with bilinearity, skewness, and the
cyclic Jacobi identity under its declared Lie-algebra hypotheses.
[SouriauCoadjointOrbitSymplecticReduction](../lean/InfoGeometry/Canonical/SouriauCoadjointOrbitSymplecticReduction.lean)
proves invariance under adding a supplied isotropy element, assuming nullity.
Its `reducedKKSForm` still takes two elements of the ambient `L`; its
`marsden_weinstein_pullback_identity` is a definitional equality there.
[SouriauKKSLeafRestriction](../lean/InfoGeometry/Canonical/SouriauKKSLeafRestriction.lean)
has a genuine restriction but assumes the relevant annihilator-triviality
condition for nondegeneracy.

**Next theorem.** With `[LieRing L] [LieAlgebra ℝ L]` and
`μ : Module.Dual ℝ L`, define
the actual radical submodule

$$\mathfrak h_\mu=\{X\mid\forall Y,\ \mu([X,Y])=0\}.$$

Lift the form to `L / hμ` and prove

$$\overline\omega_\mu([X],[Y])=\mu([X,Y]),$$

alternation, and both left- and right-nondegeneracy from the choice of the
full radical. Native `LinearMap.liftQ₂` provides the quotient-lifting API.
Quotienting by a smaller arbitrary isotropy submodule would not suffice.
This is a
vector-space quotient: a coadjoint stabilizer need not be an ideal, so no
quotient Lie bracket is implicit. The algebraic construction does not need
finite dimensionality. Identification with a smooth orbit tangent space and
differential closedness are later milestones.

### CE closedness should control graph closure

[DerivationExteriorCalculus](../lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean)
already constructs `actionExteriorDerivative`, its Cartan recurrence, and
square-zero theorems for a `LieActionLane`.
[NeutralPhaseSpaceCore](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
constructs the neutral space `E × E*` and proves its nondegeneracy under the
stated projectivity hypothesis.
[PhaseSpaceGeneralizedMetric](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)
constructs a skew `BFieldDatum` and its invertible algebraic B-transform.
Existing Chevalley/pure-spinor owners already supply substantial isotropic
geometry. Differential involutivity is the missing next condition.

**Next theorem.** Start with a real Lie algebra and trivial action on real
coefficients. Reuse `actionExteriorDerivative` through
`LieActionLane ℝ ℝ`; the more specialized `DerivationLieLane` has a
faithfulness requirement and is not a valid zero-action replacement for a
general nontrivial Lie algebra. Supply the needed degree-one/two adapters at
the action-level API.

With conventions fixed explicitly, define on `L × L*`

$$
[(X,\xi),(Y,\eta)]_D=
([X,Y],\mathcal L_X\eta-\iota_Yd_{\rm CE}\xi).
$$

For a skew bilinear form `B`, prove that its actual graph submodule is closed
under this bracket exactly when `d_CE B = 0`. For the plus-sign transform
`eᴮ(X,ξ) = (X,ξ + B(X,·))`, the corresponding defect target is

$$
[e^Bu,e^Bv]_D-e^B[u,v]_D
=(0,\ Z\mapsto(d_{\rm CE}B)(X,Y,Z)).
$$

Use the existing first-slot insertion convention: on a one-form,
`(d ξ)(X,Y) = -ξ([X,Y])`. The current neutral bilinear pairing is
`ξ(Y) + η(X)`, without a factor of one half. Extract a metric-independent
B-transform for this theorem and prove compatibility with the existing
generalized-metric method; graph closure needs no metric duality equivalence.

This first milestone is the cotangent semidirect-product Lie bracket over a
point. It does not by itself construct a smooth Courant algebroid. The smooth
graph theorem and the double of a Lie bialgebroid give precise later targets
[H8, H9]. An eventual groupoid milestone should start with the pair groupoid of
a finite-dimensional real symplectic vector space and the actual form
`pr₁*ω - pr₂*ω`, proving smoothness, closedness, nondegeneracy, and
multiplicativity. General integration requires its genuine obstruction
hypotheses [H10].

## P2. Connect ABS algebra to actual module classes and topology

**Existing owners.**
[Cl11GradedTensorMorita](../lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean)
already supplies an actual graded tensor cancellation and module-category
equivalence, including noncommutative coefficients.
[KahlerHestenesJWABSPrimary](../lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean)
has `absModuleCat`, `absRestrictionFunctor`, the arithmetic map
`absZeroStepRestrictMonoid : ℕ →+ ℕ × ℕ`, and `absCokernelZeroEquivInt`.
The arithmetic cokernel is a real quotient-group theorem. The inspected owner
does not identify its input monoids with isomorphism classes of actual finite
graded Clifford modules.

Pending [AtiyahBottShapiroSymbol at #465](https://github.com/nickgou-nuke/info-geometry-lean/blob/5ee7def6bdeb7a5ddfff95018456427dbe9ddcdf/lean/InfoGeometry/Canonical/AtiyahBottShapiroSymbol.lean)
constructs the real grading eigenspaces, their complementarity, and the
algebraic symbol equivalence

$$\sigma(v)=-c(v):W^-\longrightarrow W^+,$$

with inverse `-Q(v)⁻¹ c(v)` when `Q(v) ≠ 0`. On the negative unit sphere the
inverse is `+c(v)`. It also has finite rank equality and nonzero examples.
Its graded-module object construction does not assert a classification of
all finite graded modules or a topological KO class.

**Next algebraic theorem.** Define the finite-real-carrier subcategory and
identify both isomorphism-class monoids: graded `Cl(0,0)` modules with
`ℕ × ℕ`, and graded `Cl(0,1)` modules with `ℕ`. For the latter construct the
actual graded-module isomorphism to `V ⊕ V` with

$$\Gamma(x,y)=(x,-y),\qquad c(e)(x,y)=(-y,x).$$

Prove direct-sum compatibility and the commuting square in which actual
restriction becomes `n ↦ (n,n)`. Only then does the existing arithmetic
cokernel compute the stated module-class cokernel. This zero-step
classification does not require a full `Cl(0,8)` theorem.

**Next topological theorem.** For a finite-dimensional real graded module `W`
over a finite-dimensional real Euclidean `V` with `Q(v) = -‖v‖²`, construct
the continuous symbol family and continuous inverse
on the unit sphere on their actual topological carriers. Given an additional
odd negative Clifford generator `J` with `J² = -id` and
`J c(v) = -c(v) J`, construct the hemisphere extension

$$-c(v)-tJ,\qquad (c(v)+tJ)^2=(Q(v)-t^2)\,\mathrm{id}.$$

Prove invertibility on the hemisphere `‖v‖² + t² = 1`, `t ≥ 0`, with inverse
`c(v) + tJ`, continuity, and agreement
with the boundary symbol. The relative KO conclusion requires the actual
bundle/stabilization/homotopy quotient, additivity, and invariance under module
isomorphism. The original ABS paper [H11] separates these steps. Split
`Cl(1,1)` cancellation and a mod-eight signature table do not alone establish
the definite real eightfold Bott comparison. The continuous symbol theorem
can proceed independently of the isomorphism-class monoid comparison. An
isometry claim would additionally require compatibility with a chosen
positive inner product.

## P3. Complete the analytic constructions without replacing their carriers

### From the closed Tomita operator to the modular operator

The repository already constructs finite faithful Tomita closability,
[a closed Tomita operator](../lean/InfoGeometry/Canonical/FilteredGNSTomitaClosedOperator.lean),
[its positive modular form](../lean/InfoGeometry/Canonical/FilteredGNSTomitaModularForm.lean),
and [the form-quotient Hilbert completion](../lean/InfoGeometry/Canonical/FilteredGNSTomitaModularHilbertCompletion.lean).
[FilteredGNSTomitaRealColimit](../lean/InfoGeometry/Canonical/FilteredGNSTomitaRealColimit.lean)
already provides `closedTomitaOperatorRealLinearMap`; realification should be
reused. The closed domain contains the dense embedded PreGNS core, so exposing
its density is an API lemma to derive from the construction, not a new
arbitrary analytic assumption.

The next target is a native `LinearPMap` on the same original GNS Hilbert
space, identifying its graph and dense domain, followed by the positive
self-adjoint operator `Δ = S†S` with its actual composition domain. Relate its
form to `closedTomitaModularForm`. Completing a form quotient does not itself
construct that operator on the original space.

Then derive polar conjugation and modular powers, and prove algebra
invariance. In a real formulation, implement the needed phase/complex
structure internally and prove the identifications explicitly. A fixed
Clifford swap is not automatically the state-derived polar conjugation.
[RealTomitaCore](../lean/InfoGeometry/Canonical/RealTomitaCore.lean) currently
receives bounded logarithm/exponential data. Preserve the separate achievement
of [FiniteSeedRepresentedAnalyticKMS](../lean/InfoGeometry/Canonical/FiniteSeedRepresentedAnalyticKMS.lean),
which proves an analytic strip KMS result with its own stated boundary.
Takesaki and Haagerup provide the established modular and standard-form
frameworks [H12, H13].

### From an invariant readout to a continuous core

[YangMillsContinuum](../lean/InfoGeometry/Canonical/YangMillsContinuum.lean)
uses scalar modular data `Δ = r·id` and `H = -log(r)·id`; the corresponding
inner commutator is zero. Its named Type III interface does not impose a
von Neumann factor or a standard Type III criterion.
[TypeIIIContinuousCoreReal](../lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean)
explicitly does not construct a crossed product. Its
`RealContinuousCoreInterface` supplies a type, maps, an additive action, and
an invariant real-valued readout, without the algebra and weight properties
of a canonical continuous core.

For the usual dual-action sign convention, the canonical semifinite trace
satisfies `τ ∘ θ_s = exp(-s) τ`, rather than invariance [H14]. Reversing the
parameter convention reverses the exponent's sign, not the presence of scaling.
The existing
abstract invariant readout must therefore remain distinguished from that
trace. First construct actual represented operators `π(a)` and `λ(t)` and
prove crossed-product covariance. Then construct the operator algebra, dual
action, and correct positive extended-valued weight/trace with its scaling
law. Attach a Type III claim to an actual algebra and its type criterion.

### A true infinite-dimensional bounded phase

[RealSplitKreinBoundedTransform](../lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean)
has a general interface that selects a compact resolvent as phase and assumes
defect properties. Its actual `D(1+D²)^(-1/2)` construction is finite-dimensional.
The unbounded packet's pairing-based skew condition does not establish
equality with a domain-defined adjoint.
[CompactPhaseObstruction](../lean/InfoGeometry/KK/CompactPhaseObstruction.lean)
proves that compact `F` and compact `F² - id` force finite dimensionality.
Thus that compact choice cannot realize the intended infinite-dimensional
Fredholm phase.

Start with a densely defined real Hilbert-self-adjoint `D` and its actual
domain-sensitive adjoint theorem. Construct a bounded, noncompact phase
`F = D(1 + D²)^(-1/2)` on an infinite-dimensional real `ℓ²` model;
prove a norm bound, compactness of `id - F²` by finite-rank
approximation, and the required adjoint/domain equalities. Reuse the native
domains in [LinearDiracTransport](../lean/InfoGeometry/KK/LinearDiracTransport.lean)
and the concrete unbounded witness. A weighted off-diagonal number operator
is a proposed first model. For a Hilbert-skew-adjoint generator `K`, the
positive expression is instead `1 - K²`; a conversion must be proved before
reusing a self-adjoint formula. The Fredholm-module requirements are classical
[H15]; geometric index comparison remains a later theorem. This real Hilbert
milestone also does not construct a general Hilbert-module correspondence or
Kasparov product.

## Acceptance and recommended first tranche

Start independent implementation tasks for the support logarithm, the concrete
flow/generator theorem, and strictly positive finite Sinkhorn convergence.
The KKS radical quotient is a smaller algebraic task that can proceed in
parallel. Integrate the already pending Fock, uncertainty, Fisher, and ABS
work before adding dependent owners. The later analytic and topological tasks
should consume the resulting actual maps and domains.

Each implementation task should record its exact carrier, conventions,
reused declarations, additional hypotheses, smallest missing implication, and
excluded stronger claims. Acceptance requires native complete Lean proofs,
independent semantic review, the relevant locked build, and declaration-level
axiom review under the repository policy. A proof of a supplied hypothesis is
different from constructing its witness. Preserve noncommutative operator
content, real scalar conventions, and the distinct adjoint/support structures.

This publication changes documentation only. It records open work and observed
source scope; it does not close the proposed theorems, change dependencies or
gates, or certify whole-repository correctness. Publication validation and its
exact results belong in the accompanying pull request.

## Historical references

References are primary papers, author-hosted originals, or primary-author
expositions. Their role is to motivate exact theorem contracts, not to certify
that those theorems have already been formalized here.

- **[H1]** R. Sinkhorn and P. Knopp, *Concerning nonnegative matrices and doubly
  stochastic matrices* (1967), [original paper](https://msp.org/pjm/1967/21-2/pjm-v21-n2-p14-s.pdf).
  Support, scaling, uniqueness, and convergence in the stated square setting.
- **[H2]** I. Csiszár, *I-divergence geometry of probability distributions and
  minimization problems* (1975), [original paper](https://pages.stern.nyu.edu/~dbackus/BCZ/entropy/Csiszar_geometry_AP_75.pdf).
  Information projection and its Pythagorean geometry.
- **[H3]** M. Essid and M. Pavon, *Traversing the Schrödinger bridge strait:
  Robert Fortet's marvelous proof redux* (2018 preprint; 2019 publication),
  [author preprint](https://arxiv.org/abs/1805.02695).
  Reconstruction of Fortet's existence/convergence method and its historical reception.
- **[H4]** H. Araki, *Relative Entropy for States of von Neumann Algebras II*
  (1977), [publisher record](https://ems.press/journals/prims/articles/2844).
  Extension to nonfaithful states.
- **[H5]** M. H. Stone, *On one-parameter unitary groups in Hilbert space*
  (1932), [original-paper DOI](https://doi.org/10.2307/1968538).
  The operator/domain and continuity obligations of a generator theorem.
- **[H6]** S.-I. Amari, *Differential geometry of curved exponential families:
  curvatures and information loss* (1982),
  [author-hosted original](https://bsi-ni.brain.riken.jp/modules/xoonips/file/85/076.pdf).
  Fisher geometry and dual affine structures.
- **[H7]** H. Shima, *Homogeneous Hessian manifolds* (1980),
  [original paper](https://www.numdam.org/article/AIF_1980__30_3_91_0.pdf).
  Hessian structures and the induced tangent-bundle Kähler construction.
- **[H8]** H. Bursztyn and O. Radko, *Gauge equivalence of Dirac structures
  and symplectic groupoids* (2003),
  [original paper](https://www.numdam.org/item/10.5802/aif.1945.pdf), especially §2.4.
  Graph integrability and closed two-forms.
- **[H9]** Z.-J. Liu, A. Weinstein, and P. Xu, *Manin triples for Lie
  bialgebroids* (1997; 1995 preprint),
  [author preprint](https://arxiv.org/abs/dg-ga/9508013).
  Doubles and complementary integrable isotropic structures.
- **[H10]** M. Crainic and R. L. Fernandes, *Integrability of Lie brackets*
  (2003; 2001 preprint), [author preprint](https://arxiv.org/abs/math/0105033).
  Genuine obstructions to global Lie-algebroid integration.
- **[H11]** M. F. Atiyah, R. Bott, and A. Shapiro, *Clifford modules* (1964),
  [original paper](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/abs.pdf).
  Module restriction, relative symbol construction, and the comparison theorem.
- **[H12]** M. Takesaki, *Tomita's Theory of Modular Hilbert Algebras and its
  Applications* (1970),
  [publisher record](https://link.springer.com/book/10.1007/BFb0065832).
  Modular operators and modular automorphisms.
- **[H13]** U. Haagerup, *The standard form of von Neumann algebras* (1975),
  [journal record](https://journals.msp.org/mscand/article/view/2067).
  State-independent standard-form structure and its precise requirements.
- **[H14]** M. Takesaki, *Structure of von Neumann Algebras of Type III*,
  [lecture notes](https://www.imsc.res.in/~sunder/mtnotes.pdf).
  Continuous cores and crossed products. For the explicit negative-exponent
  dual-action trace convention, see also I. Goldbring and C. Houdayer,
  *Existentially closed W\*-probability spaces* (2022),
  [§2 of the primary paper](https://link.springer.com/article/10.1007/s00209-022-03038-z).
- **[H15]** A. Connes, *Noncommutative Geometry* (1994),
  [author-hosted book](https://alainconnes.org/wp-content/uploads/book94bigpdf.pdf).
  Unbounded cycles, compact resolvents, and bounded Fredholm modules.
