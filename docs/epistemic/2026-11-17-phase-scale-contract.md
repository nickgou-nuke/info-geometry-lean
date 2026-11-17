# Phase, scale, and finite-family operator uncertainty

## Provenance and acceptance boundary

The intake is preserved in [2026-11-17-phase-scale-intake.txt](2026-11-17-phase-scale-intake.txt).
Source review starts at upstream `08c34e03f610b452e03422037949196dc7d92d6d`.
The requested task is to connect the mathematical ideas to actual owners and
prepare an upstream PR. The earlier unfinished instrument/GNS work is a separate
task; its old temporary checkout and verification results are not reused here.

This contract is written before promotion of the new Lean owners. Acceptance
requires native compilation, recursive axiom inspection, and independent semantic
review. The intended results below are not marked kernel-verified until those
checks have actually completed. Final command results belong in the validation
section at the end of this document.

## Mathematical objects and distinctions

The common language is associative composition of operators, with products
retaining their order. The QGT construction uses a positive Hilbert inner product
and a normalized state. Acting on that state and projecting horizontally
produces the projective quantum geometric tensor; finite families produce a
positive Gram matrix. The internal-phase integral construction works on real
Banach spaces with bounded real-linear operators and explicit integrability.
A choice of circular algebraic basis supplies none of those analytic hypotheses
by itself.

The positive Hilbert pairing used for covariance is distinct from an indefinite
Minkowski or Krein pairing. Indexing a covariance matrix by `Fin 4` does not make
that matrix a spacetime metric or construct spacetime coordinate observables.

Fourier duality, convex Legendre duality, and the Penrose transform are different
constructions. Fourier resolves additive characters; Mellin uses multiplicative
scale and becomes Fourier after a logarithmic change of variables with the
correct weight. Convex Legendre-Fenchel duality is defined by a supremum;
Legendre-polynomial spectral transforms are a separate integral construction.
The Penrose owner uses cohomology, incidence, and contour integrals. No
equivalence between these different constructions is claimed.

## Owner inventory and claim ledger

The rows below report declaration-level source inspection at the baseline;
they are not a fresh compilation certificate for every listed historical file.
Paths are relative to `lean/InfoGeometry` unless prefixed by `src/`.

| Intake atom | Existing owner and precise result | Boundary |
| --- | --- | --- |
| Fourier, Laplace, Mellin | `Analysis/LaplaceFourierComparison`: `verticalLineTransform_eq_fourier`, `laplace_inverse_on_vertical_line`, `mellin_logPullback_eq_laplaceTransform`, `mellin_unique_on_positive_axis` | Actual native integrals and inversion under stated integrability/continuity hypotheses; the old introductory comment understates the implemented results. |
| Convex dual coordinates | `Convex/Legendre` | Fenchel-Young, supporting hyperplanes, gradient-image inverse coordinates under the stated boundedness and convexity assumptions; no Fourier integral identification. |
| Log partition and classical information | `Analytic/LogSumExp`: `logSumExp_deriv_eq_mean`, `logSumExp_secondDeriv_eq_variance`, `logSumExpWeight_deriv` | Actual one-parameter finite positive-weight exponential family; derivatives are proved. Strict convexity remains an argument to the Legendre adapter. This is not a general noncommutative Hessian/covariance theorem. |
| Finite log-Laplace and divergence | `Canonical/FiniteScalarLogLaplace`: `hasDerivAt_logPartition`, `hasDerivAt_deriv_logPartition`, `kl_eq_bregman_reverse` | Actual finite classical log-partition derivatives, centered variance, and KL/Bregman identity; no asymptotic Laplace principle is inferred. |
| Two-operator uncertainty | `QuantumGeometry/Projective/QGT`: `QGT_eq_inner_projOrth`, `QGT_cauchy_schwarz`, `robertson_schrodinger_qgt_bound`, `berryCurvature_skewAdjoint_commutator` | Arbitrary complete complex Hilbert carrier, bounded complex-linear operators, normalized state; the commutator readback explicitly assumes skew-adjointness. |
| Real internal phase | `Krein/DoubledSpace`: `complex_i`, `complex_i_sq`; `Canonical/OperatorialUncertainty`: `inner_sq_add_complex_i_inner_sq_le` | Actual doubled real Hilbert carrier and Bessel inequality. Channel formulas require phase linearity when moving the phase through a channel. |
| Cramer-Rao response | `Canonical/OperatorialCramerRao`: `one_le_comparisonStateGeneratorMetric_self_mul_self_of_unit_response`, `inv_comparisonStateGeneratorMetric_self_le_of_unit_response` | Constructed Cauchy-Schwarz consequence with unit response; the inverse bound also requires a nonzero reference channel. |
| Quantum statistical bound | `Quantum/QuantumCramerRaoBound` | Full finite real matrices, density factorization, symmetric observable/SLD, trace-zero derivative, supplied SLD equation and trace-pair symmetry; scalar, not general attainable multiparameter estimation. |
| Hodge-Dirac square | `Canonical/DiscreteDiracHodgeChiral`: `diracHodge_sq_eq_hodgeLaplacian` | Associative operator ring, `d²=δ²=0`, `D=d+δ`. `Topology/DiscreteHodgeDiracBridge` also owns the negative-Laplacian `d−δ` convention. |
| Concrete graph Dirac | `Streaming/BipartiteGraphDirac`: `graphDirac_sq`, `graphDirac_adjoint`, `graphDirac_krein_skew_adjoint` | Rectangular real incidence operator; square is `(BᵀB, BBᵀ)`. Hilbert and Krein adjoints have different signs. |
| Curvature remainder | `Superalgebra/KahlerDiracWeitzenbockSynthesis`: `diracOperator₂_sq_weitzenbock` | Retains the connection commutator under explicit mixed-commutation hypotheses; does not construct a manifold spin connection or derive scalar curvature. |
| Positive square root | `Canonical/DiracLaplacianSquareRootBridge`: `canonicalDirac_sq_eq_metricOp`, `canonicalDirac_sq_eq_laplacian` | Finite-dimensional positive operator square root; identifying the metric operator with a Laplacian is a supplied hypothesis. |
| Dirac dispersion | `Physics/FourVectorDiracReadout`: `diracSlash_sq`, `diracSlash_mass_factorization`, `dirac_equation_nonzero_spinor_implies_mass_shell`, `mass_shell_implies_nonzero_dirac_kernel` | Actual finite matrix slash operator and both directions of mass shell/nonzero kernel; no spacetime PDE or unbounded-domain theorem. |
| Spinor conjugation and ideals | `Physics/KreinDiracKasparovSpinorBilinear`; `CliffordWeyl/KreinIdealBilinears` | Adjoint reverses product order and exchanges left/right ideals under the stated metric/star hypotheses. |
| Spinor bilinears and covariance | `CliffordWeyl/SpinorBilinearSoldering`, `DiracMetricCovariance`, `DiracTraceCovariance`, `SplitSpinorFierz` | Actual rank-one soldering, trace/Fierz reconstruction, transported metric, and full matrix algebra equivalence. A conserved PDE current is not inferred from these algebraic identities. |
| Split-octonions to operators | `Lie/SplitOctonionCliffordAction`: `splitOctonionLeftCliffordRepresentation`, `imaginaryLeftMul_anticommutator` | Native Clifford algebra homomorphism into real endomorphisms, derived through alternativity; vector-map injectivity is not faithfulness of the whole Clifford representation. |
| Nonassociativity | `Lie/SplitOctonionNonmultiplicativity`; `OperatorAlgebra/SplitOctonionLeftMultiplicationBridge` | Explicit nonzero associator/left-multiplication defects. Products of regular operators cannot be replaced by regular multiplication by the product without a proof. |
| Fourth unit and circular basis | `Clifford/SplitOctonionQuaternionEllBridge` | `ell²=+1`, `jᵢ²=−1`, `ell*jᵢ=Jᵢ`; `(jᵢ±Jᵢ)/2` are null. This is a chosen hyperbolic direction, not a unique fourth imaginary unit. |
| Circular CAR and bivectors | `Canonical/SplitOctonionCARRightRegularBridge`, `SplitOctonionRightRegularBraid` | Actual three-mode regular-operator CAR, Majorana squares and anticommutation, bivector square `−1`, and operator conjugation. |
| Circular scaling obstruction | `Lie/SplitOctonionCircularZ3Grading`: `hyperbolicFlowZorn_not_mul_of_ne_zero`, `circularAxialGrading_not_derivation` | A nontrivial circular scaling is not a raw Zorn algebra automorphism; explicit nonzero Leibniz defect. |
| Phase and boost exponentials | `Physics/HestenesKreinOperatorCalculus`, `Clifford/Cl33BivectorLoxodromicBridge` | Actual complete normed-algebra exponential identities; commuting and anticommuting generators have different formulas. |
| Rapidity and logit | `Canonical/AmariBinarySimplexBridge`: `logistic_eq_half_add_tanh_half`, `logit_logistic`; `Physics/AitchisonJaynesRapidityBridge`: `BinaryProbability.logit_eq_two_mul_rapidity` | Setting the logistic parameter to `2χ` gives `p=(1+tanh χ)/2` and `logit p=2χ`; inverse probability formulas require `0<p<1`. |
| Reciprocal null scaling | `Nuclear/FocalRapidity`: `rapidity_boost`, `boost_preserves_product`, `scale_sq` | Positive pair `u,v`, `χ=(log(v/u))/2`, `s²=uv`, and `(u,v) -> (u exp(-a),v exp(a))`; an auxiliary two-dimensional Lorentz plane, not a constructed four-dimensional spacetime. |
| Transform kernels | `Clifford/SplitCliffordTransformKernel` | Algebraic kernels and group laws; explicitly no analytic Fourier/Mellin integral transform. |
| Penrose | `Twistor/HomogeneousTwistorCech`, `Twistor/PenroseContourTransform` | Laurent Cech quotient, coefficient contour readback, and an explicit nonconstant Maxwell zero-rest-mass field. Not a general analytic Penrose isomorphism. |
| Poincare and SUSY | `Parafermion/TetractysPoincareSupersymmetryTwistorPoset`, `Physics/CuntzDeformedSuperPoincare` | Explicit Peirce/Lorentz/odd-bracket algebra under stated relations. Some closure equations are presentation fields; an independent translation module, physical supersymmetry theory, or emergent spacetime is not thereby constructed. |

Related but different matrix owners were inspected:
`src/InfoGeometry/OperatorAlgebra/FiniteOperatorCovariance.lean` uses finite
weighted samples in a star algebra; `src/.../CovarianceTransport.lean` proves
matrix transport with added covariance; `Canonical/StableVacuum` uses a real
tangent Gram matrix. These do not supply the proposed centered one-state
finite-family QGT matrix and its complex family-change theorem.

Misleading-name boundaries: `Canonical/CramerRaoUncertainty` assumes
`VarX * I_F ≥ 1` and `VarP = I_F / 4`, then derives `VarX * VarP ≥ 1/4`;
it does not construct the statistical or wavefunction premises.
`Canonical/PontryaginDualFourierInversionBridge` does not construct Pontryagin
duality or Fourier inversion. Their names are not used as evidence of the
stronger requested mathematics.

## New owner A: finite-family QGT matrix

Target: `QuantumGeometry/Projective/QGTMatrix.lean`.

Carrier: arbitrary complete complex Hilbert space `H`. The observation index
is finite where sums or matrix positivity require it. The Hilbert space is not
assumed finite-dimensional. Each `X i` is an arbitrary bounded complex-linear
endomorphism. No pairwise commutativity or diagonalization is imposed.

Reuse `NormalizedState`, `projOrth`, `QGT`, `fubiniStudyMetric`, and
`berryCurvature` from the existing projective owner. Define

\[
v_i=P_{\psi^\perp}(X_i\psi),\qquad Q_{ij}=\langle v_i,v_j\rangle.
\]

Required constructive conclusions:

1. `qgtMatrix` equals native `Matrix.gram`; it is Hermitian and positive
   semidefinite.
2. For every complex coefficient family, `c* Q c` equals the squared norm of
   `sum_i c_i v_i`. This keeps all cross terms.
3. The whole matrix is invariant under multiplication of the normalized state
   by a unit complex phase.
4. For `C : Matrix ι κ ℂ`, define actual mixed operators
   `Y j = sum_i C i j • X i`. Prove `Q(Y)=Cᴴ Q(X) C`, with no invertibility
   requirement on `C` and no dimension restriction on `κ` beyond each theorem's
   explicit assumptions.
5. Set `g=Re Q`, `Ω=−2 Im Q` using the repository convention. Prove symmetry of
   `g`, antisymmetry of `Ω`, `Q=g−(i/2)Ω`, and real congruence of both under real
   family mixing.
6. For skew-adjoint generators, reuse the owner's commutator theorem to prove
   `Q−Qᵀ=−<ψ,[X_i,X_j]ψ>`. Do not silently switch to self-adjoint observable
   conventions.

The existing `fisherMetric` is normalized as the Fubini-Study metric. The common
pure-state quantum Fisher convention is four times that metric. No theorem in
this change identifies those differently normalized quantities.

The matrix result specializes to four observation channels but is not a
Lorentz-covariant spacetime Cramer-Rao theorem. Such a theorem also needs actual
generators, state transformation, statistical scores/SLDs, unbiased response,
and appropriate operator domains.

## New owner B: real internal-phase Fourier integral

Targets: `Analysis/InternalPhaseFourier.lean` and the focused native adapter
`Analysis/DoubledInternalPhaseFourier.lean`.

Carrier: a complete real normed vector space `H`, a bounded real-linear phase
operator `K`, and real Lebesgue measure. Define an actual Bochner integral

\[
\mathcal F_K f(\xi)=\int_{\mathbb R}
 \bigl(\cos(2\pi\xi x)f(x)-\sin(2\pi\xi x)K(f(x))\bigr)\,dx.
\]

Required constructive conclusions allow two complete real normed spaces, phase
operators `K` and `L`, and a bounded real-linear map `T : H -> G`:

- If `TK=LT`, then `T(F_K f(ξ))=F_L(T∘f)(ξ)`.
- If `TK=−LT`, then `T(F_K f(ξ))=F_L(T∘f)(−ξ)`.

Integrability is explicit. A proof that an integrable `f` has integrable kernel
is preferred, using bounded trigonometric coefficients and continuity of `K`.
The intertwining itself does not need `K²=−1`; that additional identity is what
makes this kernel an internal complex phase. The existing doubled `complex_i`
supplies that identity for its concrete carrier. The native adapter specializes
to `complex_i` and derives preservation under that phase axis and reversal
under `modular_j` and `spectral_epsilon`, using their existing product laws.

A logarithmic pullback can express a scale transform, but a transform over
`du` in log coordinates must be labeled that way. A theorem over `dx/x` requires
the actual measure change. Inversion, Plancherel/unitarity, and wave-packet
position/momentum domain estimates are not supplied by the intertwining laws.

## Independent semantic review

Separate authoring and read-only review covered the three proposed owners and
their pinned Mathlib APIs. The reviewer confirmed coefficient orientation,
Gram positivity, the skew-adjoint commutator sign, Bochner integrability, and
both canonical involution signs. The reviewer identified a required local
`ComplexOrder` scope for the complex PSD instance; it was added before native
validation. Source review and kernel validation remain separate results.

Complex family mixing need not preserve skew-adjointness. The congruence theorem
is valid for arbitrary bounded complex-linear operators; the commutator theorem
has its own skew-adjoint hypothesis. The Gram matrix can be singular, so neither
an inverse-Fisher bound nor identifiability follows from positivity alone.

For state derivatives generated by observables through
`exp(-i theta G / hbar)`, the derivative generator is `X=-iG/hbar`. Thus the
conventional quantum Fisher normalization also includes `hbar^(-2)` when
expressed as an observable covariance. This physical identification is not a
new theorem in these owners.

## Dependency order and open work

The source-level dependency order for owner A is:
normalized state and horizontal projection -> native Gram identification ->
positivity and coefficient norm -> complex operator-family congruence ->
real metric/Berry congruence and existing skew-adjoint commutator readback.

For owner B it is:
bounded real-linear operators and explicit integrability -> actual Bochner
integral -> continuous-linear-map/integral commutation -> same-frequency or
reversed-frequency intertwining according to the operator commutation sign.

These are two related operator constructions. No unproved map between the real
carrier and the complex projective carrier is inserted into this dependency
order. The existing split-octonion representation can supply operators only
after its topology, boundedness, inner product, and phase compatibility are
specified. The existing scalar Mellin/Fourier theorem is analytic reuse, not
an assertion that every noncommutative representation decomposes into scalar
characters.

Remaining open targets include full internal-phase Fourier inversion, the
multiplicative Haar-measure adapter, unbounded relativistic generators on a
common core, state/estimator-based multiparameter Cramer-Rao and attainability,
stationary-phase and Laplace-principle connections to convex conjugacy,
geometric spin-connection/Lichnerowicz data, and any proposed emergence or
classification theorem. Boost-induced reciprocal null-coordinate scaling does
not by itself establish isotropic Weyl gauge symmetry or set a physical unit
of length.

The related `ChiralGrandCanonicalLoxodromicRotor` uses full complex `4 x 4`
Dirac matrices. Its reciprocal projector weights are exact, but its operator
parameter is not automatically physical vector rapidity: spinor and induced
conjugation actions may differ by a factor of two. The separate `Cl(3,3)`
bivector owner has a real `8 x 8` matrix representation. These carriers are
not silently identified.

## Search and validation scope

Source searches covered active `lean/InfoGeometry`, `src/InfoGeometry`, and
`proofs` for QGT/Gram/positivity/congruence owners, with import and consumer
inspection. Internal-phase transform searches covered Fourier/Mellin kernels,
integral intertwining, real phase reversal, and nearest Hestenes/rotor owners.
No existing owner for the two selected new implications was located within
those bounds. This is a bounded absence finding, not a claim that all 17,000+
Lean files were individually read.

Additional nearby-owner review checked `ConstructiveTrigonometricFourierBridge`
(three scalar trigonometric interval integrals), `ConstructiveMellinL2IntegralBridge`
(four scalar monomial integral/energy identities), and
`ComplexifiedCartanMellinKernel` (scalar complex damping/phase factorization).
None defines the generic real internal-phase integral or its intertwining laws.
Reusing complex Fourier inversion in that lane would first require a
norm-compatible complex scalar action identifying multiplication by `i` with
the internal phase operator.

A bounded additional search for stationary-phase, Varadhan, Gartner-Ellis,
and Laplace-principle declarations found finite log-Laplace calculus but no
derived asymptotic bridge in the closest inspected owners.
`Canonical/PrimeLeeYangLargeDeviation.PrimeChainLargeDeviationWitness` supplies
both the Legendre rate-function identification and the large-deviation
principle as fields. `lean/Omega/POM/FiberIndexLdpThermo.lean`'s
`gartner_ellis_wrapper` extracts a supplied affine-support predicate; it does
not establish the analytic Gartner-Ellis theorem. Defining a convex conjugate
does not establish a probability asymptotic. These are source-scope findings,
not a denial of the mathematical stationary-phase or Laplace-principle bridges.

The optional DAG-status command failed in this checkout because
`dag-toolchain.json` is absent. No live graph, current AST index, or external
memory completeness is claimed. The root Lake route uses `lean/`, while
`src/` is a distinct source lane. Existing source is the search authority.

Validation status at contract creation: pending. The exact pinned environment
is Lean `v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No pins or dependency source files
are to be changed. All Lean/Lake work uses the shared build lock.

### Recorded validation and CI scope

The independent source review, staged proof gate, and selected semantic-content
gate passed. The semantic gate read all three selected owners with complete
selected coverage and reported zero findings. A lexical scan found no proof
placeholders, custom axioms, unsafe declarations, or `native_decide` in the new
owners. These are not substitutes for kernel verification.

Native compilation of the exact ten-module source closure has reached all ten
modules, but the selected run failed in the QGT congruence proof as recorded
below. Recursive axiom inspection has not yet run. A successful fresh native
check is required. The maintained checker is unchanged. The focused
[`phase-scale-qgt.yml`](../../.github/workflows/phase-scale-qgt.yml) workflow
uses the same checker on a GitHub runner, reads the exact dependency pins,
requires zero warnings in the new owners, runs the selected semantic gate,
and preserves the native evidence. It does not certify the root Lake build.

The root path-package preflight found missing `HomotopyHypothesis` and `Atlas`
configurations with untracked dependency paths, plus an uninitialized `GIFT`
gitlink. Earlier queued local sessions ended without reports. A fresh selected
native check was queued on 17 November; no successful root build result exists.

The first focused [run 44054152325](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44054152325)
for head `441f95c93cce4734788738715662eda503244b3d` failed before native work.
`actions/checkout` fetched the merge commit successfully, then failed while
removing authentication because its recursive submodule traversal encountered
`external_refs/auto-ontology` without a `.gitmodules` URL. Lean compilation,
axiom inspection, and semantic checks were all skipped. No evidence artifact
was produced by that run.

The focused workflow now fetches the public source without credentials and
checks that `HEAD` equals the requested `github.sha`. This preserves the
pull-request merge-commit scope and avoids recursive submodule traversal.
The separate pinned Mathlib checkout and all mathematical acceptance checks
are unchanged. A subsequent successful native run is still required.

The replacement [run 44088120137](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44088120137)
for head `ef993816e550ec6c440fa0a818066a178a2c2704` successfully fetched the exact
source, installed the pinned compiler, and obtained the native import cache.
`InternalPhaseFourier` and `DoubledInternalPhaseFourier` compiled; the former
had four unused-section-variable warnings and the latter had zero warnings.
`QGTMatrix` failed in `qgtMatrix_mixOperatorFamily`: the inner-product expansion
put the two finite sums in the opposite order to the matrix product. Its
pointwise goal was therefore false before reindexing. It also emitted six
unused-assumption/tactic warnings. The recursive declaration audit and selected
zero-warning/semantic steps were skipped; the run retained its evidence artifact.

The source repair explicitly swaps the two left-hand finite sums with
`conv_lhs => rw [Finset.sum_comm]` before termwise scalar normalization. It
preserves the ordered operators, inner-product arguments, and `Cᴴ Q C`
statement. Declaration-local `omit` commands remove only the reported unused
completeness assumptions; unused decomposition simp arguments and an unreachable
`ring` are removed. No linter or acceptance check is disabled. Independent
source review agrees with this reindexing; native acceptance of the repair
remains a separate pending check.

Initial published head `00fcd6afbabdfe747a96df7dbd2b9b6d0ae4d587` has the
following observed CI failures. The relevant failing scripts/configuration
files are unchanged from the baseline. No separate baseline CI rerun is claimed.

| Workflow | Observed failure and scope |
| --- | --- |
| [Sorry Gate](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44048388469) | Repository inventory reports 878 forensic/fixture findings in 91 files, zero package findings; the new owners are not listed. |
| [Lean style lint](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44048389861) | Existing `lean/docs` and `lean/Docs` case collision; the style linter is not reached. |
| [Closure Debt + Superorganism Smoke](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44048388616/job/133919693690) | `python3 -m pytest` fails with `No module named pytest`; tests and subsequent Lean checks do not run. |
| [Reviewed PR Integration](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44048388299/job/133919692321) | Recursive checkout fails because `external_refs/auto-ontology` has no URL in `.gitmodules`; compilation and axiom inspection are skipped. |
| [CI](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44048388332/job/133925631034) | Path-package preflight reports the same Homotopy/Atlas/GIFT blockers. Its green smoke-summary step catches and records a failed `compilerBridgeServer` build; it is not a successful smoke test. |
| [Idempotent chart calculus](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44048388494/job/133919692968) | Existing `check_operator_geometry.py` has an unclosed parenthesis at line 168; its build and negative certificate check do not run. |
| [Ordered homotopes and twistor invariants](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44048388337/job/133919693030) | Existing pre-push hook differs from that lane's reviewed reference; its control guard stops before project compilation. |

The draft remains unverified by the Lean kernel until the selected native
compilation and complete declaration axiom audit return successful results.
