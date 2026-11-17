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

The common construction is a representation by operators on a space with a
positive inner product, together with a chosen state. Operator products retain
their order. Their action on the state produces vectors; horizontal projection
produces the projective quantum geometric tensor (QGT); finite families produce
a positive Gram matrix. Integral transforms require additional measure and
integrability structure. A choice of circular algebraic basis supplies none of
those analytic hypotheses by itself.

The positive Hilbert pairing used for covariance is distinct from an indefinite
Minkowski or Krein pairing. Indexing a covariance matrix by `Fin 4` does not make
that matrix a spacetime metric or construct spacetime coordinate observables.

Fourier duality, convex Legendre duality, and the Penrose transform are different
constructions. Fourier resolves additive characters; Mellin uses multiplicative
scale and becomes Fourier after a logarithmic change of variables with the
correct weight. A Legendre transform is a convex supremum, not an integral
transform. The Penrose owner uses cohomology, incidence, and contour integrals.
No equivalence between these three kinds of duality is claimed.

## Owner inventory and claim ledger

The rows below report declaration-level source inspection at the baseline;
they are not a fresh compilation certificate for every listed historical file.
Paths are relative to `lean/InfoGeometry` unless prefixed by `src/`.

| Intake atom | Existing owner and precise result | Boundary |
| --- | --- | --- |
| Fourier, Laplace, Mellin | `Analysis/LaplaceFourierComparison`: `verticalLineTransform_eq_fourier`, `laplace_inverse_on_vertical_line`, `mellin_logPullback_eq_laplaceTransform`, `mellin_unique_on_positive_axis` | Actual native integrals and inversion under stated integrability/continuity hypotheses; the old introductory comment understates the implemented results. |
| Convex dual coordinates | `Convex/Legendre` | Fenchel-Young, supporting hyperplanes, gradient-image inverse coordinates under the stated boundedness and convexity assumptions; no Fourier integral identification. |
| Log partition and classical information | `Analytic/LogSumExp`: `logSumExp_deriv_eq_mean`, `logSumExp_secondDeriv_eq_variance`, `logSumExpWeight_deriv` | Actual one-parameter finite positive-weight exponential family; derivatives are proved. Strict convexity remains an argument to the Legendre adapter. This is not a general noncommutative Hessian/covariance theorem. |
| Two-operator uncertainty | `QuantumGeometry/Projective/QGT`: `QGT_eq_inner_projOrth`, `QGT_cauchy_schwarz`, `robertson_schrodinger_qgt_bound`, `berryCurvature_skewAdjoint_commutator` | Arbitrary complete complex Hilbert carrier, bounded complex-linear operators, normalized state; the commutator readback explicitly assumes skew-adjointness. |
| Real internal phase | `Krein/DoubledSpace`: `complex_i`, `complex_i_sq`; `Canonical/OperatorialUncertainty`: `inner_sq_add_complex_i_inner_sq_le` | Actual doubled real Hilbert carrier and Bessel inequality. Channel formulas require phase linearity when moving the phase through a channel. |
| Cramer-Rao response | `Canonical/OperatorialCramerRao`: `one_le_self_mul_self_of_unit_response`, `inv_self_le_of_unit_response` | Constructed Cauchy-Schwarz consequence with unit response and nonzero reference channel. |
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

Misleading-name boundaries: `Canonical/CramerRaoUncertainty` assumes its main
scalar product bound; `Canonical/PontryaginDualFourierInversionBridge` does not
construct Pontryagin duality or Fourier inversion. Their names are not used as
evidence of the stronger requested mathematics.

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

The proved dependency order for owner A is:
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

The optional DAG-status command failed in this checkout because
`dag-toolchain.json` is absent. No live graph, current AST index, or external
memory completeness is claimed. The root Lake route uses `lean/`, while
`src/` is a distinct source lane. Existing source is the search authority.

Validation status at contract creation: pending. The exact pinned environment
is Lean `v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No pins or dependency source files
are to be changed. All Lean/Lake work uses the shared build lock.
