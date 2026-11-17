# Split-octonion attachment: corrected mathematical contract

This review covers the complete attachment `Pasted text(20261117-091117).txt`. The attachment supplies proposed mathematics. Its terminology and proposed dependency order do not establish its claims. The useful addition is a projected Gram operator on a specified positive real Hilbert space. The existing PR's operator, uncertainty, and wave-packet contracts remain separate.

## 1. Concrete new construction

The isolated candidate `ProjectedGramDissipation.lean` uses namespace `InfoGeometry.Analysis.ProjectedGramDissipation`. Let `H` and `F` be complete real inner-product spaces, let `ι` be a finite index type, and let `R i : H →L[ℝ] F` be actual bounded linear maps. Define

\[
P_h=\operatorname{proj}_{(\mathbb Rh)^\perp},\qquad
M_{\gamma,h,R}=\gamma\sum_i(R_iP_h)^*(R_iP_h).
\]

The projection is Mathlib's `Submodule.starProjection`, and the adjoint is Mathlib's continuous-linear-map adjoint. The construction does not store positivity, symmetry, or the energy-kernel conclusion as structure fields. It applies in finite-dimensional Euclidean spaces and also on arbitrary complete real inner-product spaces with a finite family of bounded maps.

| Declaration | Exact contract |
| --- | --- |
| `energyProjection_apply` | `P_h x = x - (⟪h,x⟫ / ‖h‖²) • h`, including the totalized zero case. |
| `energyProjection_self`, `energyProjection_zero` | `P_h h = 0`; `P_0 = id`. No nonzero-energy assumption is needed. |
| `dissipator_eq_sandwich` | `M = γ • (P_h† ∘ (∑ i, R_i† ∘ R_i) ∘ P_h)`, with operator order preserved. |
| `dissipator_isPositive` | `0 ≤ γ` implies native `ContinuousLinearMap.IsPositive M`. |
| `inner_dissipator`, `inner_dissipator_swap` | The bilinear pairing is `γ ∑ i, ⟪R_i(P_h x), R_i(P_h y)⟫` and is symmetric, for every real `γ`. |
| `dissipator_energy` | `M h = 0`, for every real `γ`. |
| `inner_dissipator_self` | `⟪x,M x⟫ = γ ∑ i, ‖R_i(P_h x)‖²`. |
| `inner_dissipator_self_nonneg` | The quadratic form is nonnegative when `0 ≤ γ`. |
| `inner_dissipator_self_eq_zero_iff` | When `γ ≠ 0`, zero quadratic value is equivalent to every `R_i(P_h x)` being zero. |
| `dissipator_apply_eq_zero_iff` | When `γ ≠ 0`, `M x = 0` has the same joint-kernel characterization. |

A nonzero-rate hypothesis is necessary for these equivalences to hold uniformly over the maps: at `γ = 0`, the operator is zero regardless of the maps. Nonnegativity of the operator additionally requires `γ ≥ 0`; the kernel equivalences also hold at negative rates. The finite index type may be empty, in which case the equivalences correctly reduce to a zero operator and a vacuous universal condition. No claim of strict production is made without a nonzero projected generator.

The candidate imports only `Mathlib.Analysis.InnerProductSpace.Positive` and `Mathlib.Analysis.InnerProductSpace.Projection.Basic`. It reuses native positive Gram operators, positive finite sums, adjoints, and orthogonal projections. It does not add an associative multiplication to the split octonions or use the indefinite composition norm as a positivity witness.

**Validation boundary:** the candidate has been source-reviewed against Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. This document does not certify successful elaboration, kernel checking, an axiom audit, or CI. Those results must be bound to the actual integrated source revision.

## 2. How existing owners fit

The following are actual source declarations, not conclusions inferred from filenames. Links are pinned to the reviewed repository revision `20a3bfeaa0ddb6e3f00b31dff874eddeec72827c`.

| Existing owner and declarations | What can be reused, and its boundary |
| --- | --- |
| [Canonical/ParaComplexNeutralForm.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/20a3bfeaa0ddb6e3f00b31dff874eddeec72827c/lean/InfoGeometry/Canonical/ParaComplexNeutralForm.lean), `form_self_eq_two_mul_cross_pairing`, `plus_isotropic`, `minus_isotropic` | Given the stated involution and bilinear-form compatibility, derive isotropic sheets and the quadratic cross-pairing identity. `NondegenerateDatum` separately supplies nondegeneracy and cross-nondegeneracy fields; its existence is not established by the identity. |
| [Canonical/SplitOctonionRegularOperators.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/20a3bfeaa0ddb6e3f00b31dff874eddeec72827c/lean/InfoGeometry/Canonical/SplitOctonionRegularOperators.lean), `SplitOctonion.rightRegular`, `rightRegular_comp_defect_apply` | The real-linear map `rightRegular b ∘ rightRegular a - rightRegular (a*b)` acts on `v` as `(v*a)*b - v*(a*b)`. The separate `SplitOctonionProjectedGram.lean` candidate transports this actual map along an explicit linear coordinate equivalence to a finite-dimensional positive real Hilbert space and obtains continuity natively. |
| [Lie/SplitOctonionNonmultiplicativity.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/20a3bfeaa0ddb6e3f00b31dff874eddeec72827c/lean/InfoGeometry/Lie/SplitOctonionNonmultiplicativity.lean), `nonmultiplicativity_obstruction`, `imaginaryLeftMul_product_defect` | Supplies genuine failures of multiplication preservation and the operator-product defect. It does not prove that every representation on the underlying eight-dimensional vector space is impossible. |
| [Analysis/HilbertGramDuality.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/20a3bfeaa0ddb6e3f00b31dff874eddeec72827c/lean/InfoGeometry/Analysis/HilbertGramDuality.lean), `gramEigenspaceEquiv`, `inner_map_map_of_mem_eigenspace`, `gram_operator_norm_eq` | Already handles actual Hilbert Gram operators `A†A` and `AA†`, with nonzero-eigenspace transport and norm laws. The new candidate adds the energy projection, finite generator sum, and exact joint kernel rather than duplicating these spectral results. |
| [Thermo/GenericMetriplecticFlow.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/20a3bfeaa0ddb6e3f00b31dff874eddeec72827c/lean/InfoGeometry/Thermo/GenericMetriplecticFlow.lean), `System.energy_rate`, `entropy_rate_nonneg`, `entropy_covector_eq_zero_of_injective`, `entropy_rate_zero_of_injective` | Derives rates from explicit skewness, symmetry, positivity, and Casimir laws. The new construction proves the dissipative operator laws on the positive Hilbert carrier. A connection to this covector formulation additionally needs the actual gradient/covector identification. The injective-Poisson obstruction is already proved here. |
| [Canonical/LandauerDissipationNativeBridge.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/20a3bfeaa0ddb6e3f00b31dff874eddeec72827c/lean/InfoGeometry/Canonical/LandauerDissipationNativeBridge.lean), `landauerHeat`, `landauer_heat_positivity` | Defines heat to be a prescribed positive bit-count difference times `log 2 / beta`, then proves positivity. This is not a derivation of a thermodynamic heat bound from a metriplectic entropy-production theorem. |

The bounded reuse search found no existing owner proving this complete projected finite-family Gram contract. The separate `SplitOctonionProjectedGram.lean` candidate uses namespace `InfoGeometry.Analysis.SplitOctonionProjectedGram`. It takes a coordinate equivalence `e : SplitOctonion ≃ₗ[ℝ] H`, constructs the transported bounded associator map, and proves its action as `e ([e⁻¹x,a,b])`. The equivalence is coordinate input data; the associator action and operator conclusions are proved, not supplied as fields.

| Adapter declaration | Exact construction or conclusion |
| --- | --- |
| `associatorMap`, `associatorMap_apply` | Constructs `e ∘ (rightRegular b ∘ rightRegular a - rightRegular (a*b)) ∘ e⁻¹` and proves its value is the transported associator. Finite dimensionality of the positive target supplies continuity. |
| `associatorDissipator` | Instantiates the projected Gram construction with the actual associator maps for all ordered pairs of a finite supplied generator family. |
| `associatorDissipator_isPositive`, `associatorDissipator_energy` | Derives positivity for `γ ≥ 0` and annihilation of the energy direction. |
| `inner_associatorDissipator_self` | Gives the sum of squared positive coordinate norms of the actual projected associators. |
| `inner_associatorDissipator_self_eq_zero_iff`, `associatorDissipator_apply_eq_zero_iff` | For `γ ≠ 0`, zero quadratic value or zero operator action is equivalent to every projected associator vanishing. |

A concrete existing coordinate choice is `InfoGeometry.Canonical.splitOctonionDoubledQuaternionEquiv` in [SplitOctonionBogoliubovCarrierBridge.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/20a3bfeaa0ddb6e3f00b31dff874eddeec72827c/lean/InfoGeometry/Canonical/SplitOctonionBogoliubovCarrierBridge.lean). It maps the root split-octonion type to the positive L² product of two four-dimensional Euclidean spaces, and its owner supplies finite dimensionality. The ordinary product `E4 × E4` in that file is an intermediate coordinate space; the positive Hilbert carrier is `WithLp 2 (E4 × E4)`. The minimal adapter does not import the full carrier-bridge owner. This keeps the coordinate choice explicit without duplicating its construction or identifying the positive norm with the split composition form.

## 3. Algebraic corrections

### The scalar sandwich and cross pairing

With standard split-octonion conjugation, pure imaginary `ℓ`, and the indicated parentheses,

\[
\operatorname{Sc}((\psi\ell)\bar\psi)=0.
\]

Conjugation is an anti-involution, and alternativity justifies the required rebracketing because `bar ψ` is in the real span of `1` and `ψ`. An arbitrary Clifford reversion must not silently be substituted for this conjugation. Likewise, the difference of the two cross terms of a symmetric polar form is zero.

For complementary isotropic sheets and a symmetric form, the valid identity is

\[
B(x,x)=2B(x_+,x_-).
\]

Ambient nondegeneracy and the complementary decomposition are additional data needed to infer a nondegenerate cross pairing. The cross potential is not nonzero at every state: it vanishes on each individual null sheet. A zero identity may be mathematically useful; nonvacuity is not a requirement that every function take nonzero values everywhere.

### An associative representation does not force a 64-dimensional state

Octonion multiplication cannot simply replace the associative multiplication in an even Clifford algebra. Nevertheless, an eight-dimensional real linear equivalence can transport an existing group representation to the underlying eight-dimensional octonion vector space. The endomorphism algebra is associative independently of the octonion product. Its dimension is 64; that does not change its state space into a 64-dimensional space.

A tensor product of two eight-dimensional carriers is an available 64-dimensional construction when independent factor actions are desired. Nonassociativity alone establishes neither its necessity nor its uniqueness. A nonassociative multiplication witness also need not consist of elements of the particular spin group under discussion.

### An associative subalgebra does not kill all ambient associators

For the repository's split Cayley–Dickson convention

\[
(a,b)(c,d)=(ac+\bar d b,\; da+b\bar c),
\]

take `j = (j,0)`, `ℓ = (0,1)`, and `iℓ = (0,i)`. Then

\[
(j\ell)(i\ell)=-k,\qquad j(\ell(i\ell))=k,
\qquad [j,\ell,i\ell]=-2k\ne0.
\]

The vector `j` lies in the quaternion subalgebra. Thus allowing the generator indices to range over all seven ambient imaginary directions does not give zero associator Gram dissipation on that subalgebra. A sufficient corrected condition is that the projected direction and both generator arguments belong to the same associative subalgebra. The exact general condition is the joint-kernel statement in the candidate.

## 4. Dynamics and statistical obligations

The expression `γ ∑ ‖R_i P_h ∇S‖²` is nonnegative when `γ ≥ 0`. It may be zero at nonassociative states. Strict positivity requires at least one nonzero projected generator. Establishing this expression as the derivative of entropy along a curve additionally requires differentiable functions, their actual gradients, the vector-field equation, and the chain rule. It does not supply existence, uniqueness, global continuation, convergence, or a stationary Gibbs state.

There is a sharper incompatibility in the attachment's proposed combination. A full symplectic inverse is injective. If the entropy is also a full Poisson Casimir, then

\[
L\,dS=0\ \Longrightarrow\ dS=0,
\]

so entropy production vanishes. The existing `GenericMetriplecticFlow` owner proves precisely this obstruction. A nontrivial GENERIC construction needs a degenerate Poisson operator, or a different and explicitly weaker condition such as `{S,H}=0` for the selected Hamiltonian. These are distinct contracts.

The proposed universal compact Gibbs cone is false without a specified state space, moment map, measure, and integrability hypotheses. For example, the zero coadjoint orbit with unit point measure has partition function 1 for every Lie-algebra parameter, including noncompact directions. Finite-state Gibbs sums likewise converge for every finite real parameter. Compact-type Lie algebra membership alone does not prove integrability on a noncompact phase space. In the normal-convergence formulation, the admissible parameter domain is open and convex when nonempty, and can be empty; it is not universally contained in a fixed proper compact subalgebra. See [Marle, Definition 3.1.2 and Proposition 3.1.3](https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf).

Nonnegative entropy production alone also does not define reservoir heat, bath temperature, or erasure of one bit. A Landauer inequality requires a thermodynamic model. For example, [Reeb and Wolf, Theorem 3](https://arxiv.org/pdf/1306.4352) assumes an initially uncorrelated system and thermal reservoir followed by a joint unitary, and relates reservoir heat to the system entropy decrease plus correlation and relative-entropy terms. The Gram identity does not establish those assumptions or identify its quadratic production with heat.

## 5. Mixed Hessians, Ricci signs, and Legendre duality

Let `C = Ψ_xy` be a smooth invertible mixed Hessian. The actual neutral metric with matrix `[[0,C],[Cᵀ,0]]` has signature `(n,n)`, and the associated mixed two-form is closed by equality of mixed partial derivatives. The symmetric tensors `dx_i ⊙ dx_j` are not zero: their coefficients in this particular metric vanish. A convention for the normalization of `⊙` is required.

With the curvature convention `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z` and `Ric(X,Y) = tr(Z ↦ R(Z,X)Y)`, the mixed Ricci component has sign

\[
\operatorname{Ric}_{i\bar j}=-\partial_{x_i}\partial_{y_j}\log|\det C|.
\]

Changing curvature or Ricci-form conventions can change the displayed sign. A convention-free positive-sign assertion is not justified; compare the explicit mixed-Hessian formula in [Bor, Makhmali, and Nurowski](https://link.springer.com/article/10.1007/s10711-021-00665-4). Also `det g = (-1)^n (det C)^2`, so replacing `log|det C|` by `log|det g|` introduces a factor of two.

Writing `σ = log|det C|` defines a scalar. It does not solve a prescribed determinant equation. Adding `φ(x)+χ(y)` leaves `C` unchanged, but alters the pure `x` Hessian; the mixed neutral geometry therefore does not determine Legendre invertibility.

Strict twice-differentiable convexity alone is insufficient for an invertible Hessian: `x ↦ x⁴` is a counterexample at zero. The local inverse-Hessian identity needs an invertible Hessian and the differentiability assumptions for the inverse gradient map. A global Legendre diffeomorphism needs additional domain and growth hypotheses. Statistical Cramér–Rao conclusions additionally require a statistical model, score/expectation identities, and estimator assumptions; they do not follow from naming a Hessian “Fisher.”

## 6. CAR relations and the proposed dependency graph

The relation `ab+ba=1` implies that the ideal generated by `a,b` is the whole unital ring. It does not imply that the ring is simple. Complementary idempotents `ab,ba` require further hypotheses, such as `a²=b²=0`. Their isotropy requires a specified compatible bilinear form.

The attachment's final table has 15 vertices and 28 edges. Direct reachability checking finds no transitive redundant edge; `K_TT` and `Pi_ST` are incomparable in that table. Thus the suspected antichain defect is absent from this particular final graph. Its displayed ranks strictly increase along every edge, but three covers jump by two ranks, and maximal chains have lengths 5 and 6. It is therefore not a graded poset with the asserted rank function. A finite graph having a designated common upper vertex also does not prove a unique mathematical or physical synthesis.

## 7. Minimal integration scope

The minimal proof scope consists of the generic projected Gram owner and the small split-octonion adapter, subject to compilation and axiom review. Reuse the existing cross-pairing, regular associator-map, Hilbert Gram, and GENERIC rate owners. The adapter constructs the operator transport after an explicit positive coordinate choice. It does not select a canonical physical observer, nor establish differential flow, a statistical model, geometric curvature, Gibbs integrability/convergence, or a reservoir model. These remain explicit obligations. None should be replaced by a structure field whose content is the desired conclusion.
