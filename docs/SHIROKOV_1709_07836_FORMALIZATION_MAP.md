# Formalization map: Shirokov, arXiv:1709.07836v2

Source: Dmitry S. Shirokov, *Covariantly constant solutions of the Yang–Mills
equations*, arXiv:1709.07836v2 (2018). The statements below are contracts
extracted from the supplied PDF, not claims that the paper is fully formalized.

## Mathematical carriers and conventions

The paper uses a real Clifford algebra `Cl_{p,q}` (also its h-form
realization), spacetime indices `μ, ν`, Clifford-frame indices `a`, and
commutator `[x,y] = xy - yx`. Its compatible-frame equation is

```text
∂_μ h_a - [C_μ, h_a] = 0.
```

The Yang–Mills convention is

```text
F_{μν} = ∂_μ B_ν - ∂_ν B_μ - [B_μ,B_ν],
D_μ F^{μν} = ∂_μ F^{μν} - [B_μ,F^{μν}].
```

Any bridge must preserve these signs, the distinction between frame index `a`
and coordinate index `μ`, and the paper's pseudo-Euclidean metric. Existing
positive-definite orthonormal-frame results are special cases only.

## Theorem contracts and current owner evidence

| Paper result | Lean-level contract | Existing owner and boundary |
|---|---|---|
| (1.4)–(1.5), Thm. 1.1 | The frame elements lie in the complement of the center; the odd-volume trace condition is stated to ensure independence of the ordered products. | `shirokov_frame_vectors_noncentral` proves noncentrality under the Clifford relations when the dimension is at least two and each frame element has nonzero scalar square. `shirokov_isometry_frame_blade_basis` proves the ordered blades form a basis for frames induced by an isometry of the fixed negative-definite `Cl(0,n)` quadratic space. This does not yet derive an arbitrary pointwise frame map from (1.4)–(1.5), cover general signatures, or formalize the odd-volume trace argument. At `n=1`, the odd Clifford algebra is commutative, so the complement of the center is empty and the theorem requires a dimension qualification. `Canonical.KahlerAtiyahCartanForms` separately constructs `c_g(v)=ε(v)+ι(g(v,-))` and proves its symmetric Clifford anticommutator. |
| Thm. 1.2 | Under `S⁻¹∂_μS` in the spin Lie algebra, `h'_a=S⁻¹h_aS` and `C'_μ=S⁻¹C_μS-S⁻¹∂_μS` satisfy the same compatibility equation. | `shirokov_theorem_1_2_gauge_covariance` proves exact transport of the pointwise residual `Dₓa-[C(x),a]` for any unit `g`, derivation-lane direction, and noncommutative coefficient algebra. Its transformed covariant one-form is `g⁻¹Dg-g⁻¹Cg`, the negative of the paper's transformed connection under this owner's `D + [Γ,·]` convention. The theorem covers the algebraic pointwise gauge law; a smooth base-space spin-group-valued field and its differentiability remain unmodeled. |
| Thm. 1.3, (1.8) | Given the stated Clifford-frame hypotheses, the commutator system has a unique spin-Lie-valued solution, expressed using grade projections and inverse coefficient matrices. | `Canonical.KahlerAtiyahSpinConnection.metricSkewSpinLift` constructs a basis-independent lift of metric-skew endomorphisms and proves its action on Clifford generators. `shirokov_grade_two_unique_of_vector_commutators` proves uniqueness of a grade-two coefficient from its commutator action on all vectors in the fixed negative-definite finite-stage `Cl(0,n)` carrier. `shirokov_even_grade_projection_denominator_pos` verifies the scalar factors `1/(n-λᵢ)` are defined under the one-based index bounds. `shirokov_even_grade_projection_matrix_isUnit` proves the explicit power matrix with columns indexed by `λᵢ=(-1)^i(n-2i)` is invertible over `ℚ` for even `n`, using Mathlib's Vandermonde determinant theorem. `shirokov_generator_sandwich_blade`, `shirokov_grade_sandwich_blade_scalar`, and `shirokov_grade_sandwich_blade_eigenvalue_action` evaluate the standard-frame sandwich action on each ordered blade as `-λ_|S|`; the sign comes from the negative generator square in this `Cl(0,n)` carrier. `shirokov_even_grade_scalar_interpolation` proves that the inverse Vandermonde coefficients isolate each sandwich eigenvalue over `ℚ`. `shirokov_even_grade_projector_blade` and `shirokov_even_grade_projector_apply` lift the interpolation to the Clifford-valued grade-projection identity on the ordered-blade basis of fixed `Cl(0,n)`. Existence under (1.4)–(1.5), and general signatures and moving-frame hypotheses remain open. |
| Thm. 1.4, (1.9) | Compatibility for all frame generators implies the induced connection curvature vanishes, subject to the paper's frame and grade hypotheses. | `covariantDerivative_zero_of_clifford_generators` extends parallelness from Clifford vectors to all Clifford elements using `CliffordAlgebra.adjoin_range_ι`. `shirokov_curvature_defect_eq_connection_commutator` reduces the defect, under the stated compatibility convention, to `[C₁,C₂]`. `shirokov_clifford_compatibility_curvature_central` proves this bracket is central when coordinate directions commute. `shirokov_curvature_flat_of_grade_two_connection_commutator` then forces it to vanish if it has grade-two blade support. Closure of the grade-two subspace under commutators, and the paper's moving-frame/signature hypotheses, remain open. |
| Thms. 2.1–2.2, (2.1)–(2.3) | The Leibniz rule extends compatibility from generators to ordered products. Theorem 2.2's displayed formula is `C_μ = 2⁻ⁿ Σ_A (∂_μ h^A)h_A`, with `h^A` the dual/inverse frame notation, and has an odd-dimensional reduced sum. | `shirokov_theorem_2_1_ordered_frame_products` states the ordered-word result over a noncommutative coefficient algebra, using `covariantDerivative_list_prod_zero`. `shirokov_theorem_2_2_average_reduction` proves the noncommutative sum reduction conditional on compatibility and the center-projection Reynolds identity. The standard-frame inverse-blade average and odd reduced sum are proved on individual ordered blades; extension to arbitrary coefficients, vanishing-center-component hypotheses, and transport to the paper's varying dual frame remain open. `covariantDerivative_zero_of_algebra_generators` and its Clifford specialization extend vanishing to the generated algebra; `covariant_frameTransport_list_product_zero` handles pure-gauge transported products. |
| Thms. 3.1–3.3 | Covariant differentiation acts coefficientwise in a parallel frame; it obeys additivity, Leibniz, commuting-derivative under flatness, and the stated connection Bianchi identities. | `DerivationDifferentialForms` constructs native CE derivatives, curvature, commutator-curvature, and Bianchi. `MaurerCartanFrameTransport.gaugeForm_flat` derives flatness of a pure gauge. The coordinate-field coefficient theorem still needs an explicit field/carrier map. |
| Thm. 4.1 | With flat compatible `C`, covariantly constant `K_μ`, and `[K_μ,[K^μ,K^ν]]=J^ν`, the ansatz `B_μ=C_μ+K_μ` solves both field equations with `F_{μν}=-[K_μ,K_ν]`. | `Canonical.ShirokovYangMillsTransfer` compiles the finite-coordinate algebraic transfer. It proves curvature, the pointwise covariant-current identity, its finite unweighted sum, and a pseudo-Euclidean version that raises both contracted indices using diagonal signs. The coefficient algebra is abstract and the derivation family is supplied as structure data; the Clifford-frame compatibility hypotheses and their derivation remain to be connected. |
| Thm. 5.1 | The Thm. 4.1 transfer specializes to constant h-form coefficients. | Requires a finite-dimensional h-form field carrier and the Thm. 4.1 bridge. No separate h-form coefficient owner was found in the bounded search. |
| Thm. 5.2 | For Clifford vectors, the contracted expression `Σ_μ [h_μ,[h^μ,h^ν]]` reduces to `4(n-1)h^ν`; scaling by `σ` gives current `εh^ν`, `ε=4(n-1)σ³`, and hence the Thm. 5.1 solution. | `Canonical.KahlerAtiyahSpinConnection` supplies positive and diagonal pseudo-Euclidean frame contractions. `Canonical.ShirokovCliffordYangMills` now composes these with the finite-coordinate transfer, proving both curvature and current formulas under explicit flat-background and scaled-frame parallelness hypotheses. Those hypotheses are not yet derived from the paper's Clifford-frame equations. |
| Thm. 5.3 | For a pure grade-one frame, the spin connection is `C_μ=(1/4)(∂_μh_ν)h^ν`; then `B_μ=σh_μ+C_μ` has the same cubic current. | `frameDerivativeMap` extends the supplied frame-direction values linearly; `frameDerivativeMap_metricSkew` derives metric-skewness from the differentiated frame-pairing identity. `spinConnectionFromFrameDerivative_eq_quarter_product` proves the pointwise frame formula. `shirokov_pseudo_frame_derivative_yang_mills` composes this spin lift with the Yang–Mills transfer: it derives parallelness from the derivative action and proves the field-strength/current claims, conditional on flatness of the spin connection. These are finite-frame/first-jet statements; no base manifold, smooth frame field, or proof of spin-connection flatness from the paper's global compatibility equations is supplied yet. |

### Theorem 1.3 follow-up

`shirokov_grade_sandwich_blade_eigenvalue_action` evaluates the standard-frame
sandwich operator on every ordered blade as the negative of the paper's grade
eigenvalue. The sign is due to the negative generator square in this fixed
`Cl(0,n)` carrier. The even-dimensional Vandermonde interpolation is lifted by
`shirokov_even_grade_projector_blade` to ordered blades and by
`shirokov_even_grade_projector_apply` to arbitrary elements, where it agrees
with the ordered-blade-coordinate grade projection. The follow-up
`shirokov_even_grade_projector_compose_blade` proves the composition law on
individual blades. The corresponding operator-level composition law and
existence under the paper's moving-frame hypotheses remain open.

## Implementation order

1. Compatibility on Clifford generators now propagates to the generated
   algebra and implies centrality under commuting coordinate directions.
   Still prove the Clifford-grade/center intersection needed for flatness, and
   the full-basis averaging formula using the actual coefficient/projection
   maps. In the supplied PDF, Theorem 2.2 uses `h^A` in the derivative factor
   and `h_A` on the right; its proof sums over `A` and uses the dual-frame
   identities. Reference [16], Theorem 3.2 ([arXiv:1412.0246](https://arxiv.org/abs/1412.0246)),
   gives the standard-frame Reynolds operator
   `2⁻ⁿ Σ_A (e^A)⁻¹ U e^A = π₀(U)` for even `n`, and
   `π₀(U)+πₙ(U)` for odd `n`. The Lean transport still needs the exact map
   from this standard basis result to the varying frame `h^A`, the dual-frame
   product/normalization, and the odd-dimensional reduced-sum identity. The
   factor `2⁻ⁿ` also requires a coefficient field where `2^n` is invertible.
   The current owner now also proves `shirokov_blade_conjugation_sign`, by
   composing the repository's `cBlade_mul_swap_overlap` and `cBlade_sq` laws.
   This is a concrete character coefficient for conjugation by ordered blades
   in the existing negative-definite `Cl(0,n)` carrier. It is not yet the
   Reynolds sum, a center projection, or the varying-frame identity.
   The coordinate product formula and parity cancellation are now proved for
   the overlap sign: `shirokov_blade_swap_sign_character` identifies the
   coefficient with a product of one-coordinate signs, and
   `shirokov_blade_swap_average_vanishes` proves its sum is zero for even
   nonempty grades and odd non-top grades. The owner now proves the
   algebra-valued average `shirokov_noncentral_blade_reynolds_vanishes` for
   noncentral blade basis elements, and `shirokov_scalar_blade_reynolds_average`
   for the scalar blade. In odd dimension,
   `shirokov_odd_pseudoscalar_reynolds_average` proves that the top-grade
   pseudoscalar is fixed with factor `2^n`. These results use the existing
   negative-definite `Cl(0,n)` basis, inverse-blade conjugation, and a finite
   powerset average. They do not yet construct the center projection for
   arbitrary multivectors, identify the average with that projection on the
   whole algebra, transport it to a varying dual frame, or prove the
   odd-dimensional reduced-sum transport required by Theorem 2.2. The new
   `shirokov_blade_reynolds_formula` packages the scalar/top/noncentral cases,
   and `shirokov_reynolds_finite_blade_support` extends that computation by
   linearity to any explicitly supplied finite blade expansion. The owner now
   proves `shirokov_blade_coordinates_injective` and
   `shirokov_blade_expansion`: every element of the negative-definite finite
   stage `Cl(0,n)` equals the finite powerset sum of its ordered-blade
   coordinates. The composed theorem `shirokov_reynolds_all_elements`
   consequently applies the Reynolds average formula to every element of this
   carrier. The identification of this average with the
   paper's center projection, transport to a varying dual frame, and the
   odd-dimensional reduced-sum identity required by Theorem 2.2 remain open.
   The owner now proves `shirokov_odd_complement_sum_reduction`: for an odd
   finite index cardinality and any complement-invariant function on its
   powerset, the full sum is twice the sum over subsets strictly below the
   midpoint. This is only the finite combinatorial pairing argument. The
   paper's summand depends on a moving dual Clifford frame; its complement
   invariance and the normalization/identification needed to derive equation
   (2.3) from this lemma have not yet been proved. The owner additionally
   proves `shirokov_odd_blade_character_complement_invariant`,
   `shirokov_odd_blade_reynolds_reduced_sum`, and
   `shirokov_odd_reynolds_reduced_sum`: for each ordered blade, the standard
   inverse-blade conjugation signs agree on complementary subsets. By the
   ordered-blade expansion, this yields the reduced powerset sum for every
   element of the fixed finite-stage negative-definite `Cl(0,n)` carrier. It
   also proves `shirokov_theorem_2_2_standard_frame_odd_reduced_sum`: under
   the standard-frame compatibility equation, the paper's derivative
   summands reduce to twice their lower-half sum. No grade-two assumption is
   needed for this reduced identity. It does not yet transport the identity
   to the paper's moving dual frame or derive the compatibility premise from
   the paper's global geometric hypotheses. Finally,
   `shirokov_theorem_2_2_standard_frame_odd_grade_two` combines that reduction
   with the full standard-frame average: for odd `n`, grade-two-supported `C`,
   and the explicit standard-frame compatibility premise, the lower-half
   derivative sum is `(2^(n-1) : ℝ) • C`. This remains a fixed-frame,
   negative-definite `Cl(0,n)` result; it does not establish the moving dual
   frame formula or derive either hypothesis from the paper's geometric
   setup. The owner also has `shirokov_theorem_2_2_automorphism_frame_odd_grade_two`,
   which transports the odd lower-half formula along a real algebra
   automorphism when the pulled-back coefficient is grade two. This covers
   isometry-induced frames through the existing Clifford algebra equivalence;
   it does not cover arbitrary non-orthonormal moving frames or construct a
   field of such frames over a base manifold.
2. Connect the finite-coordinate `C+K` transfer's derivation family to the
   repository's CE/exterior-form carrier; derive its flatness and parallelness
   hypotheses from the Clifford-frame compatibility equations.
3. Construct the base-space frame field and directional derivative, prove the
   frame-pairing identity is differentiated to the pointwise compatibility
   premise, and derive spin-connection flatness from the paper's Clifford-frame
   compatibility equations.
4. Audit each new declaration's axioms and compile the affected owners.

## Validation boundary at this revision

The owner `InfoGeometry.Canonical.KahlerAtiyahSpinConnection` (including the
conditional finite-frame Theorem 5.3 formula) passed a locked Lake
build after this extension (3,165 jobs, exit code 0). Earlier, the owners
`InfoGeometry.Canonical.ShirokovYangMillsTransfer` and
`InfoGeometry.Canonical.ShirokovCliffordYangMills` passed a locked Lake build
targeting the Clifford specialization and its dependencies (3,167 jobs, exit
code 0). A temporary `#print axioms` audit of both Clifford-vector
specializations and the scaled pseudo contraction reported only
`[propext, Classical.choice, Quot.sound]`; the metric-dual-frame and composite
pseudo-orthonormal quarter-frame-product theorems have the same reported
dependencies. The strict screener reports three
T16 hits on older operator-algebra tactics in the enlarged spin-connection
owner (lines 276, 419, and 487); it reports no hit on the new declarations.
The two added frame-derivative declarations also report only
`[propext, Classical.choice, Quot.sound]` in `#print axioms`; so does
`shirokov_pseudo_frame_derivative_yang_mills`.
The new `shirokov_theorem_2_2_standard_frame_odd_grade_two` extension passed
the locked owner build (9,091 jobs, exit code 0), the owner axiom checker
(1 module passed), and the strict OpenGauss screen (0 traps). The follow-up
`shirokov_theorem_2_2_automorphism_frame_odd_grade_two` passed the locked
direct file check and targeted owner build (9,091 jobs, exit code 0), the
owner axiom checker (1 module passed), and the strict OpenGauss screen (0
traps). The owner build and direct file checks report existing linter warnings
in this enlarged file and its dependencies; no warning-free claim is made
here. A staged proof-proxy gate passed for the first extension's two
task-owned files; it will be rerun for this follow-up checkpoint.
The compatibility-to-centrality theorem and its final cleaned proof passed a
9,029-job targeted build of `InfoGeometry.Canonical.ShirokovCliffordYangMills`
(exit code 0). Replayed dependencies emitted pre-existing warnings. The native
module axiom checker passed all declarations in this owner, and the strict
OpenGauss screen reported zero traps in this owner and
`MaurerCartanFrameTransport`. The
paper-specific `shirokov_theorem_2_1_ordered_frame_products` extension also
passed the same targeted owner build, owner axiom audit, and strict screen in
this session. The conditional, division-free algebraic reduction
`shirokov_theorem_2_2_average_reduction` was added to the same owner; its
targeted 9,029-job locked build passed (exit code 0), its owner axiom checker
passed (1 module, 0 failures), and its strict screen reported zero traps.
It yields `card • (C - centerProj C)` under an explicit finite Reynolds-average
hypothesis; it does not prove that hypothesis for `CliffordAlgebra`, nor that
the center projection of the paper's connection is zero. The generic
ordered-product and generator-to-algebra lemmas,
including the Clifford specialization, passed a 9,024-job locked build of
`InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport`. The Clifford-grade/
center vanishing required for (1.9), and the paper's full-basis averaging
formula with its identification as the unique spin connection, remain open.
The new `shirokov_blade_conjugation_sign` declaration compiled in the targeted
owner build (9,091 jobs); the axiom checker passed 1 module with 0 failures,
and the strict screener reported 0 traps. The follow-up coordinate-factor,
parity-cancellation, and overlap-character theorems also compile in the same
targeted owner build (9,091 jobs). The subsequent inverse-blade and
Clifford-valued Reynolds results, including scalar and odd top-grade fixed
terms, passed the current targeted build of
`InfoGeometry.Canonical.ShirokovCliffordYangMills`; the strict screener
reported zero traps and Gate 4's generated `#print axioms` audit passed for
all 18 public declarations in the owner. This finite-stage average still
does not prove a center-projection theorem for arbitrary multivectors or the
varying-frame/odd-reduced-sum transport in Theorem 2.2.
The later `shirokov_blade_reynolds_formula`,
`shirokov_reynolds_blade_expansion`, and
`shirokov_reynolds_finite_blade_support` extensions compile in the same
targeted owner build. The current extension also proves injectivity of the
ordered-blade coordinate map by finite-dimensional rank equality and proves
`shirokov_blade_expansion` by constructing the coordinate preimage from the
finite powerset sum. The composed theorem `shirokov_reynolds_all_elements`
therefore states the average formula for arbitrary elements of this finite-stage
carrier. This remains a
finite algebra identity; it does not by itself identify the average with the
paper's center projection or supply the varying-frame transport and
odd-dimensional reduced-sum identity.
The current extension also proves
`shirokov_reynolds_noncentral_coordinate_zero`: every coordinate other than
the scalar coordinate and (in odd dimension) the top-blade coordinate
vanishes. This is a support theorem in the ordered-blade basis; it does not
yet identify the Reynolds average with the algebraic center projection. The
owner now also proves `shirokov_odd_top_blade_mem_center` for odd `n` by
commuting the volume blade with the Clifford generators and extending over
their generated algebra, then composes this with the support formula in
`shirokov_reynolds_mem_center`. The owner further proves
`shirokov_reynolds_eq_card_smul_of_mem_center`: the unnormalized average acts
as multiplication by `2^n` on every central element. After normalization,
`shirokovCenterProjection` has range in the algebraic center, fixes every
central element, and is idempotent. Thus the standard-frame finite-stage
operator is a genuine projection onto the center of `Cl(0,n)`. This does not
yet transport the result to the paper's varying dual frame or prove the
odd-dimensional reduced-sum identity. The new
`shirokov_center_coordinate_support` theorem also shows that a central
element has zero ordered-blade coordinates outside the scalar coordinate and,
in odd dimension, the top-blade coordinate. Its proof composes the center
projection fixed-point theorem with the Reynolds coordinate-support theorem.
`shirokov_center_two_coordinate_expansion` packages that support result as an
explicit decomposition: every central element is its scalar blade component,
plus its top-blade component when the dimension is odd. This is a center
classification for the standard finite-stage `Cl(0,n)` carrier only; the
paper's moving dual frame remains outside this theorem.
The new `shirokov_center_grade_two_eq_zero` theorem proves the scalar/top
center has zero intersection with elements whose ordered-blade coordinates
are supported only in grade two. This is the finite-stage center/grade
intersection needed for a curvature-defect argument, conditional on proving
that the defect has grade-two support. The new
`shirokov_center_projection_eq_zero_of_grade_two` also shows that the
standard-frame Reynolds center projection annihilates any grade-two-supported
element. This can discharge the center-projection term in the conditional
Theorem 2.2 reduction once a separate theorem identifies the paper's varying
dual-frame sum with this standard average.
`shirokovInverseBladeUnit` now packages each inverse ordered blade as a unit,
and `shirokov_standard_frame_average` identifies its finite conjugation sum
with the normalized Reynolds center projection. Composing that identity with
`shirokov_center_projection_eq_zero_of_grade_two` proves
`shirokov_theorem_2_2_standard_frame_grade_two`: for a compatible derivation
and a grade-two-supported connection coefficient, the standard-frame average
equals the frame cardinality times that coefficient. This is still a
standard-frame specialization.
`shirokov_automorphism_frame_average` transports the average through a real
Clifford algebra automorphism, and
`shirokov_theorem_2_2_automorphism_frame_grade_two` gives the corresponding
Theorem 2.2 result when the pulled-back coefficient is grade two.
`shirokov_isometry_map_blade` identifies the frame blades for the automorphism
induced by a quadratic-form isometry: they are ordered products of the
transformed coordinate vectors. The named frame-vector operations prove the
transformed generators still square to `-1` and pairwise anticommute, while
`shirokovIsometryInverseBladeUnit` packages each transformed inverse blade as
a unit and exposes its value and inverse. Thus the transported Reynolds
identity applies to fixed orthogonal changes of frame in this negative-
definite `Cl(0,n)` carrier. Arbitrary point-dependent dual-frame transport,
other signatures, and the paper's odd-dimensional reduced sum remain open.
The owner also includes the concrete noncommutativity witness
`shirokov_generators_noncommute` for the first two generators of the real
negative-definite two-dimensional Clifford algebra. This is a separate carrier
sanity check; it does not strengthen the standard-frame theorem.
For Theorem 1.4, `shirokov_clifford_compatibility_curvature_eq_zero_of_grade_two`
closes the conditional last step on the fixed negative-definite finite-stage
carrier: commuting derivation directions and generator compatibility make the
defect central, and an explicit grade-two support premise forces it to vanish.
`shirokov_grade_two_support_sub` and
`shirokov_clifford_compatibility_curvature_eq_zero_of_component_grade_two`
decompose this into support premises for the two differentiated connection
terms and their commutator. Those component premises are still not derived
from the paper's geometric hypotheses; other signatures and a varying
base-space frame are also outside this theorem.
The automorphism-frame average and Theorem 2.2 specialization passed the locked
file check and targeted locked Lake build of
`InfoGeometry.Canonical.ShirokovCliffordYangMills` (9,091 jobs, exit code 0).
The owner axiom audit passed (1 module, 0 failures), and the strict source
screen reported 0 traps. These checks cover the owner, not the full repository.
This remains a statement about the repository's standard negative-definite
finite-stage carrier, not a varying-frame classification theorem. The updated
owner passed both the locked Lean file check and the targeted locked Lake
build of `InfoGeometry.Canonical.ShirokovCliffordYangMills` (9,091 jobs,
exit code 0). The owner axiom audit, strict source screen, staged proof proxy
gate, and diff checks also passed for this addition. These validations cover
the owner and staged files only; they do not close the paper's remaining
varying-frame contracts. The earlier targeted locked build of
`InfoGeometry.Canonical.ShirokovCliffordYangMills` passed (9,091 jobs, exit
code 0); the owner axiom audit passed (1 module, 0 failures), the strict
OpenGauss source screen passed (0 traps), and the staged proof proxy gate
passed. These checks cover this owner and staged surface only; they do not
certify the whole repository or close the remaining paper contracts.
The earlier strict screen of the new Shirokov bridge reported zero traps. The
automated GATE_4 review was rejected before
kernel verification because the repository-wide staged Lean set fails its QMS
staged-hook check; that finding is unrelated to an axiom dependency result.
`git diff --check` and `git diff --cached --check` passed at the last
inspection. A broader build of
`Canonical.All` failed after replaying dependencies and exposing unrelated
workspace errors, including `Canonical.Unification`,
`CuntzPrimitiveExactness`, `CantorBernoulliFiniteDiagonalGNSBridge`,
`CuntzMatrixTraceTopologicalColimit`, and `DAG.GraphHodgeBridge`; the failure
list also included many downstream targets. This is not an umbrella
integration certificate. The paper is not fully formalized: the remaining
theorem contracts above are still open.
The odd complement-pairing lemma subsequently passed the locked file check and
targeted owner build (9,091 jobs, exit code 0). Its complement-invariance
hypothesis is explicit and has not yet been discharged for Shirokov's
varying-frame summand.
The generic noncentrality implication for dimension `m + 2` was then checked
with `run_locked_lean.py` and the targeted locked Lake build (9,091 jobs,
exit code 0); the owner axiom audit passed (1 module, 0 failures), and the
strict OpenGauss source screen reported 0 traps. The file check emitted only
the owner's existing linter warnings. These checks do not establish ordered
blade independence or formalize the full Theorem 1.1 hypotheses.
The isometry-frame blade basis result was checked with the same locked owner
file command and targeted module build (9,091 jobs, exit code 0); the owner
axiom audit passed (1 module, 0 failures), and the strict OpenGauss screen
reported 0 traps. This is a concrete transported-frame basis theorem; it does
not establish the PDF's general odd-volume trace criterion.
The pointwise Theorem 1.2 gauge-covariance identity also passed the locked
owner file check and targeted Lake build, the owner axiom audit (1 module,
0 failures), and the strict source screen (0 traps). These checks verify the
derivation-lane theorem only; they do not construct smooth spin-group fields
on the paper's pseudo-Euclidean base space.
