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
| (1.4)–(1.5), Thm. 1.1 | Clifford anticommutation plus the odd-dimensional volume condition imply the frame elements are vectors in the generated Clifford grading. | `Canonical.KahlerAtiyahCartanForms` constructs `c_g(v)=ε(v)+ι(g(v,-))` and proves its symmetric Clifford anticommutator. It does not formalize Shirokov's odd-dimensional trace condition or grade-projection classification. |
| Thm. 1.2 | Under `S⁻¹∂_μS` in the spin Lie algebra, `h'_a=S⁻¹h_aS` and `C'_μ=S⁻¹C_μS-S⁻¹∂_μS` satisfy the same compatibility equation. | `OperatorAlgebra.MaurerCartanFrameTransport.gaugeForm_product` proves the nonabelian logarithmic-derivative law and frame transport in a derivation lane. A specific smooth `S`-field action on the PDF's Clifford frame still needs a bridge. |
| Thm. 1.3, (1.8) | Given the stated Clifford-frame hypotheses, the commutator system has a unique spin-Lie-valued solution, expressed using grade projections and inverse coefficient matrices. | `Canonical.KahlerAtiyahSpinConnection.metricSkewSpinLift` constructs a basis-independent lift of metric-skew endomorphisms and proves its action on Clifford generators. It does not yet prove Shirokov's grade-projection formula or the exact uniqueness theorem under (1.4)–(1.5). |
| Thm. 1.4, (1.9) | Compatibility for all frame generators implies the induced connection curvature vanishes, subject to the paper's frame and grade hypotheses. | `covariantDerivative_zero_of_clifford_generators` extends parallelness from Clifford vectors to all Clifford elements using `CliffordAlgebra.adjoin_range_ι`. `shirokov_clifford_compatibility_curvature_central` composes this with the derivation representation law and proves centrality of the coordinate curvature defect when the coordinate directions commute. The final Clifford-grade/center argument that forces the defect itself to vanish remains open; the new theorem does not establish it. |
| Thms. 2.1–2.2, (2.1)–(2.3) | The Leibniz rule extends compatibility from generators to ordered products. Theorem 2.2's displayed formula is `C_μ = 2⁻ⁿ Σ_A (∂_μ h^A)h_A`, with `h^A` the dual/inverse frame notation, and has an odd-dimensional reduced sum. | `shirokov_theorem_2_1_ordered_frame_products` states the ordered-word result over a noncommutative coefficient algebra, using `covariantDerivative_list_prod_zero`. `shirokov_theorem_2_2_average_reduction` proves the noncommutative sum reduction conditional on compatibility and the center-projection Reynolds identity. The Clifford-specific average, vanishing center component, and odd-dimensional reduced-sum transport remain open. `covariantDerivative_zero_of_algebra_generators` and its Clifford specialization extend vanishing to the generated algebra; `covariant_frameTransport_list_product_zero` handles pure-gauge transported products. |
| Thms. 3.1–3.3 | Covariant differentiation acts coefficientwise in a parallel frame; it obeys additivity, Leibniz, commuting-derivative under flatness, and the stated connection Bianchi identities. | `DerivationDifferentialForms` constructs native CE derivatives, curvature, commutator-curvature, and Bianchi. `MaurerCartanFrameTransport.gaugeForm_flat` derives flatness of a pure gauge. The coordinate-field coefficient theorem still needs an explicit field/carrier map. |
| Thm. 4.1 | With flat compatible `C`, covariantly constant `K_μ`, and `[K_μ,[K^μ,K^ν]]=J^ν`, the ansatz `B_μ=C_μ+K_μ` solves both field equations with `F_{μν}=-[K_μ,K_ν]`. | `Canonical.ShirokovYangMillsTransfer` compiles the finite-coordinate algebraic transfer. It proves curvature, the pointwise covariant-current identity, its finite unweighted sum, and a pseudo-Euclidean version that raises both contracted indices using diagonal signs. The coefficient algebra is abstract and the derivation family is supplied as structure data; the Clifford-frame compatibility hypotheses and their derivation remain to be connected. |
| Thm. 5.1 | The Thm. 4.1 transfer specializes to constant h-form coefficients. | Requires a finite-dimensional h-form field carrier and the Thm. 4.1 bridge. No separate h-form coefficient owner was found in the bounded search. |
| Thm. 5.2 | For Clifford vectors, the contracted expression `Σ_μ [h_μ,[h^μ,h^ν]]` reduces to `4(n-1)h^ν`; scaling by `σ` gives current `εh^ν`, `ε=4(n-1)σ³`, and hence the Thm. 5.1 solution. | `Canonical.KahlerAtiyahSpinConnection` supplies positive and diagonal pseudo-Euclidean frame contractions. `Canonical.ShirokovCliffordYangMills` now composes these with the finite-coordinate transfer, proving both curvature and current formulas under explicit flat-background and scaled-frame parallelness hypotheses. Those hypotheses are not yet derived from the paper's Clifford-frame equations. |
| Thm. 5.3 | For a pure grade-one frame, the spin connection is `C_μ=(1/4)(∂_μh_ν)h^ν`; then `B_μ=σh_μ+C_μ` has the same cubic current. | `frameDerivativeMap` extends the supplied frame-direction values linearly; `frameDerivativeMap_metricSkew` derives metric-skewness from the differentiated frame-pairing identity. `spinConnectionFromFrameDerivative_eq_quarter_product` proves the pointwise frame formula. `shirokov_pseudo_frame_derivative_yang_mills` composes this spin lift with the Yang–Mills transfer: it derives parallelness from the derivative action and proves the field-strength/current claims, conditional on flatness of the spin connection. These are finite-frame/first-jet statements; no base manifold, smooth frame field, or proof of spin-connection flatness from the paper's global compatibility equations is supplied yet. |

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
