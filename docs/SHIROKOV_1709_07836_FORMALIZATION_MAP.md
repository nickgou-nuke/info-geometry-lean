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
and the strict screener reported 0 traps. This extends the finite blade
calculation only; it does not close the Reynolds-average obligation.
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
