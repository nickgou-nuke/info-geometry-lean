# Projected associator dissipation: theorem contract

This contract separates the mathematical target from its validation status. See [the review record](ASSOCIATOR_DISSIPATION_REVIEW.md) for the exact source, commands and observed results.

## Source and intended scope

The input is `Pasted text(20261117-091139).txt`, SHA256 `1fef0d88c605c9d59f6590503b776362454f6b30b5022bbdec25dc1b12960e48`. The selected content is a finite algebraic construction: actual split-octonion associators become bounded operators in a positive coordinate metric, whose projected adjoint squares produce an energy-degenerate nonnegative response. The input's narrative and claimed unique physical synthesis supply no theorem hypotheses.

The owner surface comprises `Thermo/ProjectedGramDissipation`, `Lie/SplitOctonionScalarPotentialObstruction`, and `Lie/SplitOctonionAssociatorDissipation`. Source inspection records 48 theorem statements and 11 definitions. Native declaration-audit counts are separate and must be filled from an actual run.

## Exact mathematical obligations

**Generic operator construction.** Let E and F be complete real inner-product spaces, let the index type be finite, let `Rᵢ : E →L[ℝ] F` be actual bounded maps, and let h ∈ E. Use the native orthogonal projection P onto the orthogonal complement of the span of h. Define

$$
M=\sum_i(R_iP)^\dagger(R_iP).
$$

Prove its ordered sandwich expression, self-adjointness, full bilinear pairing, positivity and Mh = 0. Prove that Mx = 0 is equivalent to every Rᵢ(Px) vanishing, and that strict positive quadratic production is equivalent to one nonzero projected image. The empty family and h = 0 are included.

**Actual split-algebra identities.** Use the canonical real Zorn carrier and its existing multiplication and conjugation. Prove the scalar sandwich identity with the exact trace normalization, including zero scalar part for a skew-conjugate middle argument. Transport the existing normalized polar form and reuse the existing split-axis involution and neutral-form API. Prove the half-norm cross pairing and its value 1/2 at the identity. Supply the explicit nonzero ambient associator with two arguments in the existing split-quaternion core, and prove the third lies outside that core.

**Positive coordinates and concrete channels.** Construct a native linear equivalence to `EuclideanSpace ℝ (Fin 2 ⊕ (Fin 3 ⊕ Fin 3))`, with the norm-square equal to the sum of all eight coordinate squares. This is an auxiliary positive metric, distinct from the indefinite split norm. Define each first-variable associator by the ordered right-action defect

$$
R_{a,b}=R_b\circ R_a-R_{ab},\qquad
R_{a,b}(v)=(va)b-v(ab).
$$

Transport it to a bounded Euclidean operator using finite-dimensional continuity. Specialize the generic M to any finite selected family. State its quadratic readout, kernel and strictness using the actual projected vector pulled back to Zorn coordinates. Associativity gives a zero channel when all three actual arguments lie in the core; membership of the input alone is insufficient.

**Pointwise flow laws.** Instantiate the existing `InfoGeometry.SuperMetriplectic.OnsagerMetricData` and `MetriplecticFlow` wrappers with the constructed operators, deriving their positivity, symmetry and energy fields. For γ ≥ 0 and a skew-adjoint bounded J, the vector `v = Jh + γMs` satisfies `⟨h,v⟩ = 0`. Under the additional explicit hypothesis Js = 0, its entropy readout is `⟨s,v⟩ = γ Σᵢ ‖RᵢPs‖²`. Strict positivity of that scaled readout would additionally require γ > 0.

## Reused obstruction and excluded conclusions

The existing `GenericMetriplecticFlow.System.entropy_covector_eq_zero_of_injective` and `entropy_rate_zero_of_injective` record that an injective Poisson operator with a full entropy Casimir forces zero production. Commutation with one Hamiltonian is a weaker hypothesis and does not establish the universal Casimir axiom.

This package makes no claim about Jacobi identities, differentiable energies or entropies, trajectory existence, smoothness of a varying projection at h = 0, a full 49-channel kernel classification, invariance under the split automorphism group, global para-Kähler geometry, Ricci signs, Gibbs convergence, Landauer heat, or uniqueness of a spinor/tensor representation. Those require separate data and proofs.

## Validation record

Source review, fresh compilation of the selected owners and source closure, zero warnings for the three owners, native declaration audit, independent QA, staged gate and push/root gate are separate acceptance surfaces. The scoped workflow invokes the unchanged maintained checker with no repository-artifact reuse or audit bypass. It does not certify `InfoGeometry.All` or a root Lake build. Native and integration status must be read from the dated review record, not inferred from the presence of source files.
