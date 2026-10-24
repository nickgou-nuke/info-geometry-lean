# Native split-octonion Clifford noninjectivity

G-A sandbox candidate, uncompiled. Parent owns independent AA/QA and promotion.
No live edits or builds. Exact carrier and scalar field are retained.

## Contract

Prove `¬ Function.Injective splitOctonionLeftCliffordRepresentation` in
`InfoGeometry.Lie.SplitOctonionImaginaryAction` for the existing map
`CliffordAlgebra leftCliffordQuadratic →ₐ[ℝ] Module.End ℝ CanonicalZorn`.
Two small dimension lemmas expose the reusable numerical facts: source 128,
target 64. An injective linear map would give 128 ≤ 64, a contradiction.
No surjectivity, exact kernel dimension, or explicit kernel element is claimed.

## Source-grounded reuse

- `Lie/SplitOctonionCliffordAction.lean`: actual quadratic form,
  `splitOctonionLeftCliffordRepresentation`, its generator evaluation, and
  `imaginaryLeftMul_injective`. The representation uses mathlib's Clifford lift.
- `Lie/SplitOctonionImaginaryAction.lean`: `Imaginary` is the trace kernel
  inside CanonicalZorn; `imaginaryCoordLinearEquiv` proves
  `finrank_imaginary = 7` on that actual subtype.
- `Lie/SplitOctonionAnnihilatorDimension.lean`: `canonicalZorn_finrank = 8`,
  transported through `kingdonCanonicalLinearEquiv` from native Kingdon dimension.
- Mathlib `CliffordAlgebra/Contraction.lean`: `CliffordAlgebra.equivExterior`,
  a linear equivalence, requiring invertible 2 (available over ℝ).
- Mathlib `ExteriorAlgebra/Basis.lean`: `Module.Basis.ExteriorAlgebra`, indexed
  by finite subsets of the original basis index. A native basis indexed by
  Fin 7 gives 2^7 = 128. The basis is local, not a new carrier.
- Mathlib `FreeModule/Finite/Matrix.lean`: `Module.finrank_linearMap` and
  the finite-dimensional endomorphism instance give 8*8 = 64.
- Mathlib `Dimension/StrongRankCondition.lean`:
  `LinearMap.finrank_le_finrank_of_injective` needs finite-dimensional target;
  the candidate obtains it from the native dimension-eight theorem.

Related repository precedents were inspected: `CliffordWeyl/SplitCliffordGrades`
and `Clifford/Cl12RealCliffordEquivalence` use the Clifford/exterior basis route.
`Canonical/CanonicalZornCliffordIsomorphism` concerns a DIFFERENT complex
sixteen-dimensional Dirac carrier and states target dimension 256; it is not
evidence of injectivity for this real seven-generator action. Bounded searches
of the representation name and dimension/noninjectivity variants found no
existing noninjectivity theorem for this exact map.

## Mathematical distinction

The native generator map `Imaginary →ₗ[ℝ] Module.End ℝ CanonicalZorn` is
injective by evaluation at one. Its extension from the full Clifford algebra
cannot be injective because the domain is larger than the target. The proposal
therefore refutes the claimed full Clifford embedding, without disputing the
generator injection or the existing universal-property representation.

All ingredients have source APIs; no dimension API gap was found. Elaboration,
axiom dependencies, and warning checks remain pending the independent locked
QA lane. No new structures, substitute matrix carrier, or classification of
real Clifford algebras is required.
