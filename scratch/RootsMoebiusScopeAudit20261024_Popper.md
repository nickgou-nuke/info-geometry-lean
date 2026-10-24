# Roots/Möbius intake: bounded independent source audit

Disposition: REQUEST_CHANGES for the broad interpretation; valid algebraic replacements identified.
Read-only owner inspection, no builds or tests. This record does not certify new Lean declarations.

## Exact corrections and minimal contracts

1. An involution Γ²=1 has inverse Γ, not −Γ. For Γ²=Δ the same statement holds in the active corner with identity Δ. WΓW=−Γ is sign reversal, not inversion of Γ and not a Klein-bottle theorem.
2. Valid torus relation: let p,q be orthogonal idempotents, r=1−p−q, W²=1, WpW=q and WqW=p. For a central unit λ, D(λ)=λp+λ⁻¹q+r satisfies D(λ)D(λ⁻¹)=1 in both orders and WD(λ)W=D(λ⁻¹). A commutative-base algebra supplies central parameters. Nonzero is not sufficient for invertibility over an arbitrary ring. These relations alone establish neither a faithful normalizer presentation nor a topological bundle.
3. Nonzero square-zero elements are nonunits, not roots of unity. Polynomial annihilation and support-relative power identities do not establish primitive order or arbitrary-ring classification; zero support and positive characteristic permit degeneration. Rational/Cayley expressions require invertible denominators. Existing Cayley product identities must not be read as unrestricted division formulas.
4. The unnormalized Jordan triple formula gives 2•(xyz+zyx); division by two needs extra assumptions. The associator sign is [y,[x,z]], and the square-zero inner-inverse specialization is −2d. Octonion products retain their parentheses and native signed-basis convention.
5. Moore–Penrose inversion does not imply B=star d. The native example d=2E01, B=(1/2)E10 is MP but not adjoint duality; d+B need not be self-adjoint. Majorana star symmetry needs the separate duality hypothesis.
6. With dB=p, Bd=q and support absorption, d and B are inverse arrows between idempotent objects in the idempotent-completion category of a ring: d:q→p, B:p→q. They need not be ambient units. This is a mathematical interpretation of the equations, not a claimed newly constructed Lean groupoid or geometric bundle.
7. Raw octonion multiplication is nonassociative. Invertible elements cannot simply be treated as an associative group of product-preserving automorphisms. Native left-multiplication nonmultiplicativity obstructs that shortcut. G₂ identification requires an actual appropriate automorphism/derivation construction with its own base assumptions; no such classification follows from these intake identities.

## Native owner references

- Core/JordanAssociatorRing.lean: symm_jordan_triple; symm_associator_eq_double_commutator; symm_triple_eq_symm_sub_commutator; proposed_triple_formula_defect; symm_associator_square_zero_inner_inverse.
- Core/DiracSuperalgebra.lean: majorana_star_symmetry; cayleyPlus_star_eq_cayleyMinus; cayleyMinus_mul_cayleyPlus; cayleyPlus_mul_cayleyMinus; globalMajoranaReflection.
- Core/MajoranaSupportSwap.lean: globalMajoranaReflection_conjugates_forward; globalMajoranaReflection_conjugates_inverse; globalMajoranaReflection_conjugates_exactSupport; globalMajoranaReflection_conjugates_coexactSupport. These use their stated MP/square-zero assumptions.
- Singular/MoorePenrose.lean: IsMoorePenroseInverse and its four Penrose equations.
- Canonical/PeirceSquareZeroExamples.lean: reciprocalStep_mp; reciprocalStep_ne_star_scaledStep; explicit nonselfadjoint sum example.
- Canonical/GunaydinGurseyTripleProducts.lean: triple_left; triple_right; triple_associator; triple_jacobiator. uStar is a basis label, not canonical conjugation.
- Lie/SplitOctonionNonmultiplicativity.lean: nonmultiplicativity_obstruction; associator_obstruction.

## Handoff

Keep the torus inversion proposal a bounded ring-algebra contract on existing supports and native reflection. Search existing torus/normalizer consumers before adding a theorem; this audit makes no repository-wide novelty claim. Derive inverse and support-swapping laws, do not postulate the intended conclusion. Keep MP and adjoint assumptions distinct. Any concrete specialization must discharge unit/centrality/nondegeneracy assumptions. Independent exact-source AA and serialized kernel QA are required before promotion. Do not infer Möbius topology, analytic dynamics, primitive orders, G₂, or arbitrary-ring classification.

## Owner hashes at artifact creation

- `lean/InfoGeometry/Core/JordanAssociatorRing.lean`: `10e0b1f9b942ab7cbb56f2fdf602cbeb56db9cd15eeec53e03bac6e2912c66c3`
- `lean/InfoGeometry/Core/DiracSuperalgebra.lean`: `a0fba78ffa87e8d4ab1703f936d63631351b9353a8fbe8d8f71e4266434629c3`
- `lean/InfoGeometry/Core/MajoranaSupportSwap.lean`: `eb9ad74ee70c5497091c2aa76c758436bf54545584e16dc16688171c37048738`
- `lean/InfoGeometry/Singular/MoorePenrose.lean`: `0fc09c7636869e801a51e4603e76620e051ac4953068e35d3652953876ae0fd3`
- `lean/InfoGeometry/Canonical/PeirceSquareZeroExamples.lean`: `e6ae853bb5369646aa527a58234f2d8167a315a8e5b909126d980a18a1849eb8`
- `lean/InfoGeometry/Canonical/GunaydinGurseyTripleProducts.lean`: `5e8c00e1553471a759121b1b19a9b43317262377c2f6622ec8baf700c14fc4b5`
- `lean/InfoGeometry/Lie/SplitOctonionNonmultiplicativity.lean`: `7e34a6c2bfeb06c08d9384e3efc134bbc217195f65dee54c5ec0ddc98de76ee9`
