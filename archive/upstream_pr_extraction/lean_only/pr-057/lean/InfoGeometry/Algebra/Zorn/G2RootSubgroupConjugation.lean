/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2TwoRootSystem

/-!
# Root subgroup conjugation and the Weyl-equivariant bridge

This file establishes the precise mechanism by which a Weyl element `w`
conjugates one root subgroup onto another:

    w X_α w⁻¹ = X_{cAction α}

This is the canonical Chevalley relation. Over `𝔽₂`, each root subgroup
`X_α = {1, x_α(1)} ≅ ℤ₂` is minimal elementary abelian.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootSubgroupConjugation

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem

/-- The root subgroup `X_α` as a two-element subgroup of `SplitOctF2Aut`.
    Over `𝔽₂`, this is `{1, x_α(1)} ≅ ℤ₂`. -/
noncomputable def rootSubgroup (α : G2Root) : Subgroup SplitOctF2Aut where
  carrier := { g | g = 1 ∨ g = rootAut α }
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (mul_one 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · left; exact rootAut_sq α
  inv_mem' := by
    rintro g (rfl | rfl)
    · exact Or.inl (inv_one)
    · right
      show (rootAut α)⁻¹ = rootAut α
      -- If a*a = 1, then a⁻¹ = a
      exact inv_eq_of_mul_eq_one_left (rootAut_sq α)

/-- The generator of the root subgroup `X_α`. -/
noncomputable def rootGenerator (α : G2Root) : SplitOctF2Aut :=
  rootAut α

theorem rootGenerator_mem_rootSubgroup (α : G2Root) :
    rootGenerator α ∈ rootSubgroup α := by
  simp [rootGenerator, rootSubgroup]

/-- Conjugation by the Coxeter element `c` sends generators of `X_α`
    to generators of `X_{cAction α}`. -/
theorem c_conj_rootGenerator (α : G2Root) :
    c * rootGenerator α * c⁻¹ = rootGenerator (cAction α) := by
  simp [rootGenerator, c_rootAut_c]

/-- Conjugation by `c⁻¹` sends generators of `X_{cAction α}`
    to generators of `X_α`. -/
theorem c_inv_conj_rootGenerator (α : G2Root) :
    c⁻¹ * rootGenerator (cAction α) * c = rootGenerator α := by
  simp [rootGenerator]
  -- From c_rootAut_c: c * rootAut α * c⁻¹ = rootAut (cAction α)
  -- Multiply on left by c⁻¹ and right by c to get the inverse
  have h := c_rootAut_c α
  calc c⁻¹ * rootAut (cAction α) * c = c⁻¹ * (c * rootAut α * c⁻¹) * c := by rw [h]
  _ = rootAut α := by group

/-- Canonical isomorphism between root subgroups induced by conjugation with `c`. -/
noncomputable def rootSubgroupConjEquiv (α : G2Root) :
    rootSubgroup α ≃* rootSubgroup (cAction α) where
  toFun g := ⟨c * g.val * c⁻¹, by
    cases g.property with
    | inl hl =>
      rw [hl]
      left; simp
    | inr hr =>
      rw [hr]
      right; exact c_conj_rootGenerator α⟩
  invFun h := ⟨c⁻¹ * h.val * c, by
    cases h.property with
    | inl hl =>
      rw [hl]
      left; simp
    | inr hr =>
      rw [hr]
      right; exact c_inv_conj_rootGenerator α⟩
  left_inv g := by ext; simp; group
  right_inv h := by ext; simp; group
  map_mul' x y := by ext; simp [mul_assoc]; group

end InfoGeometry.Algebra.Zorn.G2RootSubgroupConjugation
