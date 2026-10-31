/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2RootSubgroup

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

/-- Compatibility name for the canonical two-element root subgroup. The
carrier and subgroup laws are owned by `G2RootSubgroup.rootSubgroup`; this
module only adds its Coxeter-conjugation API. -/
abbrev rootSubgroup (α : G2Root) : Subgroup SplitOctF2Aut :=
  InfoGeometry.Algebra.Zorn.G2RootSubgroup.rootSubgroup α

/-- The generator of the root subgroup `X_α`. -/
noncomputable def rootGenerator (α : G2Root) : SplitOctF2Aut :=
  rootAut α

theorem rootGenerator_mem_rootSubgroup (α : G2Root) :
    rootGenerator α ∈ rootSubgroup α := by
  change rootAut α ∈ InfoGeometry.Algebra.Zorn.G2RootSubgroup.rootSubgroup α
  change rootAut α = 1 ∨ rootAut α = rootAut α
  exact Or.inr rfl

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
  map_mul' x y := by ext; simp only [Subgroup.coe_mul]; group

end InfoGeometry.Algebra.Zorn.G2RootSubgroupConjugation
