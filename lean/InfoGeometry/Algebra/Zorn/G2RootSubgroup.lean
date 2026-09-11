/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2RootSubgroup

open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open scoped BigOperators

def rootSubgroup (α : G2Root) : Subgroup SplitOctF2Aut where
  carrier := {g | g = (1 : SplitOctF2Aut) ∨ g = rootAut α}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (by rw [ha]; exact hb)
    · exact Or.inr (by simpa [ha, hb])
    · exact Or.inr (by simpa [ha, hb])
    · left
      simpa [ha, hb, rootAut_sq α] using (rootAut_sq α)
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (by rw [ha]; rfl)
    · have h_inv : (rootAut α)⁻¹ = rootAut α := by
        apply mul_left_cancel (a := rootAut α)
        simp [rootAut_sq α]
      exact Or.inr (by simpa [ha, h_inv])

def rootSubgroupConjEquiv (w : SplitOctF2Aut) (α β : G2Root)
    (hw : ∀ a : Bool, w * xRoot α a * w⁻¹ = xRoot β a) :
    rootSubgroup α ≃* rootSubgroup β :=
  { toFun := fun g =>
      ⟨w * g.1 * w⁻¹, by
        rcases g.2 with h | h
        · exact Or.inl (by rw [h]; simp)
        · have h' : w * rootAut α * w⁻¹ = xRoot β true := hw true
          exact Or.inr (by rw [h]; simpa [xRoot] using h')⟩
    invFun := fun g =>
      ⟨w⁻¹ * g.1 * w, by
        rcases g.2 with h | h
        · exact Or.inl (by rw [h]; simp)
        · have h' : w⁻¹ * rootAut β * w = xRoot α true := by
            have h'' := congrArg (fun t => w⁻¹ * t * w) (hw true)
            simpa [xRoot, mul_assoc] using h''.symm
          exact Or.inr (by rw [h]; simpa [xRoot] using h')⟩
    left_inv := by
      intro g
      apply Subtype.ext
      change w⁻¹ * (w * g.1 * w⁻¹) * w = g.1
      simp [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right]
    right_inv := by
      intro g
      apply Subtype.ext
      change w * (w⁻¹ * g.1 * w) * w⁻¹ = g.1
      simp [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right]
    map_mul' := by
      intro a b
      apply Subtype.ext
      change w * (a.1 * b.1) * w⁻¹ =
        (w * a.1 * w⁻¹) * (w * b.1 * w⁻¹)
      simp [mul_assoc] }

def rootSubgroupConjEquiv_of_aut (w : SplitOctF2Aut) (α β : G2Root)
    (h : w * rootAut α * w⁻¹ = rootAut β) :
    rootSubgroup α ≃* rootSubgroup β :=
  rootSubgroupConjEquiv w α β (fun a => by
    cases a
    · simp [xRoot]
    · simpa [xRoot] using h)

def rootSubgroupEquiv_c (α : G2Root) :
    rootSubgroup α ≃* rootSubgroup (cAction α) :=
  rootSubgroupConjEquiv_of_aut c α (cAction α) (c_rootAut_c α)

def rootSubgroupEquiv_c_short_one :
    rootSubgroup (RootLength.Short, (1 : ZMod 6)) ≃*
      rootSubgroup (RootLength.Short, (2 : ZMod 6)) :=
  rootSubgroupEquiv_c (RootLength.Short, (1 : ZMod 6))

end InfoGeometry.Algebra.Zorn.G2RootSubgroup
