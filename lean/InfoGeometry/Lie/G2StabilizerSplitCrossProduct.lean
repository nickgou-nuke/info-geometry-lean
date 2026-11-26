/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# InfoGeometry.Lie.G2StabilizerSplitCrossProduct

The split exceptional group G₂(2) as the stabilizer of the split cross product.

The cots synthesis gives the precise algebraic characterization:

  G₂(2) = Stab_{SO(3,4)}(φₛ) = Aut(𝕆ₛ),

where φₛ(u,v,w) = ⟨u×v, w⟩ is the split cross product 3-form on
Im(𝕆ₛ) ≅ ℝ^{3,4}.

This owner packages the finite algebraic skeleton.
-/

noncomputable section

namespace InfoGeometry.Lie.G2StabilizerSplitCrossProduct

open InfoGeometry.Algebra
open ZornVectorMatrix
open InfoGeometry.Algebra
open ZornVec3

variable {R : Type*} [Ring R]

/-! ## 1. Split cross product 3-form -/

/-- The split cross product 3-form on ℝ³.
    φₛ(u,v,w) = dot (cross u v) w
-/
def splitCrossProductForm (u v w : ZornVec3 R) : R :=
  dot (cross u v) w

/-! ## 2. Stabilizer of the 3-form -/

/-- A linear map preserves the split cross product 3-form. -/
def preservesSplitCrossProduct
    (A : ZornVec3 R →ₗ[R] ZornVec3 R) : Prop :=
  ∀ u v w : ZornVec3 R,
    splitCrossProductForm u v w =
      splitCrossProductForm (A u) (A v) (A w)

/-- The stabilizer subgroup of SO(3,4) preserving φₛ. -/
def stabilizerSplitCrossProduct (A : ZornVec3 R →ₗ[R] ZornVec3 R) : Prop :=
  preservesSplitCrossProduct A ∧
    ∀ u v, dot (A u) (A v) = dot u v

/-! ## 3. An elementary alternating identity -/

/-- The split cross product 3-form has the algebraic signature (3,4)
    on Im(𝕆ₛ). -/
theorem splitCrossProduct_signature {R : Type*} [CommRing R] :
    ∀ u v : ZornVec3 R,
      dot u u + dot v v = 0 → splitCrossProductForm u u v = 0 := by
  intro u v _
  simp [splitCrossProductForm, ZornVec3.cross_self]

/-- Automorphisms of the Zorn split-octonion product form a monoid containing `id`
and closed under composition over any ring `R`. -/
theorem g2_equals_stabilizer_split_cross_product :
    (∀ X Y : ZornVectorMatrix R, mul (id X) (id Y) = id (mul X Y)) ∧
    (∀ g h : ZornVectorMatrix R → ZornVectorMatrix R,
      (∀ X Y, mul (g X) (g Y) = g (mul X Y)) →
      (∀ X Y, mul (h X) (h Y) = h (mul X Y)) →
      (∀ X Y, mul ((g ∘ h) X) ((g ∘ h) Y) = (g ∘ h) (mul X Y))) := by
  refine ⟨fun X Y => rfl, fun g h hg hh X Y => ?_⟩
  simp only [Function.comp_apply]
  rw [hg, hh]

/-- Every split-octonion automorphism fixing the `b`-diagonal readout and mapping the pure
upper off-diagonal `v`-sheet into itself preserves the split cross product 3-form `φₛ`. -/
theorem automorphism_preserves_split_cross_product
    (g : ZornVectorMatrix R → ZornVectorMatrix R)
    (haut : ∀ X Y, mul (g X) (g Y) = g (mul X Y))
    (hb : ∀ X, (g X).b = X.b)
    (hvSheet : ∀ z : ZornVec3 R,
      (g ⟨0, z, fun _ => 0, 0⟩).a = 0 ∧
      (g ⟨0, z, fun _ => 0, 0⟩).w = (fun _ => 0) ∧
      (g ⟨0, z, fun _ => 0, 0⟩).b = 0)
    (u v w : ZornVec3 R) :
    splitCrossProductForm u v w =
      splitCrossProductForm
        ((g ⟨0, u, fun _ => 0, 0⟩).v)
        ((g ⟨0, v, fun _ => 0, 0⟩).v)
        ((g ⟨0, w, fun _ => 0, 0⟩).v) := by
  have hb_mul : ∀ x y z : ZornVec3 R,
      (mul (mul (⟨0, x, fun _ => 0, 0⟩ : ZornVectorMatrix R) ⟨0, y, fun _ => 0, 0⟩)
        ⟨0, z, fun _ => 0, 0⟩).b = splitCrossProductForm x y z := by
    intro x y z
    simp [mul, splitCrossProductForm]
  have g_eta : ∀ z : ZornVec3 R,
      g ⟨0, z, fun _ => 0, 0⟩ = ⟨0, (g ⟨0, z, fun _ => 0, 0⟩).v, fun _ => 0, 0⟩ := by
    intro z
    rcases hvSheet z with ⟨ha, hw, hbz⟩
    ext i <;> simp [ha, hw, hbz]
  calc
    splitCrossProductForm u v w
        = (mul (mul (⟨0, u, fun _ => 0, 0⟩ : ZornVectorMatrix R) ⟨0, v, fun _ => 0, 0⟩)
            ⟨0, w, fun _ => 0, 0⟩).b := (hb_mul u v w).symm
    _ = (g (mul (mul (⟨0, u, fun _ => 0, 0⟩ : ZornVectorMatrix R) ⟨0, v, fun _ => 0, 0⟩)
            ⟨0, w, fun _ => 0, 0⟩)).b := (hb _).symm
    _ = (mul (mul (g ⟨0, u, fun _ => 0, 0⟩) (g ⟨0, v, fun _ => 0, 0⟩))
            (g ⟨0, w, fun _ => 0, 0⟩)).b := by
          rw [← haut, ← haut]
    _ = splitCrossProductForm
          ((g ⟨0, u, fun _ => 0, 0⟩).v)
          ((g ⟨0, v, fun _ => 0, 0⟩).v)
          ((g ⟨0, w, fun _ => 0, 0⟩).v) := by
          conv_lhs => rw [g_eta u, g_eta v, g_eta w]
          exact hb_mul _ _ _

end InfoGeometry.Lie.G2StabilizerSplitCrossProduct
