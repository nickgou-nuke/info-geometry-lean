/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Canonical.SouriauContragredientPairing
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Tactic

/-!
# The algebraic left-trivialized cotangent form

On a real Lie algebra and its algebraic dual, the canonical evaluation form
has the bracket correction `α ⁅X, Y⁆`.  This file constructs a native bilinear
form, proves alternation and nondegeneracy, and proves invariance under an
actual Lie algebra equivalence paired with its contragredient.

The evaluation form is reused from `NeutralPhaseSpaceCore`.  These are
fiberwise algebraic statements.  No Lie group, differential of a group
automorphism, closed differential form, or smooth symplectic groupoid is
constructed by this file.
-/

noncomputable section

namespace InfoGeometry.Geometry.CotangentLieForm

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Canonical.SouriauContragredientPairing

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The full paired primal/contragredient lift on the existing phase carrier. -/
def cotangentLift (e : V ≃ₗ[ℝ] V) :
    PhaseSpaceCarrier V ≃ₗ[ℝ] PhaseSpaceCarrier V :=
  e.prodCongr (contragredientLinearEquiv e)

@[simp] theorem cotangentLift_apply (e : V ≃ₗ[ℝ] V) (z : PhaseSpaceCarrier V) :
    cotangentLift e z = (e z.1, contragredient e z.2) := rfl

/-- The lift preserves the existing neutral pairing. -/
theorem cotangentLift_neutral (e : V ≃ₗ[ℝ] V) (z w : PhaseSpaceCarrier V) :
    canonicalNeutralBilin (cotangentLift e z) (cotangentLift e w) =
      canonicalNeutralBilin z w := by
  simp [canonicalNeutralBilin_apply, cotangentLift_apply]

/-- The lift preserves the existing canonical skew form with its stated sign. -/
theorem cotangentLift_omega (e : V ≃ₗ[ℝ] V) (z w : PhaseSpaceCarrier V) :
    neutralOmega (cotangentLift e z) (cotangentLift e w) = neutralOmega z w := by
  simp [neutralOmega_apply, cotangentLift_apply]

end Linear

section Lie

variable {V : Type*} [LieRing V] [LieAlgebra ℝ V]

/-- A covector evaluated on the native Lie bracket is a bilinear form. -/
def bracketForm (α : Module.Dual ℝ V) : LinearMap.BilinForm ℝ V where
  toFun x :=
    { toFun := fun y => α ⁅x, y⁆
      map_add' := by intros; simp [lie_add]
      map_smul' := by intros; simp [lie_smul] }
  map_add' := by intros; ext; simp [add_lie]
  map_smul' := by intros; ext; simp [smul_lie]

@[simp] theorem bracketForm_apply (α : Module.Dual ℝ V) (x y : V) :
    bracketForm α x y = α ⁅x, y⁆ := rfl

/-- The algebraic fiber formula for `-dθ` in left trivialization. -/
def cotangentForm (α : Module.Dual ℝ V) :
    LinearMap.BilinForm ℝ (PhaseSpaceCarrier V) :=
  neutralOmega + (bracketForm α).compl₁₂
    (LinearMap.fst ℝ V (Module.Dual ℝ V))
    (LinearMap.fst ℝ V (Module.Dual ℝ V))

@[simp] theorem cotangentForm_apply (α : Module.Dual ℝ V)
    (z w : PhaseSpaceCarrier V) :
    cotangentForm α z w = w.2 z.1 - z.2 w.1 + α ⁅z.1, w.1⁆ := by
  simp [cotangentForm, neutralOmega_apply]

/-- Native Lie alternation supplies the missing alternating-form hypothesis. -/
theorem cotangentForm_isAlt (α : Module.Dual ℝ V) : (cotangentForm α).IsAlt := by
  intro z
  simp [cotangentForm_apply]

theorem cotangentForm_skew (α : Module.Dual ℝ V) (z w : PhaseSpaceCarrier V) :
    cotangentForm α z w = -cotangentForm α w z := by
  simp only [cotangentForm_apply]
  rw [← lie_skew w.1 z.1, map_neg]
  ring

/-- The bracket correction does not introduce a radical. -/
theorem cotangentForm_nondegenerate (α : Module.Dual ℝ V) :
    (cotangentForm α).Nondegenerate := by
  have hleft : (cotangentForm α).SeparatingLeft := by
    intro z hz
    have hx : z.1 = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ z.1).mp
      intro β
      simpa using hz (0, β)
    have hp : z.2 = 0 := by
      apply LinearMap.ext
      intro y
      have h := hz (y, 0)
      simpa [hx] using h
    exact Prod.ext hx hp
  refine ⟨hleft, ?_⟩
  intro z hz
  apply hleft z
  intro w
  rw [cotangentForm_skew, hz, neg_zero]

/-- Bracket-intertwining and contragredient transport preserve the fiber form. -/
theorem cotangentForm_invariant (e : V ≃ₗ[ℝ] V)
    (he : ∀ x y : V, e ⁅x, y⁆ = ⁅e x, e y⁆)
    (α : Module.Dual ℝ V) (z w : PhaseSpaceCarrier V) :
    cotangentForm (contragredient e α) (cotangentLift e z) (cotangentLift e w) =
      cotangentForm α z w := by
  simp only [cotangentForm_apply, cotangentLift_apply,
    contragredient_pairing_invariant]
  rw [← he, contragredient_pairing_invariant]

/-- In particular a native Lie equivalence supplies the bracket intertwiner. -/
theorem cotangentForm_lieEquiv (e : V ≃ₗ⁅ℝ⁆ V)
    (α : Module.Dual ℝ V) (z w : PhaseSpaceCarrier V) :
    cotangentForm (contragredient e.toLinearEquiv α)
        (cotangentLift e.toLinearEquiv z) (cotangentLift e.toLinearEquiv w) =
      cotangentForm α z w :=
  cotangentForm_invariant e.toLinearEquiv (fun x y => e.map_lie x y) α z w

end Lie

end InfoGeometry.Geometry.CotangentLieForm
