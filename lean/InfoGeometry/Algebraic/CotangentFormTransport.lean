/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebraic.CotangentBilinearGraph
import InfoGeometry.Twistor.RealDualTwistor
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Algebraic transport of the cotangent bilinear form

The carrier is the existing `V × Module.Dual ℝ V`. The lift is the existing
`RealDualTwistor.frameAction`, so no second cotangent lift is introduced.
The form is nondegenerate on the whole carrier; a fixed-subspace restriction
requires a separate nondegeneracy argument. These are linear-algebra statements,
without a smooth cotangent bundle or a differential-form closedness theorem.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CotangentFormTransport

open CotangentBilinearGraph InfoGeometry.Twistor.RealDualTwistor

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Inverse dual transport preserves the evaluation terms, leaving only
the explicit covariance hypothesis for the additional bilinear term. -/
theorem cotangentForm_frameAction
    (e : V ≃ₗ[ℝ] W) (B : LinearMap.BilinForm ℝ V)
    (C : LinearMap.BilinForm ℝ W)
    (hBC : ∀ x y, C (e x) (e y) = B x y)
    (v w : Carrier V) :
    cotangentForm C (frameAction e v) (frameAction e w) =
      cotangentForm B v w := by
  simp only [cotangentForm_apply, frameAction_fst, frameAction_snd_apply,
    LinearEquiv.symm_apply_apply, hBC]

/-- The same equality as an equality of native bilinear forms. -/
theorem cotangentForm_pullback_frameAction
    (e : V ≃ₗ[ℝ] W) (B : LinearMap.BilinForm ℝ V)
    (C : LinearMap.BilinForm ℝ W)
    (hBC : ∀ x y, C (e x) (e y) = B x y) :
    (cotangentForm C).compl₁₂ (frameAction e).toLinearMap
      (frameAction e).toLinearMap = cotangentForm B := by
  ext v w
  exact cotangentForm_frameAction e B C hBC v w

/-- Adding a bilinear term in the primal arguments preserves nondegeneracy
on the full vector/dual product. Alternation is a separate property of `B`. -/
theorem cotangentForm_nondegenerate (B : LinearMap.BilinForm ℝ V) :
    (cotangentForm B).Nondegenerate := by
  constructor
  · intro v hv
    have hx : v.1 = 0 := by
      apply eq_zero_of_dual_vanishes
      intro φ
      simpa only [cotangentForm_apply, map_zero, LinearMap.zero_apply,
        sub_zero, add_zero] using hv (0, φ)
    apply Prod.ext hx
    ext x
    simpa only [cotangentForm_apply, hx, map_zero, LinearMap.zero_apply,
      zero_sub, zero_add, add_zero, neg_eq_zero] using hv (x, 0)
  · intro v hv
    have hx : v.1 = 0 := by
      apply eq_zero_of_dual_vanishes
      intro φ
      simpa only [cotangentForm_apply, map_zero, LinearMap.zero_apply,
        zero_sub, zero_add, add_zero, neg_eq_zero] using hv (0, φ)
    apply Prod.ext hx
    ext x
    simpa only [cotangentForm_apply, hx, map_zero, LinearMap.zero_apply,
      sub_zero, add_zero] using hv (x, 0)

section LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- The native bilinear form obtained by evaluating the native Lie bracket. -/
def bracketForm (α : Module.Dual ℝ L) : LinearMap.BilinForm ℝ L :=
  (LieAlgebra.ad ℝ L).toLinearMap.compr₂ α

@[simp] theorem bracketForm_apply (α : Module.Dual ℝ L) (x y : L) :
    bracketForm α x y = α ⁅x, y⁆ := rfl

theorem bracketForm_isAlt (α : Module.Dual ℝ L) :
    (bracketForm α).IsAlt := by
  intro x
  simp only [bracketForm_apply, lie_self, map_zero]

/-- Lie-bracket covariance supplies the bilinear transport hypothesis.
The base covector and both tangent covectors use inverse dual transport. -/
theorem cotangentForm_lieEquiv (e : L ≃ₗ⁅ℝ⁆ L)
    (α : Module.Dual ℝ L) (v w : Carrier L) :
    cotangentForm (bracketForm (e.toLinearEquiv.symm.dualMap α))
      (frameAction e.toLinearEquiv v) (frameAction e.toLinearEquiv w) =
        cotangentForm (bracketForm α) v w := by
  apply cotangentForm_frameAction
  intro x y
  change α (e.toLinearEquiv.symm ⁅e x, e y⁆) = α ⁅x, y⁆
  rw [← e.map_lie]
  exact congrArg α (e.toLinearEquiv.symm_apply_apply ⁅x, y⁆)

end LieAlgebra

end InfoGeometry.Algebraic.CotangentFormTransport
