/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CartanTrialityFirstCoordinate
import InfoGeometry.Algebraic.CotangentFormTransport
import InfoGeometry.Algebraic.OrderThreeFixedForm

/-!
# The explicit triality cycle and its fixed cotangent form

The actual four-dimensional first-coordinate cycle is a real linear
equivalence with inverse its square. Its existing contragredient cotangent
lift has cube one. The native canonical alternating form therefore restricts
nondegenerately to the lift's fixed submodule.

This connects the matrix and bilinear parts of the intake by an explicit
map. It does not identify this eight-dimensional linear carrier with a
smooth cotangent groupoid or construct an outer Lie-group automorphism.
-/

noncomputable section

namespace InfoGeometry.Lie.CartanTrialityCotangentFixedForm

open Matrix CartanTrialityFirstCoordinate
open InfoGeometry.Algebraic.CotangentBilinearGraph
open InfoGeometry.Algebraic.CotangentFormTransport
open InfoGeometry.Algebraic.OrderThreeFixedForm
open InfoGeometry.Twistor.RealDualTwistor

/-- The given cycle acts on the real four-vector carrier, with its square as
the inverse. No scalar or commuting replacement is used. -/
def cycleEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun := firstCoordinateCycle.mulVec
  invFun := (firstCoordinateCycle ^ 2).mulVec
  left_inv v := by
    rw [Matrix.mulVec_mulVec, ← pow_succ, firstCoordinateCycle_pow_three,
      Matrix.one_mulVec]
  right_inv v := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', firstCoordinateCycle_pow_three,
      Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _

@[simp] theorem cycleEquiv_apply (v : Fin 4 → ℝ) :
    cycleEquiv v = firstCoordinateCycle.mulVec v := rfl

theorem cycleEquiv_three_apply (v : Fin 4 → ℝ) :
    cycleEquiv (cycleEquiv (cycleEquiv v)) = v := by
  change firstCoordinateCycle.mulVec
    (firstCoordinateCycle.mulVec (firstCoordinateCycle.mulVec v)) = v
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_three',
    firstCoordinateCycle_pow_three, Matrix.one_mulVec]

private theorem cycleEquiv_symm_three_apply (v : Fin 4 → ℝ) :
    cycleEquiv.symm (cycleEquiv.symm (cycleEquiv.symm v)) = v := by
  have h := cycleEquiv_three_apply
    (cycleEquiv.symm (cycleEquiv.symm (cycleEquiv.symm v)))
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The contragredient lift has order dividing three on the genuine
vector/dual product. -/
theorem cotangentCycle_pow_three :
    (frameAction cycleEquiv).toLinearMap ^ 3 =
      (1 : Module.End ℝ (Carrier (Fin 4 → ℝ))) := by
  apply LinearMap.ext
  intro p
  simp only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply]
  apply Prod.ext
  · exact cycleEquiv_three_apply p.1
  · apply LinearMap.ext
    intro x
    change p.2 (cycleEquiv.symm (cycleEquiv.symm (cycleEquiv.symm x))) = p.2 x
    rw [cycleEquiv_symm_three_apply]

/-- The actual cycle supplies the finite-order hypothesis needed for the
nondegenerate fixed restriction. -/
theorem fixedCotangentForm_nondegenerate :
    ((cotangentForm (0 : LinearMap.BilinForm ℝ (Fin 4 → ℝ))).restrict
      (frameAction cycleEquiv).toLinearMap.fixedSubmodule).Nondegenerate := by
  apply nondegenerate_restrict_fixedSubmodule
    (cotangentForm (0 : LinearMap.BilinForm ℝ (Fin 4 → ℝ)))
    (cotangentForm_nondegenerate _) (frameAction cycleEquiv).toLinearMap
    cotangentCycle_pow_three
  intro p q
  apply cotangentForm_frameAction
  intro x y
  rfl

theorem fixedCotangentForm_isAlt :
    ((cotangentForm (0 : LinearMap.BilinForm ℝ (Fin 4 → ℝ))).restrict
      (frameAction cycleEquiv).toLinearMap.fixedSubmodule).IsAlt := by
  apply isAlt_restrict_fixedSubmodule
  apply cotangentForm_isAlt
  exact LinearMap.BilinForm.isAlt_zero

end InfoGeometry.Lie.CartanTrialityCotangentFixedForm
