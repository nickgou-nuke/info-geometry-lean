/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Clifford.Cl55TKKAdjointGradeReversal
import InfoGeometry.Clifford.Cl55TKKGradeDirectSumInternal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Grade reversal on the concrete five-summand TKK decomposition

This module packages the existing grade-reversing modular conjugation as a
map on the external direct sum of the five concrete `EndV` eigenspaces and
proves that reconstruction intertwines this map with the action on `EndV`.
-/

namespace InfoGeometry.Clifford.Cl55SuperTKK

open scoped DirectSum

abbrev TkkFiveGradeCarrier (i : Fin 5) : Type := tkkFiveGradeSubmodule i

abbrev TkkFiveGradeSum : Type := ⨁ i : Fin 5, TkkFiveGradeCarrier i

private theorem tkkFiveGradeSubmodule_eq_grade_public (i : Fin 5) :
    tkkFiveGradeSubmodule i = tkkGrade (tkkFiveGradeValue i) := by
  ext X
  simp only [tkkFiveGradeSubmodule, tkkGrade, Module.End.mem_eigenspace_iff]
  rfl

/-- Reverse the ordered five-grade index: `-2,-1,0,1,2` becomes
`2,1,0,-1,-2`. -/
def tkkFiveGradeReverseIndex (i : Fin 5) : Fin 5 :=
  ⟨4 - i.val, by omega⟩

@[simp]
theorem tkkFiveGradeReverseIndex_involutive (i : Fin 5) :
    tkkFiveGradeReverseIndex (tkkFiveGradeReverseIndex i) = i := by
  apply Fin.ext
  dsimp [tkkFiveGradeReverseIndex]
  omega

theorem tkkFiveGradeValue_reverse (i : Fin 5) :
    tkkFiveGradeValue (tkkFiveGradeReverseIndex i) = -tkkFiveGradeValue i := by
  change ((4 - i.val : ℕ) : ℤ) - 2 = -((i.val : ℤ) - 2)
  omega

/-- The modular conjugation restricted from grade `i` to its reversed grade. -/
noncomputable def tkkFiveGradeComponentReverse (i : Fin 5) :
    tkkFiveGradeSubmodule i →ₗ[ℝ]
      tkkFiveGradeSubmodule (tkkFiveGradeReverseIndex i) where
  toFun x := ⟨idealModularConjugationAction x,
    by
      rw [tkkFiveGradeSubmodule_eq_grade_public]
      rw [tkkFiveGradeValue_reverse]
      exact idealModularConjugationAction_maps_grade_neg
        (tkkFiveGradeValue i)
        (by
          simpa only [tkkFiveGradeSubmodule_eq_grade_public] using x.property)⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add idealModularConjugationAction (x : EndV) (y : EndV)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul idealModularConjugationAction c (x : EndV)

/-- The direct-sum map induced by modular grade reversal. -/
noncomputable def tkkFiveGradeDirectSumReverseAction :
    TkkFiveGradeSum →ₗ[ℝ] TkkFiveGradeSum :=
  tkkFiveGradeDirectSumEquiv.symm.toLinearMap.comp
    (idealModularConjugationAction.comp
      tkkFiveGradeDirectSumEquiv.toLinearMap)

@[simp]
theorem tkkFiveGradeDirectSumReverseAction_lof
    (i : Fin 5) (x : tkkFiveGradeSubmodule i) :
    tkkFiveGradeDirectSumReverseAction
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier i x) =
      DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier
        (tkkFiveGradeReverseIndex i) (tkkFiveGradeComponentReverse i x) :=
  by
    apply tkkFiveGradeDirectSumEquiv.injective
    rw [tkkFiveGradeDirectSumReverseAction]
    simp only [LinearMap.comp_apply]
    change tkkFiveGradeDirectSumEquiv
        (tkkFiveGradeDirectSumEquiv.symm
          (idealModularConjugationAction
            (tkkFiveGradeDirectSumEquiv
              (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier i x)))) =
      tkkFiveGradeDirectSumEquiv
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier
          (tkkFiveGradeReverseIndex i) (tkkFiveGradeComponentReverse i x))
    calc
      _ = idealModularConjugationAction
          (tkkFiveGradeDirectSumEquiv
            (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier i x)) :=
        tkkFiveGradeDirectSumEquiv.apply_symm_apply _
      _ = tkkFiveGradeDirectSumEquiv
            (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier
              (tkkFiveGradeReverseIndex i) (tkkFiveGradeComponentReverse i x)) := by
          change idealModularConjugationAction
              (DirectSum.coeLinearMap tkkFiveGradeSubmodule
                (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier i x)) =
            DirectSum.coeLinearMap tkkFiveGradeSubmodule
              (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier
                (tkkFiveGradeReverseIndex i) (tkkFiveGradeComponentReverse i x))
          rw [DirectSum.coeLinearMap_lof, DirectSum.coeLinearMap_lof]
          rfl

/-- Reconstruction intertwines the induced direct-sum reversal with modular
conjugation on the concrete endomorphism carrier. -/
theorem tkkFiveGradeDirectSumReverseAction_intertwines_reconstruction :
    tkkFiveGradeDirectSumEquiv.toLinearMap.comp
        tkkFiveGradeDirectSumReverseAction =
      idealModularConjugationAction.comp
        tkkFiveGradeDirectSumEquiv.toLinearMap := by
  ext x
  simp [tkkFiveGradeDirectSumReverseAction]

/-- Modular conjugation is involutive on the concrete endomorphism carrier. -/
theorem idealModularConjugationAction_involutive (X : EndV) :
    idealModularConjugationAction
        (idealModularConjugationAction X) = X := by
  change idealModularConjugation *
      (idealModularConjugation * X * idealModularConjugation) *
      idealModularConjugation = X
  calc
    _ = (idealModularConjugation * idealModularConjugation) * X *
        (idealModularConjugation * idealModularConjugation) := by
          noncomm_ring
    _ = X := by rw [idealModularConjugation_sq]; simp

/-- The induced modular grade reversal is an involution on the external
five-summand direct sum. -/
theorem tkkFiveGradeDirectSumReverseAction_involutive :
    Function.Involutive tkkFiveGradeDirectSumReverseAction := by
  intro x
  apply tkkFiveGradeDirectSumEquiv.injective
  simp [tkkFiveGradeDirectSumReverseAction, LinearMap.comp_apply,
    idealModularConjugationAction_involutive]

end InfoGeometry.Clifford.Cl55SuperTKK
