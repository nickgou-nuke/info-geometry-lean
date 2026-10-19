/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Clifford.Cl55TKKDirectSumBracket
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
import InfoGeometry.Physics.Cl55FiveGradeDualityBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Generic five-grading interfaces for the concrete Cl(5,5) TKK carrier

This file adapts the existing `EndV` eigenspace grading and modular reversal
to the repository's selected-law `FiveGrading` and `GradeReversal` contracts.
It adds no new bracket-closure, colimit, or physical-identification theorem.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SuperTKK

open scoped DirectSum

open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
open InfoGeometry.Physics.Cl55FiveGradeDualityBridge

local instance : LieRing EndV := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ EndV := LieAlgebra.ofAssociativeAlgebra

private theorem lieBracket_eq_tkkBracket (x y : EndV) :
    ⁅x, y⁆ = tkkBracket x y := LieRing.of_associative_ring_bracket x y

private abbrev TkkFiveGradeNested :=
  Prod (Prod (Prod (Prod (tkkFiveGradeSubmodule 0)
    (tkkFiveGradeSubmodule 1)) (tkkFiveGradeSubmodule 2))
    (tkkFiveGradeSubmodule 3)) (tkkFiveGradeSubmodule 4)

private def tkkFiveGradePiToNested :
    (∀ i : Fin 5, tkkFiveGradeSubmodule i) ≃ₗ[ℝ] TkkFiveGradeNested where
  toFun f := ((((f 0, f 1), f 2), f 3), f 4)
  invFun p := fun i =>
    Fin.cases p.1.1.1.1 (fun i =>
      Fin.cases p.1.1.1.2 (fun i =>
        Fin.cases p.1.1.2 (fun i =>
          Fin.cases p.1.2 (fun i =>
            Fin.cases p.2 (fun i => Fin.elim0 i) i) i) i) i) i
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨⟨⟨x0, x1⟩, x2⟩, x3⟩, x4⟩
    rfl
  map_add' f g := by rfl
  map_smul' c f := by rfl

private def tkkFiveGradeCoordinateEquiv : EndV ≃ₗ[ℝ] TkkFiveGradeNested :=
  (tkkFiveGradeDirectSumEquiv.symm.trans
    (DirectSum.linearEquivFunOnFintype ℝ (Fin 5)
      TkkFiveGradeCarrier)).trans tkkFiveGradePiToNested

private theorem tkkFiveGradeSubmodule_eq_grade (i : Fin 5) :
    tkkFiveGradeSubmodule i = tkkGrade (tkkFiveGradeValue i) := by
  ext X
  simp only [tkkFiveGradeSubmodule, tkkGrade, Module.End.mem_eigenspace_iff]
  rfl

private theorem modular_maps_grade_three_to_one {x : EndV}
    (hx : x ∈ tkkFiveGradeSubmodule 3) :
    idealModularConjugationAction x ∈ tkkFiveGradeSubmodule 1 := by
  have hx' : x ∈ tkkGrade 1 := by
    simpa [tkkFiveGradeSubmodule, tkkFiveGradeValue, tkkGrade, tkkAdjoint] using hx
  have h := idealModularConjugationAction_maps_grade_neg 1 hx'
  simpa [tkkFiveGradeSubmodule, tkkFiveGradeValue, tkkGrade, tkkAdjoint] using h

private theorem modular_maps_grade_one_to_three {x : EndV}
    (hx : x ∈ tkkFiveGradeSubmodule 1) :
    idealModularConjugationAction x ∈ tkkFiveGradeSubmodule 3 := by
  have hx' : x ∈ tkkGrade (-1) := by
    simpa [tkkFiveGradeSubmodule, tkkFiveGradeValue, tkkGrade, tkkAdjoint] using hx
  have h := idealModularConjugationAction_maps_grade_neg (-1) hx'
  simpa [tkkFiveGradeSubmodule, tkkFiveGradeValue, tkkGrade, tkkAdjoint] using h

private theorem modular_maps_grade_four_to_zero {x : EndV}
    (hx : x ∈ tkkFiveGradeSubmodule 4) :
    idealModularConjugationAction x ∈ tkkFiveGradeSubmodule 0 := by
  have hx' : x ∈ tkkGrade 2 := by
    simpa [tkkFiveGradeSubmodule, tkkFiveGradeValue, tkkGrade, tkkAdjoint] using hx
  have h := idealModularConjugationAction_maps_grade_neg 2 hx'
  simpa [tkkFiveGradeSubmodule, tkkFiveGradeValue, tkkGrade, tkkAdjoint] using h

private theorem modular_maps_grade_zero_to_four {x : EndV}
    (hx : x ∈ tkkFiveGradeSubmodule 0) :
    idealModularConjugationAction x ∈ tkkFiveGradeSubmodule 4 := by
  have hx' : x ∈ tkkGrade (-2) := by
    simpa [tkkFiveGradeSubmodule, tkkFiveGradeValue, tkkGrade, tkkAdjoint] using hx
  have h := idealModularConjugationAction_maps_grade_neg (-2) hx'
  simpa [tkkFiveGradeSubmodule, tkkFiveGradeValue, tkkGrade, tkkAdjoint] using h

private theorem modular_maps_grade_two_to_two {x : EndV}
    (hx : x ∈ tkkFiveGradeSubmodule 2) :
    idealModularConjugationAction x ∈ tkkFiveGradeSubmodule 2 := by
  have hx' : x ∈ tkkGrade 0 := by
    simpa [tkkFiveGradeSubmodule, tkkFiveGradeValue, tkkGrade, tkkAdjoint] using hx
  have h := idealModularConjugationAction_maps_grade_neg 0 hx'
  simpa [tkkFiveGradeSubmodule, tkkFiveGradeValue, tkkGrade, tkkAdjoint] using h

/-- The concrete TKK eigenspaces, with the coordinates ordered from grade
`-2` through grade `+2`, form the repository's selected-law five-grading. -/
noncomputable def cl55TkkFiveGrading
    : FiveGrading EndV where
  gNegTwo := tkkFiveGradeSubmodule 0
  gNegOne := tkkFiveGradeSubmodule 1
  gZero := tkkFiveGradeSubmodule 2
  gPosOne := tkkFiveGradeSubmodule 3
  gPosTwo := tkkFiveGradeSubmodule 4
  decomposition := tkkFiveGradeCoordinateEquiv
  decomposition_symm_apply := by
    intro v
    classical
    change DirectSum.coeLinearMap tkkFiveGradeSubmodule
      ((DirectSum.linearEquivFunOnFintype ℝ (Fin 5) TkkFiveGradeCarrier).symm
        (tkkFiveGradePiToNested.symm v)) = _
    rw [DirectSum.coeLinearMap_eq_dfinsuppSum]
    simp [DirectSum.linearEquivFunOnFintype, tkkFiveGradePiToNested,
      Fin.sum_univ_succ]; all_goals abel
  bracket_neg_one_pos_one := by
    intro X Y hX hY
    have h := tkk_bracket_grade_add (i := -1) (j := 1) (k := 0) (by norm_num)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hX)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hY)
    simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue,
      tkkBracket, LieRing.of_associative_ring_bracket] using h
  bracket_zero_zero := by
    intro X Y hX hY
    have h := tkk_bracket_grade_add (i := 0) (j := 0) (k := 0) (by norm_num)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hX)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hY)
    simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue,
      tkkBracket, LieRing.of_associative_ring_bracket] using h
  bracket_pos_one_pos_one := by
    intro X Y hX hY
    have h := tkk_bracket_grade_add (i := 1) (j := 1) (k := 2) (by norm_num)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hX)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hY)
    simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue,
      tkkBracket, LieRing.of_associative_ring_bracket] using h
  bracket_neg_one_neg_one := by
    intro X Y hX hY
    have h := tkk_bracket_grade_add (i := -1) (j := -1) (k := -2) (by norm_num)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hX)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hY)
    simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue,
      tkkBracket, LieRing.of_associative_ring_bracket] using h
  bracket_zero_pos_two := by
    intro X Y hX hY
    have h := tkk_bracket_grade_add (i := 0) (j := 2) (k := 2) (by norm_num)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hX)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hY)
    simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue,
      tkkBracket, LieRing.of_associative_ring_bracket] using h
  bracket_zero_neg_two := by
    intro X Y hX hY
    have h := tkk_bracket_grade_add (i := 0) (j := -2) (k := -2) (by norm_num)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hX)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hY)
    simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue,
      tkkBracket, LieRing.of_associative_ring_bracket] using h
  bracket_pos_two_pos_two_zero := by
    intro X Y hX hY
    have h := tkkBracket_eq_zero_of_grade_sum_outside
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hX)
      (by simpa [tkkFiveGradeSubmodule_eq_grade, tkkFiveGradeValue] using hY)
      (show (2 : ℤ) + 2 < -2 ∨ 2 < (2 : ℤ) + 2 by norm_num)
    simpa [tkkBracket, LieRing.of_associative_ring_bracket] using h

/-- The concrete modular conjugation supplies the generic bracket-compatible
grade reversal for the five eigenspace grading. -/
noncomputable def cl55TkkGradeReversal
    :
    GradeReversal cl55TkkFiveGrading where
  theta := idealModularConjugationAction
  negOne_of_posOne := by
    intro x hx
    exact modular_maps_grade_three_to_one hx
  posOne_of_negOne := by
    intro x hx
    exact modular_maps_grade_one_to_three hx
  negTwo_of_posTwo := by
    intro x hx
    exact modular_maps_grade_four_to_zero hx
  posTwo_of_negTwo := by
    intro x hx
    exact modular_maps_grade_zero_to_four hx
  zero_of_zero := by
    intro x hx
    exact modular_maps_grade_two_to_two hx
  map_bracket := by
    intro x y
    simpa only [lieBracket_eq_tkkBracket] using
      idealModularConjugationAction_preserves_tkkBracket x y

end InfoGeometry.Clifford.Cl55SuperTKK

end
