/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.WittPureSpinorVacuum
import InfoGeometry.Clifford.ChevalleyPureSpinor

open InfoGeometry.Canonical.PureSpinor
#print axioms creationAction_vacuum_eq_zero_iff
#print axioms vacuum_annihilator_eq_bot
#print axioms vacuum_annihilator_rank_lt
#print axioms vacuum_creation_rank_ne
#print axioms InfoGeometry.Clifford.scalarVacuum_isPureSpinor

example : Module.finrank ℝ (Fin 5 → ℝ) = 5 := by simp

example : Module.finrank ℝ
    (sheetAnnihilator (1 : ExteriorAlgebra ℝ (Fin 5 → ℝ))) < 5 := by
  simpa using vacuum_annihilator_rank_lt
    (R := ℝ) (W := Fin 5 → ℝ) (by simp)

example : InfoGeometry.Clifford.IsPureSpinor
    (1 : InfoGeometry.Clifford.SpinorSpace (Fin 5 → ℝ)) :=
  InfoGeometry.Clifford.scalarVacuum_isPureSpinor
