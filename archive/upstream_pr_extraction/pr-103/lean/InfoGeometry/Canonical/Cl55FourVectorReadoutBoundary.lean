import InfoGeometry.Canonical.Cl55WittLieRouting
import InfoGeometry.Geometry.PauliParavectorBridge

/-!
# The `Cl(5,5)` five-grade carrier versus four-vector readouts

The native Witt carrier has genuine grades `-2,-1,0,+1,+2`.  Its positive and
negative one-grade sectors are five-dimensional.  Consequently they are not
the physical four-vector carrier `Fin 4 → ℝ` by a hidden type identification.
Four-vectors must enter through an explicit branching/readout map (or a chosen
four-dimensional subspace).  This file records that boundary and re-exports
the grade-addition facts needed by downstream readouts.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace InfoGeometry.Canonical.Cl55FourVectorReadoutBoundary

open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Geometry.PauliParavectorBridge

theorem creation_grade_plus_one (i : Fin 5) :
    creation i ∈ gradeSubmodule 1 := by
  exact creation_mem_gradeSubmodule i

theorem annihilation_grade_minus_one (i : Fin 5) :
    annihilation i ∈ gradeSubmodule (-1) := by
  exact annihilation_mem_gradeSubmodule i

theorem creation_annihilation_bracket_grade_zero (i j : Fin 5) :
    bracket (creation i) (annihilation j) ∈ gradeSubmodule 0 := by
  have hi : creation i ∈ gradeSubmodule (1 : ℤ) :=
    creation_mem_gradeSubmodule i
  have hj : annihilation j ∈ gradeSubmodule (-1 : ℤ) :=
    annihilation_mem_gradeSubmodule j
  simpa using (gradeSubmodule_bracket_mem (k := (1 : ℤ)) (l := (-1 : ℤ)) hi hj)

theorem creation_creation_bracket_grade_plus_two (i j : Fin 5) :
    bracket (creation i) (creation j) ∈ gradeSubmodule 2 := by
  have hi : creation i ∈ gradeSubmodule (1 : ℤ) :=
    creation_mem_gradeSubmodule i
  have hj : creation j ∈ gradeSubmodule (1 : ℤ) :=
    creation_mem_gradeSubmodule j
  simpa using (gradeSubmodule_bracket_mem (k := (1 : ℤ)) (l := (1 : ℤ)) hi hj)

theorem annihilation_annihilation_bracket_grade_minus_two (i j : Fin 5) :
    bracket (annihilation i) (annihilation j) ∈ gradeSubmodule (-2) := by
  have hi : annihilation i ∈ gradeSubmodule (-1 : ℤ) :=
    annihilation_mem_gradeSubmodule i
  have hj : annihilation j ∈ gradeSubmodule (-1 : ℤ) :=
    annihilation_mem_gradeSubmodule j
  simpa using (gradeSubmodule_bracket_mem (k := (-1 : ℤ)) (l := (-1 : ℤ)) hi hj)

theorem no_linearEquiv_wittPosOne_minkowski4 :
    ¬ Nonempty (wittPosOne ≃ₗ[ℝ] Minkowski4) := by
  intro h
  rcases h with ⟨e⟩
  have hfin := LinearEquiv.finrank_eq e
  rw [wittPosOne_finrank_eq_five] at hfin
  have hfour : Module.finrank ℝ Minkowski4 = 4 := by
    simpa [Minkowski4] using
      (Module.finrank_fintype_fun_eq_card ℝ (η := Fin 4))
  rw [hfour] at hfin
  norm_num at hfin

theorem no_linearEquiv_wittNegOne_minkowski4 :
    ¬ Nonempty (wittNegOne ≃ₗ[ℝ] Minkowski4) := by
  intro h
  rcases h with ⟨e⟩
  have hfin := LinearEquiv.finrank_eq e
  rw [wittNegOne_finrank_eq_five] at hfin
  have hfour : Module.finrank ℝ Minkowski4 = 4 := by
    simpa [Minkowski4] using
      (Module.finrank_fintype_fun_eq_card ℝ (η := Fin 4))
  rw [hfour] at hfin
  norm_num at hfin

end InfoGeometry.Canonical.Cl55FourVectorReadoutBoundary
