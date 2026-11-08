/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import Mathlib.LinearAlgebra.Eigenspace.Basic
import InfoGeometry.Clifford.Cl55TKKGradeDirectSum

/-!
# Internal direct-sum packaging for the concrete Cl(5,5) TKK grades

The eigenspace family already has a spanning decomposition and distinct
eigenvalues. This module exposes those facts through Mathlib's internal
direct-sum interface and its canonical linear equivalence.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace InfoGeometry.Clifford.Cl55SuperTKK

open scoped DirectSum

private theorem tkkFiveGradeSubmodule_eq_grade (i : Fin 5) :
    tkkFiveGradeSubmodule i = tkkGrade (tkkFiveGradeValue i) := by
  ext X
  simp only [tkkFiveGradeSubmodule, tkkGrade, Module.End.mem_eigenspace_iff]
  rfl

/-- The five concrete TKK grade submodules form an internal direct sum of
the endomorphism space of the vacuum ideal. -/
theorem tkkFiveGrade_directSum_isInternal :
    DirectSum.IsInternal tkkFiveGradeSubmodule := by
  have hIndependent : iSupIndep tkkFiveGradeSubmodule := by
    apply (iSupIndep_iff_finsetSum_eq_imp_eq
      (R := ℝ) (N := EndV) tkkFiveGradeSubmodule).2
    intro s v w hvw hsum i hi
    classical
    let X : Fin 5 → EndV := fun j => if j ∈ s then v j else 0
    let Y : Fin 5 → EndV := fun j => if j ∈ s then w j else 0
    have hgrade0 : tkkFiveGradeSubmodule 0 = tkkGrade (-2) := by
      simpa [tkkFiveGradeValue] using
        (tkkFiveGradeSubmodule_eq_grade (0 : Fin 5))
    have hgrade1 : tkkFiveGradeSubmodule 1 = tkkGrade (-1) := by
      simpa [tkkFiveGradeValue] using
        (tkkFiveGradeSubmodule_eq_grade (1 : Fin 5))
    have hgrade2 : tkkFiveGradeSubmodule 2 = tkkGrade 0 := by
      simpa [tkkFiveGradeValue] using
        (tkkFiveGradeSubmodule_eq_grade (2 : Fin 5))
    have hgrade3 : tkkFiveGradeSubmodule 3 = tkkGrade 1 := by
      simpa [tkkFiveGradeValue] using
        (tkkFiveGradeSubmodule_eq_grade (3 : Fin 5))
    have hgrade4 : tkkFiveGradeSubmodule 4 = tkkGrade 2 := by
      simpa [tkkFiveGradeValue] using
        (tkkFiveGradeSubmodule_eq_grade (4 : Fin 5))
    have hXmem (j : Fin 5) : X j ∈ tkkFiveGradeSubmodule j := by
      by_cases hj : j ∈ s
      · simpa [X, hj] using (hvw j hj).1
      · simp [X, hj]
    have hYmem (j : Fin 5) : Y j ∈ tkkFiveGradeSubmodule j := by
      by_cases hj : j ∈ s
      · simpa [Y, hj] using (hvw j hj).2
      · simp [Y, hj]
    have hXgrades : X 0 ∈ tkkGrade (-2) ∧ X 1 ∈ tkkGrade (-1) ∧
        X 2 ∈ tkkGrade 0 ∧ X 3 ∈ tkkGrade 1 ∧ X 4 ∈ tkkGrade 2 := by
      rw [← hgrade0, ← hgrade1, ← hgrade2, ← hgrade3, ← hgrade4]
      exact ⟨hXmem 0, hXmem 1, hXmem 2, hXmem 3, hXmem 4⟩
    have hYgrades : Y 0 ∈ tkkGrade (-2) ∧ Y 1 ∈ tkkGrade (-1) ∧
        Y 2 ∈ tkkGrade 0 ∧ Y 3 ∈ tkkGrade 1 ∧ Y 4 ∈ tkkGrade 2 := by
      rw [← hgrade0, ← hgrade1, ← hgrade2, ← hgrade3, ← hgrade4]
      exact ⟨hYmem 0, hYmem 1, hYmem 2, hYmem 3, hYmem 4⟩
    have hXsum : (∑ j : Fin 5, X j) = ∑ j ∈ s, v j := by
      simp [X, Finset.sum_ite_mem]
    have hYsum : (∑ j : Fin 5, Y j) = ∑ j ∈ s, w j := by
      simp [Y, Finset.sum_ite_mem]
    have hsumFive : X 0 + X 1 + X 2 + X 3 + X 4 =
        Y 0 + Y 1 + Y 2 + Y 3 + Y 4 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hXsum.trans (hsum.trans hYsum.symm)
    have hparts := tkkFiveGrade_sum_injective
      (X 0) (X 1) (X 2) (X 3) (X 4)
      (Y 0) (Y 1) (Y 2) (Y 3) (Y 4)
      hXgrades.1 hXgrades.2.1 hXgrades.2.2.1 hXgrades.2.2.2.1 hXgrades.2.2.2.2
      hYgrades.1 hYgrades.2.1 hYgrades.2.2.1 hYgrades.2.2.2.1 hYgrades.2.2.2.2
      hsumFive
    rcases hparts with ⟨h0, h1, h2, h3, h4⟩
    fin_cases i <;> simp_all [X, Y]
  have hSpanning : iSup tkkFiveGradeSubmodule = ⊤ := by
    apply le_antisymm
    · exact le_top
    · intro X _
      obtain ⟨xNeg2, xNeg1, x0, x1, x2,
        hxNeg2, hxNeg1, hx0, hx1, hx2, hX⟩ :=
          tkkFiveGrade_decomposition X
      rw [hX]
      have hNeg2 : xNeg2 ∈ iSup tkkFiveGradeSubmodule := by
        apply le_iSup tkkFiveGradeSubmodule 0
        rw [tkkFiveGradeSubmodule_eq_grade]
        exact hxNeg2
      have hNeg1 : xNeg1 ∈ iSup tkkFiveGradeSubmodule := by
        apply le_iSup tkkFiveGradeSubmodule 1
        rw [tkkFiveGradeSubmodule_eq_grade]
        exact hxNeg1
      have h0 : x0 ∈ iSup tkkFiveGradeSubmodule := by
        apply le_iSup tkkFiveGradeSubmodule 2
        rw [tkkFiveGradeSubmodule_eq_grade]
        exact hx0
      have h1 : x1 ∈ iSup tkkFiveGradeSubmodule := by
        apply le_iSup tkkFiveGradeSubmodule 3
        rw [tkkFiveGradeSubmodule_eq_grade]
        exact hx1
      have h2 : x2 ∈ iSup tkkFiveGradeSubmodule := by
        apply le_iSup tkkFiveGradeSubmodule 4
        rw [tkkFiveGradeSubmodule_eq_grade]
        exact hx2
      exact add_mem (add_mem (add_mem (add_mem hNeg2 hNeg1) h0) h1) h2
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
    (R := ℝ) (ι := Fin 5) (M := EndV) tkkFiveGradeSubmodule).2
      ⟨hIndependent, hSpanning⟩

/-- The canonical linear equivalence from the external direct sum of the five
TKK grade submodules to the full endomorphism space. -/
noncomputable def tkkFiveGradeDirectSumEquiv :
    (⨁ i : Fin 5, tkkFiveGradeSubmodule i) ≃ₗ[ℝ] EndV :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap tkkFiveGradeSubmodule)
    tkkFiveGrade_directSum_isInternal

end InfoGeometry.Clifford.Cl55SuperTKK
