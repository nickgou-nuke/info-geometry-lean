/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge
import InfoGeometry.Core.TripotentEigenspaces

/-!
# BdG interaction anomaly in a tripotent five-grade decomposition

The squared BdG interaction defect is the Peirce commutator already identified
by `PeirceBdGOperatorBridge`. This adapter applies the existing tripotent
projector decomposition to that matrix-valued defect. It requires a tripotent
on the same matrix carrier; it does not identify an arbitrary Zorn tripotent
with the BdG grading or assert that the defect lies in a particular nonzero
grade.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge

open InfoGeometry.Physics
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.Physics.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A]

/-- If the supplied tripotent acts nontrivially by commutator on the Peirce
interaction defect in the massive BdG square, then that defect has a nonzero
component in at least one nonzero grade of this tripotent grading. A nonzero
defect alone does not imply this hypothesis: it may commute with `t`. -/
theorem massiveBdG_anomaly_has_nonzero_fiveGrade_component
    (t : BdGBlock A) (ht : t * t * t = t) (D M : A) :
    (LieAlgebra.ad ℝ (BdGBlock A) t
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
          (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
          (!![D, 0; 0, D]))
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ
          (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
          (!![0, M; 0, 0]) (!![0, 0; M, 0]))) ≠ 0) →
    ∃ k : FiveGrade, k ≠ .zero ∧
      fiveGradeProjector t k
        (massiveBdGHamiltonian D M * massiveBdGHamiltonian D M -
          (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
              (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
              (!![D, 0; 0, D]) *
            InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
              (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
              (!![D, 0; 0, D]) +
            InfoGeometry.OperatorAlgebra.PeirceSpine.genV
              (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
              (!![0, M; 0, 0]) (!![0, 0; M, 0]))) ≠ 0 := by
  let defect : BdGBlock A := massiveBdGHamiltonian D M * massiveBdGHamiltonian D M -
    (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
        (!![D, 0; 0, D]) *
      InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
        (!![D, 0; 0, D]) +
      InfoGeometry.OperatorAlgebra.PeirceSpine.genV
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
        (!![0, M; 0, 0]) (!![0, 0; M, 0]))
  have hDefect : defect = InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
        (!![D, 0; 0, D]))
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
        (!![0, M; 0, 0]) (!![0, 0; M, 0])) := by
    dsimp [defect]
    rw [massiveBdG_square_is_Peirce_tetraktys_expansion]
    noncomm_ring
  intro hAdAnomaly
  have hAdDefect : LieAlgebra.ad ℝ (BdGBlock A) t defect ≠ 0 := by
    rw [hDefect]
    exact hAdAnomaly
  have hgraded := exists_nonzero_nonzero_grade_component_of_ad_ne_zero
    (t := t) (x := defect) ht hAdDefect
  rcases hgraded with ⟨k, hk, hcomponent⟩
  exact ⟨k, hk, by simpa [defect] using hcomponent⟩

/-- For the canonical BdG chiral grading, a nonzero kinetic--mass
commutator forces the massive-square defect into at least one nonzero
five-grade component.  The tripotent is the actual matrix
`Physics.chiralGrading`; no external grading element is supplied. -/
theorem massiveBdG_chiral_commutator_generates_fiveGrade_component
    (D M : A) (hDM : D * M ≠ M * D) :
    ∃ k : FiveGrade, k ≠ .zero ∧
      fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) k
        (InfoGeometry.Physics.massiveBdGHamiltonian D M *
            InfoGeometry.Physics.massiveBdGHamiltonian D M -
          (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
              (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
              (!![D, 0; 0, D]) *
            InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
              (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
              (!![D, 0; 0, D]) +
            InfoGeometry.OperatorAlgebra.PeirceSpine.genV
              (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
              (!![0, M; 0, 0]) (!![0, 0; M, 0]))) ≠ 0 := by
  have ht : InfoGeometry.Physics.chiralGrading (A := A) *
      InfoGeometry.Physics.chiralGrading (A := A) *
      InfoGeometry.Physics.chiralGrading (A := A) =
        InfoGeometry.Physics.chiralGrading (A := A) := by
    calc
      InfoGeometry.Physics.chiralGrading (A := A) *
          InfoGeometry.Physics.chiralGrading (A := A) *
          InfoGeometry.Physics.chiralGrading (A := A) =
          (InfoGeometry.Physics.chiralGrading (A := A) *
            InfoGeometry.Physics.chiralGrading (A := A)) *
            InfoGeometry.Physics.chiralGrading (A := A) := by rw [mul_assoc]
      _ = 1 * InfoGeometry.Physics.chiralGrading (A := A) := by
        rw [InfoGeometry.Physics.chiralGrading_sq]
      _ = InfoGeometry.Physics.chiralGrading (A := A) := one_mul _
  have hAd : LieAlgebra.ad ℝ (BdGBlock A) (InfoGeometry.Physics.chiralGrading (A := A))
      (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) ≠ 0 := by
    change InfoGeometry.Physics.chiralGrading (A := A) *
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M -
      InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M *
        InfoGeometry.Physics.chiralGrading (A := A) ≠ 0
    intro hz
    have h01 := congrArg (fun X : BdGBlock A => X 0 1) hz
    have hdouble : (D * M - M * D) + (D * M - M * D) = 0 := by
      calc
        (D * M - M * D) + (D * M - M * D) =
            (D * M - M * D) - (M * D - D * M) := by noncomm_ring
        _ = 0 := by
          simpa [InfoGeometry.Physics.chiralGrading,
            InfoGeometry.Physics.massiveBdGCommutatorAnomaly] using h01
    have hscalar : (2 : ℝ) • (D * M - M * D) = 0 := by
      simpa [two_smul] using hdouble
    rcases smul_eq_zero.mp hscalar with htwo | hcomm
    · norm_num at htwo
    · exact hDM (sub_eq_zero.mp hcomm)
  have hPeirceAd : LieAlgebra.ad ℝ (BdGBlock A)
      (InfoGeometry.Physics.chiralGrading (A := A))
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
          (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
          (!![D, 0; 0, D]))
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ
          (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := A))
          (!![0, M; 0, 0]) (!![0, 0; M, 0]))) ≠ 0 := by
    rw [massiveBdG_peirce_commutator_eq_andreev_anomaly]
    exact hAd
  exact massiveBdG_anomaly_has_nonzero_fiveGrade_component
    (InfoGeometry.Physics.chiralGrading (A := A)) ht D M hPeirceAd

omit [StarRing A] in
/-- The canonical BdG grading resolves the interaction anomaly exactly into
grades `+2` and `-2`; its grade `-1`, `0`, and `+1` components vanish. -/
theorem massiveBdG_chiral_anomaly_exact_fiveGrade_components (D M : A) :
    fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .posTwo
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) =
      !![0, D * M - M * D; 0, 0] ∧
    fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .negTwo
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) =
      !![0, 0; M * D - D * M, 0] ∧
    fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .negOne
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) = 0 ∧
    fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .zero
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) = 0 ∧
    fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .posOne
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) = 0 := by
  let t := InfoGeometry.Physics.chiralGrading (A := A)
  let up : BdGBlock A := !![0, D * M - M * D; 0, 0]
  let down : BdGBlock A := !![0, 0; M * D - D * M, 0]
  have ht : t * t * t = t := by
    dsimp [t]
    calc
      (InfoGeometry.Physics.chiralGrading (A := A) *
          InfoGeometry.Physics.chiralGrading (A := A)) *
          InfoGeometry.Physics.chiralGrading (A := A) =
        1 * InfoGeometry.Physics.chiralGrading (A := A) := by
          rw [InfoGeometry.Physics.chiralGrading_sq]
      _ = InfoGeometry.Physics.chiralGrading (A := A) := one_mul _
  have hsplit : InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M = up + down := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [up, down, InfoGeometry.Physics.massiveBdGCommutatorAnomaly]
  have hup : LieAlgebra.ad ℝ (BdGBlock A) t up = (2 : ℝ) • up := by
    change t * up - up * t = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [t, up, InfoGeometry.Physics.chiralGrading, Matrix.mul_apply,
        Fin.sum_univ_two, two_smul] <;> noncomm_ring
  have hdown : LieAlgebra.ad ℝ (BdGBlock A) t down = (-2 : ℝ) • down := by
    change t * down - down * t = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [t, down, InfoGeometry.Physics.chiralGrading, Matrix.mul_apply,
        Fin.sum_univ_two, two_smul] <;> noncomm_ring
  have hUpMem : up ∈ fiveGradeRange t .posTwo := by
    rw [fiveGradeRange_eq_eigenspace ht .posTwo]
    apply Module.End.mem_eigenspace_iff.mpr
    simpa [fiveGradeValue] using hup
  have hDownMem : down ∈ fiveGradeRange t .negTwo := by
    rw [fiveGradeRange_eq_eigenspace ht .negTwo]
    apply Module.End.mem_eigenspace_iff.mpr
    simpa [fiveGradeValue] using hdown
  have hUpFixed := (mem_fiveGradeRange_iff_projector_fixed ht .posTwo).mp hUpMem
  have hDownFixed := (mem_fiveGradeRange_iff_projector_fixed ht .negTwo).mp hDownMem
  have hUpZero (k : FiveGrade) (hk : k ≠ .posTwo) :
      fiveGradeProjector t k up = 0 :=
    fiveGradeProjector_eq_zero_of_eigen_ne ht hup k (by
      intro h
      cases k with
      | negTwo => norm_num [fiveGradeValue] at h
      | negOne => norm_num [fiveGradeValue] at h
      | zero => norm_num [fiveGradeValue] at h
      | posOne => norm_num [fiveGradeValue] at h
      | posTwo => exact (hk rfl).elim)
  have hDownZero (k : FiveGrade) (hk : k ≠ .negTwo) :
      fiveGradeProjector t k down = 0 :=
    fiveGradeProjector_eq_zero_of_eigen_ne ht hdown k (by
      intro h
      cases k with
      | negTwo => exact (hk rfl).elim
      | negOne => norm_num [fiveGradeValue] at h
      | zero => norm_num [fiveGradeValue] at h
      | posOne => norm_num [fiveGradeValue] at h
      | posTwo => norm_num [fiveGradeValue] at h)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hsplit, map_add, hUpFixed, hDownZero .posTwo (by decide)]
    simp [up]
  · rw [hsplit, map_add, hUpZero .negTwo (by decide), hDownFixed]
    simp [down]
  · rw [hsplit, map_add, hUpZero .negOne (by decide), hDownZero .negOne (by decide)]
    exact add_zero _
  · rw [hsplit, map_add, hUpZero .zero (by decide), hDownZero .zero (by decide)]
    exact add_zero _
  · rw [hsplit, map_add, hUpZero .posOne (by decide), hDownZero .posOne (by decide)]
    exact add_zero _

omit [StarRing A] in
/-- A nonzero kinetic--mass commutator occupies both extreme BdG grades; the
two off-diagonal blocks are the paired `+2` and `-2` components. -/
theorem massiveBdG_noncommutation_has_both_extreme_grades
    (D M : A) :
    (fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .posTwo
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) ≠ 0 ∧
      fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .negTwo
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) ≠ 0) ↔
      D * M ≠ M * D := by
  rcases massiveBdG_chiral_anomaly_exact_fiveGrade_components D M with
    ⟨hPos, hNeg, _, _, _⟩
  constructor
  · rintro ⟨hPosNe, _⟩ hDM
    apply hPosNe
    rw [hPos]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hDM]
  · intro hDM
    constructor
    · rw [hPos]
      intro hz
      have h := congrArg (fun X : BdGBlock A => X 0 1) hz
      exact hDM (sub_eq_zero.mp (by simpa using h))
    · rw [hNeg]
      intro hz
      have h := congrArg (fun X : BdGBlock A => X 1 0) hz
      apply hDM
      have heq : M * D - D * M = 0 := by simpa using h
      exact (sub_eq_zero.mp heq).symm

/-- Reversal of a five-grade label. -/
private def andreevReversedGrade : FiveGrade → FiveGrade
  | .negTwo => .posTwo
  | .negOne => .posOne
  | .zero => .zero
  | .posOne => .negOne
  | .posTwo => .negTwo

/-- Conjugation by the particle-hole swap exchanges the two extreme
five-grade projectors of the canonical BdG chiral grading. The intermediate
grades are zero for this grading, and are exchanged with each other. -/
theorem andreev_conjugation_intertwines_chiral_fiveGradeProjector
    (X : BdGBlock A) (k : FiveGrade) :
    andreevSwap * fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) k X * andreevSwap =
      fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A))
        (andreevReversedGrade k) (andreevSwap * X * andreevSwap) := by
  cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [andreevReversedGrade, fiveGradeProjector,
      InfoGeometry.Physics.chiralGrading, InfoGeometry.Physics.andreevSwap,
      InfoGeometry.Physics.Algebra.gradeNegTwoProjector,
      InfoGeometry.Physics.Algebra.gradeNegOneProjector,
      InfoGeometry.Physics.Algebra.gradeZeroProjector,
      InfoGeometry.Physics.Algebra.gradePosOneProjector,
      InfoGeometry.Physics.Algebra.gradePosTwoProjector,
      InfoGeometry.Physics.Algebra.jointPeirceProjector,
      InfoGeometry.Physics.Algebra.peirceLeft,
      InfoGeometry.Physics.Algebra.peirceRight,
      InfoGeometry.Physics.Algebra.peirceProjector,
      InfoGeometry.Physics.Algebra.projPos,
      InfoGeometry.Physics.Algebra.projNeg,
      InfoGeometry.Physics.Algebra.projZero,
      InfoGeometry.Physics.Algebra.leftMulLinear_apply,
      InfoGeometry.Physics.Algebra.rightMulLinear_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.sub_apply, Matrix.vecMul, dotProduct] <;>
    norm_num <;> noncomm_ring

omit [StarRing A] in
/-- The two nonzero components of the BdG interaction anomaly are carried to
one another by Andreev reflection, with the sign forced by the commutator. -/
theorem andreev_reflect_chiral_anomaly_grade_components (D M : A) :
    andreevSwap *
        fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .posTwo
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) * andreevSwap =
      -fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .negTwo
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) ∧
    andreevSwap *
        fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .negTwo
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) * andreevSwap =
      -fiveGradeProjector (InfoGeometry.Physics.chiralGrading (A := A)) .posTwo
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M) := by
  rcases massiveBdG_chiral_anomaly_exact_fiveGrade_components D M with
    ⟨hPos, hNeg, _, _, _⟩
  constructor
  · rw [hPos, hNeg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Physics.andreevSwap, Matrix.mul_apply,
        Fin.sum_univ_two]
  · rw [hNeg, hPos]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Physics.andreevSwap, Matrix.mul_apply,
        Fin.sum_univ_two]

end InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge
