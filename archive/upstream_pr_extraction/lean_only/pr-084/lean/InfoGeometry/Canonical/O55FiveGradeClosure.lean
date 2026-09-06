import InfoGeometry.Clifford.ConformalLieAlgebra55
import Mathlib.Tactic

open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Canonical.ConformalFiveGradeInversion

noncomputable section

namespace InfoGeometry.Canonical.O55FiveGradeClosure

-- Helper anticommutation lemmas
theorem h_v4_v5_anti : v4 * v5 = - (v5 * v4) := by
  have h : v5 * v4 + v4 * v5 = 0 := by rw [v5_v4_anti]; exact neg_add_cancel (v4 * v5)
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

theorem h_u4_v5_anti : u4 * v5 = - (v5 * u4) := by
  have h : v5 * u4 + u4 * v5 = 0 := by rw [v5_u4_anti]; exact neg_add_cancel (u4 * v5)
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

theorem adD5_v5 : D5 * v5 - v5 * D5 = -v5 := by
  dsimp [D5]
  rw [smul_mul_assoc, Algebra.mul_smul_comm, sub_mul, mul_sub]
  have hsub' : u5 * v5 + v5 * u5 = 1 := u5_v5_add_v5_u5
  have hvu5 : v5 * (u5 * v5) = v5 := by
    have hvu5' : u5 * v5 = 1 - v5 * u5 := eq_sub_of_add_eq hsub'
    calc
      v5 * (u5 * v5) = v5 * (1 - v5 * u5) := by rw [hvu5']
      _ = v5 - v5 * (v5 * u5) := by rw [mul_sub]; simp
      _ = v5 - (v5 * v5) * u5 := by rw [← mul_assoc]
      _ = v5 - 0 := by rw [v5_sq]; simp
      _ = v5 := by simp
  have huvv : u5 * v5 * v5 = 0 := by
    calc
      u5 * v5 * v5 = u5 * (v5 * v5) := by noncomm_ring
      _ = 0 := by rw [v5_sq, mul_zero]
  have hv5_u5_v5 : v5 * u5 * v5 = v5 := by
    calc
      v5 * u5 * v5 = v5 * (u5 * v5) := by noncomm_ring
      _ = v5 := hvu5
  have h_inner : (u5 * v5 * v5 - v5 * u5 * v5) - (v5 * (u5 * v5) - v5 * (v5 * u5)) = - (2 : ℝ) • v5 := by
    have h1 : v5 * (v5 * u5) = 0 := by
      calc
        v5 * (v5 * u5) = (v5 * v5) * u5 := by noncomm_ring
        _ = 0 := by rw [v5_sq, zero_mul]
    have h_two : v5 + v5 = (2 : ℝ) • v5 := by
      have h_one : v5 = (1 : ℝ) • v5 := by exact Eq.symm (one_smul ℝ v5)
      nth_rw 1 [h_one]
      nth_rw 2 [h_one]
      rw [← add_smul]
      norm_num
    calc
      (u5 * v5 * v5 - v5 * u5 * v5) - (v5 * (u5 * v5) - v5 * (v5 * u5))
          = (0 - v5) - (v5 - 0) := by rw [huvv, hv5_u5_v5, h1, hvu5]
      _ = - (v5 + v5) := by abel
      _ = - (2 : ℝ) • v5 := by rw [h_two, neg_smul]
  rw [← smul_sub]
  rw [h_inner]
  rw [smul_smul]
  norm_num

theorem adD4_v5 : D4 * v5 - v5 * D4 = 0 := by
  dsimp [D4]
  rw [smul_mul_assoc, Algebra.mul_smul_comm, sub_mul, mul_sub, ← smul_sub]
  have h1 : u4 * v4 * v5 = v5 * (u4 * v4) := by
    calc
      u4 * v4 * v5 = u4 * (v4 * v5) := by noncomm_ring
      _ = u4 * (- (v5 * v4)) := by rw [h_v4_v5_anti]
      _ = - (u4 * v5 * v4) := by noncomm_ring
      _ = - (- (v5 * u4) * v4) := by rw [h_u4_v5_anti]
      _ = v5 * u4 * v4 := by noncomm_ring
      _ = v5 * (u4 * v4) := by noncomm_ring
  have h2 : v4 * u4 * v5 = v5 * (v4 * u4) := by
    calc
      v4 * u4 * v5 = v4 * (u4 * v5) := by noncomm_ring
      _ = v4 * (- (v5 * u4)) := by rw [h_u4_v5_anti]
      _ = - (v4 * v5 * u4) := by noncomm_ring
      _ = - (- (v5 * v4) * u4) := by rw [h_v4_v5_anti]
      _ = v5 * v4 * u4 := by noncomm_ring
      _ = v5 * (v4 * u4) := by noncomm_ring
  rw [h1, h2]
  have h_sub : v5 * (u4 * v4) - v5 * (v4 * u4) - (v5 * (u4 * v4) - v5 * (v4 * u4)) = 0 := by abel
  rw [h_sub]
  exact smul_zero (1 / 2 : ℝ)

theorem adD_v5 : D * v5 - v5 * D = -v5 := by
  dsimp [D]
  have h1 : D5 * v5 - v5 * D5 = -v5 := adD5_v5
  have h2 : D4 * v5 - v5 * D4 = 0 := adD4_v5
  calc
    (D5 + D4) * v5 - v5 * (D5 + D4) = D5 * v5 + D4 * v5 - (v5 * D5 + v5 * D4) := by noncomm_ring
    _ = (D5 * v5 - v5 * D5) + (D4 * v5 - v5 * D4) := by abel
    _ = -v5 + 0 := by rw [h1, h2]
    _ = -v5 := by exact add_zero (-v5)

theorem adD5_v4 : D5 * v4 - v4 * D5 = 0 := by
  dsimp [D5]
  rw [smul_mul_assoc, Algebra.mul_smul_comm, sub_mul, mul_sub, ← smul_sub]
  have h1 : u5 * v5 * v4 = v4 * (u5 * v5) := by
    calc
      u5 * v5 * v4 = u5 * (v5 * v4) := by noncomm_ring
      _ = u5 * (- (v4 * v5)) := by rw [v5_v4_anti]
      _ = - (u5 * v4 * v5) := by noncomm_ring
      _ = - (- (v4 * u5) * v5) := by rw [u5_v4_anti]
      _ = v4 * u5 * v5 := by noncomm_ring
      _ = v4 * (u5 * v5) := by noncomm_ring
  have h2 : v5 * u5 * v4 = v4 * (v5 * u5) := by
    calc
      v5 * u5 * v4 = v5 * (u5 * v4) := by noncomm_ring
      _ = v5 * (- (v4 * u5)) := by rw [u5_v4_anti]
      _ = - (v5 * v4 * u5) := by noncomm_ring
      _ = - (- (v4 * v5) * u5) := by rw [v5_v4_anti]
      _ = v4 * v5 * u5 := by noncomm_ring
      _ = v4 * (v5 * u5) := by noncomm_ring
  rw [h1, h2]
  have h_sub : v4 * (u5 * v5) - v4 * (v5 * u5) - (v4 * (u5 * v5) - v4 * (v5 * u5)) = 0 := by abel
  rw [h_sub]
  exact smul_zero (1 / 2 : ℝ)

theorem adD4_v4 : D4 * v4 - v4 * D4 = -v4 := by
  dsimp [D4]
  rw [smul_mul_assoc, Algebra.mul_smul_comm, sub_mul, mul_sub]
  have hsub' : u4 * v4 + v4 * u4 = 1 := u4_v4_add_v4_u4
  have hvu4 : v4 * (u4 * v4) = v4 := by
    have hvu4' : u4 * v4 = 1 - v4 * u4 := eq_sub_of_add_eq hsub'
    calc
      v4 * (u4 * v4) = v4 * (1 - v4 * u4) := by rw [hvu4']
      _ = v4 - v4 * (v4 * u4) := by rw [mul_sub]; simp
      _ = v4 - (v4 * v4) * u4 := by rw [← mul_assoc]
      _ = v4 - 0 := by rw [v4_sq]; simp
      _ = v4 := by simp
  have huvv : u4 * v4 * v4 = 0 := by
    calc
      u4 * v4 * v4 = u4 * (v4 * v4) := by noncomm_ring
      _ = 0 := by rw [v4_sq, mul_zero]
  have hv4_u4_v4 : v4 * u4 * v4 = v4 := by
    calc
      v4 * u4 * v4 = v4 * (u4 * v4) := by noncomm_ring
      _ = v4 := hvu4
  have h_inner : (u4 * v4 * v4 - v4 * u4 * v4) - (v4 * (u4 * v4) - v4 * (v4 * u4)) = - (2 : ℝ) • v4 := by
    have h1 : v4 * (v4 * u4) = 0 := by
      calc
        v4 * (v4 * u4) = (v4 * v4) * u4 := by noncomm_ring
        _ = 0 := by rw [v4_sq, zero_mul]
    have h_two : v4 + v4 = (2 : ℝ) • v4 := by
      have h_one : v4 = (1 : ℝ) • v4 := by exact Eq.symm (one_smul ℝ v4)
      nth_rw 1 [h_one]
      nth_rw 2 [h_one]
      rw [← add_smul]
      norm_num
    calc
      (u4 * v4 * v4 - v4 * u4 * v4) - (v4 * (u4 * v4) - v4 * (v4 * u4))
          = (0 - v4) - (v4 - 0) := by rw [huvv, hv4_u4_v4, h1, hvu4]
      _ = - (v4 + v4) := by abel
      _ = - (2 : ℝ) • v4 := by rw [h_two, neg_smul]
  rw [← smul_sub]
  rw [h_inner]
  rw [smul_smul]
  norm_num

theorem adD_v4 : D * v4 - v4 * D = -v4 := by
  dsimp [D]
  have h1 : D5 * v4 - v4 * D5 = 0 := adD5_v4
  have h2 : D4 * v4 - v4 * D4 = -v4 := adD4_v4
  calc
    (D5 + D4) * v4 - v4 * (D5 + D4) = D5 * v4 + D4 * v4 - (v4 * D5 + v4 * D4) := by noncomm_ring
    _ = (D5 * v4 - v4 * D5) + (D4 * v4 - v4 * D4) := by abel
    _ = 0 + -v4 := by rw [h1, h2]
    _ = -v4 := by exact zero_add (-v4)

/-! ## 1. Precise Grade Assignments -/

theorem u5_grade : u5 ∈ gradeSpace ConformalGrade.posOne := by
  dsimp [gradeSpace]
  rw [LinearMap.mem_ker]
  dsimp [adD, toInt]
  rw [adD_u5]
  simp

theorem u4_grade : u4 ∈ gradeSpace ConformalGrade.posOne := by
  dsimp [gradeSpace]
  rw [LinearMap.mem_ker]
  dsimp [adD, toInt]
  rw [adD_u4]
  simp

theorem v5_grade : v5 ∈ gradeSpace ConformalGrade.negOne := by
  dsimp [gradeSpace]
  rw [LinearMap.mem_ker]
  dsimp [adD, toInt]
  rw [adD_v5]
  simp

theorem v4_grade : v4 ∈ gradeSpace ConformalGrade.negOne := by
  dsimp [gradeSpace]
  rw [LinearMap.mem_ker]
  dsimp [adD, toInt]
  rw [adD_v4]
  simp

theorem D_grade : D ∈ gradeSpace ConformalGrade.zero := by
  dsimp [gradeSpace]
  rw [LinearMap.mem_ker]
  dsimp [adD, toInt]
  simp

theorem u5_v5_commutator_grade_zero :
    u5 * v5 - v5 * u5 ∈ gradeSpace ConformalGrade.zero := by
  apply gradeSpace_commutator_of_sum ConformalGrade.posOne
    ConformalGrade.negOne ConformalGrade.zero u5_grade v5_grade
  rfl

theorem u4_v4_commutator_grade_zero :
    u4 * v4 - v4 * u4 ∈ gradeSpace ConformalGrade.zero := by
  apply gradeSpace_commutator_of_sum ConformalGrade.posOne
    ConformalGrade.negOne ConformalGrade.zero u4_grade v4_grade
  rfl

theorem u5_u4_commutator_grade_pos_two :
    u5 * u4 - u4 * u5 ∈ gradeSpace ConformalGrade.posTwo := by
  apply gradeSpace_commutator_of_sum ConformalGrade.posOne
    ConformalGrade.posOne ConformalGrade.posTwo u5_grade u4_grade
  rfl

theorem v5_v4_commutator_grade_neg_two :
    v5 * v4 - v4 * v5 ∈ gradeSpace ConformalGrade.negTwo := by
  apply gradeSpace_commutator_of_sum ConformalGrade.negOne
    ConformalGrade.negOne ConformalGrade.negTwo v5_grade v4_grade
  rfl

theorem u5_u4_anticommutator_grade_pos_two :
    u5 * u4 + u4 * u5 ∈ gradeSpace ConformalGrade.posTwo := by
  apply gradeSpace_anticommutator_of_sum ConformalGrade.posOne
    ConformalGrade.posOne ConformalGrade.posTwo u5_grade u4_grade
  rfl

theorem v5_v4_anticommutator_grade_neg_two :
    v5 * v4 + v4 * v5 ∈ gradeSpace ConformalGrade.negTwo := by
  apply gradeSpace_anticommutator_of_sum ConformalGrade.negOne
    ConformalGrade.negOne ConformalGrade.negTwo v5_grade v4_grade
  rfl


end InfoGeometry.Canonical.O55FiveGradeClosure
