/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitz

/-!
# General q-CCR vacuum-defect closure

This module derives the exact residual action of the vacuum defect from the
owner `QCCROperators` relation at arbitrary deformation parameter `q`.
The q = 0 annihilation laws are recovered as genuine specializations.
-/


namespace InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitzGeneralized

open BigOperators
open InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitz

variable {ι R Op : Type*} [DecidableEq ι] [Fintype ι]
  [CommRing R] [Ring Op] [StarRing Op] [Algebra R Op]

/-- At arbitrary q, the left vacuum-defect action is exactly the q-weighted residual
sum obtained by substituting the q-CCR relation into the defect. -/
theorem star_mul_P_vac_eq_neg_q_sum
    (A : QCCROperators ι R Op) (j : ι) :
    star (A.a j) * P_vac A =
      (-A.q) • (∑ i : ι, (A.a i * star (A.a j)) * star (A.a i)) := by
  unfold P_vac
  rw [mul_sub, mul_one, Finset.mul_sum]
  have hterm : ∀ i : ι,
      star (A.a j) * (A.a i * star (A.a i)) =
        (if j = i then star (A.a i) else 0) +
          A.q • ((A.a i * star (A.a j)) * star (A.a i)) := by
    intro i
    rw [← mul_assoc, A.q_commutation j i]
    by_cases hji : j = i
    · rw [if_pos hji, add_mul, smul_mul_assoc]
      simp [hji]
    · rw [if_neg hji, add_mul, smul_mul_assoc]
      simp [hji]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  have hdelta : (∑ i : ι, (if j = i then star (A.a i) else 0)) = star (A.a j) := by
    simp
  rw [hdelta]
  rw [← Finset.smul_sum]
  abel
  module

/-- At arbitrary q, the right vacuum-defect action is exactly the q-weighted residual
sum obtained by substituting the q-CCR relation into the defect. -/
theorem P_vac_mul_a_eq_neg_q_sum
    (A : QCCROperators ι R Op) (j : ι) :
    P_vac A * A.a j =
      (-A.q) • (∑ i : ι, A.a i * (A.a j * star (A.a i))) := by
  unfold P_vac
  rw [sub_mul, one_mul, Finset.sum_mul]
  have hterm : ∀ i : ι,
      (A.a i * star (A.a i)) * A.a j =
        (if i = j then A.a i else 0) +
          A.q • (A.a i * (A.a j * star (A.a i))) := by
    intro i
    rw [mul_assoc, A.q_commutation i j]
    by_cases hij : i = j
    · rw [if_pos hij, mul_add, mul_smul_comm]
      simp [hij]
    · rw [if_neg hij, mul_add, mul_smul_comm]
      simp [hij]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  have hdelta : (∑ i : ι, (if i = j then A.a i else 0)) = A.a j := by
    simp
  rw [hdelta]
  rw [← Finset.smul_sum]
  abel
  module

/-- The q = 0 specialization recovers exact annihilation of the vacuum defect. -/
theorem star_mul_P_vac_eq_zero_of_q_zero
    (A : QCCROperators ι R Op) (hq0 : A.q = 0) (j : ι) :
    star (A.a j) * P_vac A = 0 := by
  rw [star_mul_P_vac_eq_neg_q_sum A j, hq0, neg_zero, zero_smul]

/-- The q = 0 specialization recovers exact annihilation of the vacuum defect. -/
theorem P_vac_mul_a_eq_zero_of_q_zero
    (A : QCCROperators ι R Op) (hq0 : A.q = 0) (j : ι) :
    P_vac A * A.a j = 0 := by
  rw [P_vac_mul_a_eq_neg_q_sum A j, hq0, neg_zero, zero_smul]

end InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitzGeneralized
