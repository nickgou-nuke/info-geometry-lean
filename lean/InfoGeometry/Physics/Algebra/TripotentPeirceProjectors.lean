import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Peirce projectors for a tripotent element

For an element `T` of an associative real algebra satisfying `T^3 = T`,
these three polynomial projectors are pairwise orthogonal and sum to one.
-/

namespace InfoGeometry.Physics.Algebra

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R]

def projPos (T : R) : R := (1 / 2 : ℝ) • (T * T + T)
def projNeg (T : R) : R := (1 / 2 : ℝ) • (T * T - T)
def projZero (T : R) : R := 1 - T * T

section
variable {T : R}

private lemma tripotent_pow_four (hT : T * T * T = T) :
    T * T * T * T = T * T := by
  calc
    T * T * T * T = (T * T * T) * T := by rw [mul_assoc]
    _ = T * T := by rw [hT]

private lemma tripotent_plus (hT : T * T * T = T) :
    T * (T * T + T) = T * T + T := by
  calc
    T * (T * T + T) = T * (T * T) + T * T := by rw [mul_add]
    _ = T + T * T := by rw [← mul_assoc, hT]
    _ = T * T + T := by abel

private lemma tripotent_minus (hT : T * T * T = T) :
    T * (T * T - T) = -(T * T - T) := by
  calc
    T * (T * T - T) = T * (T * T) - T * T := by rw [mul_sub]
    _ = T - T * T := by rw [← mul_assoc, hT]
    _ = -(T * T - T) := by abel

private lemma plus_square (hT : T * T * T = T) :
    (T * T + T) * (T * T + T) = (2 : R) * (T * T + T) := by
  calc
    (T * T + T) * (T * T + T) =
        T * T * T * T + T * T * T + T * T * T + T * T := by
          noncomm_ring
    _ = T * T + T + T + T * T := by
          rw [tripotent_pow_four hT, hT]
    _ = (2 : R) * (T * T + T) := by
          rw [two_mul]
          abel

private lemma minus_square (hT : T * T * T = T) :
    (T * T - T) * (T * T - T) = (2 : R) * (T * T - T) := by
  calc
    (T * T - T) * (T * T - T) =
        T * T * T * T - T * T * T - T * T * T + T * T := by
          noncomm_ring
    _ = T * T - T - T + T * T := by
          rw [tripotent_pow_four hT, hT]
    _ = (2 : R) * (T * T - T) := by
          rw [two_mul]
          abel

@[simp] theorem projPos_add_projNeg :
    projPos T + projNeg T = T * T := by
  calc
    projPos T + projNeg T = (1 / 2 : ℝ) •
        ((T * T + T) + (T * T - T)) := by
          simp [projPos, projNeg, smul_add, add_assoc, add_comm]
    _ = (1 / 2 : ℝ) • ((2 : R) * (T * T)) := by
          rw [two_mul]
          abel
    _ = T * T := by
          rw [two_mul, ← two_smul ℝ, smul_smul]
          norm_num

@[simp] theorem projPos_sub_projNeg :
    projPos T - projNeg T = T := by
  calc
    projPos T - projNeg T = (1 / 2 : ℝ) •
        ((T * T + T) - (T * T - T)) := by
          simp [projPos, projNeg, smul_sub, sub_eq_add_neg]
    _ = (1 / 2 : ℝ) • ((2 : R) * T) := by
          rw [two_mul]
          abel
    _ = T := by
          rw [two_mul, ← two_smul ℝ, smul_smul]
          norm_num

@[simp] theorem proj_sum_eq_id :
    projPos T + projZero T + projNeg T = 1 := by
  calc
    projPos T + projZero T + projNeg T =
        projZero T + (projPos T + projNeg T) := by abel
    _ = (1 - T * T) + T * T := by rw [projZero, projPos_add_projNeg]
    _ = 1 := by abel

@[simp] theorem projPos_idempotent (hT : T * T * T = T) :
    projPos T * projPos T = projPos T := by
  unfold projPos
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [plus_square hT]
  rw [two_mul, ← two_smul ℝ, smul_smul]
  norm_num

@[simp] theorem projNeg_idempotent (hT : T * T * T = T) :
    projNeg T * projNeg T = projNeg T := by
  unfold projNeg
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [minus_square hT]
  rw [two_mul, ← two_smul ℝ, smul_smul]
  norm_num

@[simp] theorem projZero_idempotent (hT : T * T * T = T) :
    projZero T * projZero T = projZero T := by
  unfold projZero
  calc
    (1 - T * T) * (1 - T * T) =
        1 - T * T - T * T + T * T * T * T := by noncomm_ring
    _ = 1 - T * T := by rw [tripotent_pow_four hT]; abel

@[simp] theorem projPos_mul_projNeg_eq_zero (hT : T * T * T = T) :
    projPos T * projNeg T = 0 := by
  unfold projPos projNeg
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have h : (T * T + T) * (T * T - T) = 0 := by
    calc
      (T * T + T) * (T * T - T) = T * T * T * T - T * T := by noncomm_ring
      _ = 0 := by rw [tripotent_pow_four hT]; simp
  rw [h]
  simp

@[simp] theorem projNeg_mul_projPos_eq_zero (hT : T * T * T = T) :
    projNeg T * projPos T = 0 := by
  unfold projNeg projPos
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have h : (T * T - T) * (T * T + T) = 0 := by
    calc
      (T * T - T) * (T * T + T) = T * T * T * T - T * T := by noncomm_ring
      _ = 0 := by rw [tripotent_pow_four hT]; simp
  rw [h]
  simp

@[simp] theorem projPos_mul_projZero_eq_zero (hT : T * T * T = T) :
    projPos T * projZero T = 0 := by
  unfold projPos projZero
  rw [Algebra.smul_mul_assoc]
  have h : (T * T + T) * (1 - T * T) = 0 := by
    calc
      (T * T + T) * (1 - T * T) =
          T * T + T - (T * T * T * T + T * T * T) := by noncomm_ring
      _ = 0 := by rw [tripotent_pow_four hT, hT]; abel
  rw [h]
  simp

@[simp] theorem projZero_mul_projPos_eq_zero (hT : T * T * T = T) :
    projZero T * projPos T = 0 := by
  unfold projZero projPos
  rw [Algebra.mul_smul_comm]
  have h : (1 - T * T) * (T * T + T) = 0 := by
    calc
      (1 - T * T) * (T * T + T) =
          T * T + T - (T * T * T * T + T * T * T) := by noncomm_ring
      _ = 0 := by rw [tripotent_pow_four hT, hT]; abel
  rw [h]
  simp

@[simp] theorem projNeg_mul_projZero_eq_zero (hT : T * T * T = T) :
    projNeg T * projZero T = 0 := by
  unfold projNeg projZero
  rw [Algebra.smul_mul_assoc]
  have h : (T * T - T) * (1 - T * T) = 0 := by
    calc
      (T * T - T) * (1 - T * T) =
          T * T - T - (T * T * T * T - T * T * T) := by noncomm_ring
      _ = 0 := by rw [tripotent_pow_four hT, hT]; abel
  rw [h]
  simp

@[simp] theorem projZero_mul_projNeg_eq_zero (hT : T * T * T = T) :
    projZero T * projNeg T = 0 := by
  unfold projZero projNeg
  rw [Algebra.mul_smul_comm]
  have h : (1 - T * T) * (T * T - T) = 0 := by
    calc
      (1 - T * T) * (T * T - T) =
          T * T - T - (T * T * T * T - T * T * T) := by noncomm_ring
      _ = 0 := by rw [tripotent_pow_four hT, hT]; abel
  rw [h]
  simp

@[simp] theorem mul_projPos (hT : T * T * T = T) :
    T * projPos T = projPos T := by
  unfold projPos
  rw [Algebra.mul_smul_comm]
  rw [tripotent_plus hT]

@[simp] theorem projPos_mul (hT : T * T * T = T) :
    projPos T * T = projPos T := by
  unfold projPos
  rw [Algebra.smul_mul_assoc]
  have h : (T * T + T) * T = T * T + T := by
    calc
      (T * T + T) * T = T * T * T + T * T := by rw [add_mul]
      _ = T + T * T := by rw [hT]
      _ = T * T + T := by abel
  rw [h]

@[simp] theorem mul_projNeg (hT : T * T * T = T) :
    T * projNeg T = -projNeg T := by
  unfold projNeg
  rw [Algebra.mul_smul_comm, tripotent_minus hT]
  rw [smul_neg]

@[simp] theorem projNeg_mul (hT : T * T * T = T) :
    projNeg T * T = -projNeg T := by
  unfold projNeg
  rw [Algebra.smul_mul_assoc]
  have h : (T * T - T) * T = -(T * T - T) := by
    calc
      (T * T - T) * T = T * T * T - T * T := by rw [sub_mul]
      _ = T - T * T := by rw [hT]
      _ = -(T * T - T) := by abel
  rw [h]
  rw [smul_neg]

@[simp] theorem mul_projZero (hT : T * T * T = T) :
    T * projZero T = 0 := by
  unfold projZero
  calc
    T * (1 - T * T) = T - T * (T * T) := by rw [mul_sub, mul_one]
    _ = 0 := by rw [← mul_assoc, hT]; simp

@[simp] theorem projZero_mul (hT : T * T * T = T) :
    projZero T * T = 0 := by
  unfold projZero
  calc
    (1 - T * T) * T = T - (T * T) * T := by rw [sub_mul, one_mul]
    _ = 0 := by rw [hT]; simp

end
end
end InfoGeometry.Physics.Algebra
