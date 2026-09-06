import Mathlib.Tactic
import InfoGeometry.Categorical.FibonacciBraiding
import InfoGeometry.Canonical.FibonacciBraidingPhaseBridge

open InfoGeometry.Categorical.FibonacciBraiding
open FibonacciBraidingPhaseBridge
open Complex

noncomputable section

namespace InfoGeometry.Categorical.CuntzCliffordFibonacciBraid

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- Chiral Cuntz raising operator S₊ = (γ₁ + i γ₂) / 2 in any Clifford algebra R over ℂ. -/
def S_plus (g1 g2 : R) : R :=
  (1 / 2 : ℂ) • g1 + (I / 2 : ℂ) • g2

/-- Chiral Cuntz lowering operator S₋ = (γ₁ - i γ₂) / 2 in any Clifford algebra R over ℂ. -/
def S_minus (g1 g2 : R) : R :=
  (1 / 2 : ℂ) • g1 - (I / 2 : ℂ) • g2

/-- **Theorem**: Chiral Cuntz Nilpotency S₊² = 0. -/
theorem S_plus_sq (g1 g2 : R)
    (hg1 : g1 ^ 2 = 1) (hg2 : g2 ^ 2 = 1)
    (h12 : g1 * g2 + g2 * g1 = 0) :
    S_plus g1 g2 ^ 2 = 0 := by
  dsimp [S_plus]
  have hI : (I : ℂ) ^ 2 = -1 := by norm_num
  have hg1_m : g1 * g1 = 1 := by rw [← sq, hg1]
  have hg2_m : g2 * g2 = 1 := by rw [← sq, hg2]
  have h_sq1 : ((1 / 2 : ℂ) • g1) * ((1 / 2 : ℂ) • g1) = (1 / 4 : ℂ) • (1 : R) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hg1_m]
    norm_num
  have h_sq2 : ((I / 2 : ℂ) • g2) * ((I / 2 : ℂ) • g2) = (-1 / 4 : ℂ) • (1 : R) := by
    have h_c : (I / 2 : ℂ) * (I / 2 : ℂ) = -1 / 4 := by
      calc (I / 2 : ℂ) * (I / 2 : ℂ)
        _ = (I ^ 2 / 4 : ℂ) := by ring
        _ = -1 / 4 := by rw [hI]
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hg2_m, h_c]
  have h_mix : ((1 / 2 : ℂ) • g1) * ((I / 2 : ℂ) • g2) + ((I / 2 : ℂ) • g2) * ((1 / 2 : ℂ) • g1) = 0 := by
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    have h_c : (1 / 2 * (I / 2) : ℂ) = I / 4 := by ring
    have h_c2 : (I / 2 * (1 / 2) : ℂ) = I / 4 := by ring
    rw [h_c, h_c2, ← smul_add, h12, smul_zero]
  rw [sq]
  have h_exp : ((1 / 2 : ℂ) • g1 + (I / 2 : ℂ) • g2) * ((1 / 2 : ℂ) • g1 + (I / 2 : ℂ) • g2) =
      ((1 / 2 : ℂ) • g1) * ((1 / 2 : ℂ) • g1) + (((1 / 2 : ℂ) • g1) * ((I / 2 : ℂ) • g2) + ((I / 2 : ℂ) • g2) * ((1 / 2 : ℂ) • g1)) + ((I / 2 : ℂ) • g2) * ((I / 2 : ℂ) • g2) := by
    simp only [add_mul, mul_add]
    abel
  rw [h_exp, h_sq1, h_sq2, h_mix]
  simp only [add_zero, ← add_smul]
  have : (1 / 4 : ℂ) + (-1 / 4 : ℂ) = 0 := by ring
  rw [this, zero_smul]

/-- **Theorem**: Chiral Cuntz Nilpotency S₋² = 0. -/
theorem S_minus_sq (g1 g2 : R)
    (hg1 : g1 ^ 2 = 1) (hg2 : g2 ^ 2 = 1)
    (h12 : g1 * g2 + g2 * g1 = 0) :
    S_minus g1 g2 ^ 2 = 0 := by
  dsimp [S_minus]
  have hI : (I : ℂ) ^ 2 = -1 := by norm_num
  have hg1_m : g1 * g1 = 1 := by rw [← sq, hg1]
  have hg2_m : g2 * g2 = 1 := by rw [← sq, hg2]
  have h_sq1 : ((1 / 2 : ℂ) • g1) * ((1 / 2 : ℂ) • g1) = (1 / 4 : ℂ) • (1 : R) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hg1_m]
    norm_num
  have h_sq2 : ((I / 2 : ℂ) • g2) * ((I / 2 : ℂ) • g2) = (-1 / 4 : ℂ) • (1 : R) := by
    have h_c : (I / 2 : ℂ) * (I / 2 : ℂ) = -1 / 4 := by
      calc (I / 2 : ℂ) * (I / 2 : ℂ)
        _ = (I ^ 2 / 4 : ℂ) := by ring
        _ = -1 / 4 := by rw [hI]
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hg2_m, h_c]
  have h_mix : ((1 / 2 : ℂ) • g1) * ((I / 2 : ℂ) • g2) + ((I / 2 : ℂ) • g2) * ((1 / 2 : ℂ) • g1) = 0 := by
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    have h_c : (1 / 2 * (I / 2) : ℂ) = I / 4 := by ring
    have h_c2 : (I / 2 * (1 / 2) : ℂ) = I / 4 := by ring
    rw [h_c, h_c2, ← smul_add, h12, smul_zero]
  rw [sq]
  have h_exp : ((1 / 2 : ℂ) • g1 - (I / 2 : ℂ) • g2) * ((1 / 2 : ℂ) • g1 - (I / 2 : ℂ) • g2) =
      ((1 / 2 : ℂ) • g1) * ((1 / 2 : ℂ) • g1) - (((1 / 2 : ℂ) • g1) * ((I / 2 : ℂ) • g2) + ((I / 2 : ℂ) • g2) * ((1 / 2 : ℂ) • g1)) + ((I / 2 : ℂ) • g2) * ((I / 2 : ℂ) • g2) := by
    simp only [sub_mul, mul_sub]
    abel
  rw [h_exp, h_sq1, h_sq2, h_mix]
  simp only [sub_zero, ← add_smul]
  have : (1 / 4 : ℂ) + (-1 / 4 : ℂ) = 0 := by ring
  rw [this, zero_smul]

/-- **Theorem**: Canonical Anti-Commutation Relation {S₊, S₋} = 1. -/
theorem S_plus_S_minus_anticomm (g1 g2 : R)
    (hg1 : g1 ^ 2 = 1) (hg2 : g2 ^ 2 = 1) :
    S_plus g1 g2 * S_minus g1 g2 + S_minus g1 g2 * S_plus g1 g2 = 1 := by
  dsimp [S_plus, S_minus]
  have hI : (I : ℂ) ^ 2 = -1 := by norm_num
  have hg1_m : g1 * g1 = 1 := by rw [← sq, hg1]
  have hg2_m : g2 * g2 = 1 := by rw [← sq, hg2]
  have h_sq1 : ((1 / 2 : ℂ) • g1) * ((1 / 2 : ℂ) • g1) = (1 / 4 : ℂ) • (1 : R) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hg1_m]
    norm_num
  have h_sq2 : ((I / 2 : ℂ) • g2) * ((I / 2 : ℂ) • g2) = (-1 / 4 : ℂ) • (1 : R) := by
    have h_c : (I / 2 : ℂ) * (I / 2 : ℂ) = -1 / 4 := by
      calc (I / 2 : ℂ) * (I / 2 : ℂ)
        _ = (I ^ 2 / 4 : ℂ) := by ring
        _ = -1 / 4 := by rw [hI]
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hg2_m, h_c]
  have h_exp : ((1 / 2 : ℂ) • g1 + (I / 2 : ℂ) • g2) * ((1 / 2 : ℂ) • g1 - (I / 2 : ℂ) • g2) +
        ((1 / 2 : ℂ) • g1 - (I / 2 : ℂ) • g2) * ((1 / 2 : ℂ) • g1 + (I / 2 : ℂ) • g2) =
      ((1 / 2 : ℂ) • g1) * ((1 / 2 : ℂ) • g1) + ((1 / 2 : ℂ) • g1) * ((1 / 2 : ℂ) • g1) -
      (((I / 2 : ℂ) • g2) * ((I / 2 : ℂ) • g2) + ((I / 2 : ℂ) • g2) * ((I / 2 : ℂ) • g2)) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    abel
  rw [h_exp, h_sq1, h_sq2]
  have h_add1 : (1 / 4 : ℂ) • (1 : R) + (1 / 4 : ℂ) • (1 : R) = (1 / 2 : ℂ) • (1 : R) := by
    rw [← add_smul]
    norm_num
  have h_add2 : (-1 / 4 : ℂ) • (1 : R) + (-1 / 4 : ℂ) • (1 : R) = (-1 / 2 : ℂ) • (1 : R) := by
    rw [← add_smul]
    norm_num
  have h_sub_exp : ((1 / 4 : ℂ) • (1 : R) + (1 / 4 : ℂ) • (1 : R)) - ((-1 / 4 : ℂ) • (1 : R) + (-1 / 4 : ℂ) • (1 : R)) = (1 / 2 : ℂ) • (1 : R) - (-1 / 2 : ℂ) • (1 : R) := by
    rw [h_add1, h_add2]
  rw [h_sub_exp, ← sub_smul]
  have h_c3 : (1 / 2 : ℂ) - (-1 / 2 : ℂ) = 1 := by ring
  rw [h_c3, one_smul]

/-- Unitary Braid Exchange Operator R(θ) = cos(θ/2) + sin(θ/2) γ₁γ₂ in R. -/
def braidExchange (g1 g2 : R) (θ : ℝ) : R :=
  (Real.cos (θ / 2) : ℂ) • (1 : R) + (Real.sin (θ / 2) : ℂ) • (g1 * g2)

/-- **Theorem**: Braid Exchange Inverse Identity: R(θ) R(-θ) = 1. -/
theorem braidExchange_inv (g1 g2 : R) (θ : ℝ)
    (hg1 : g1 ^ 2 = 1) (hg2 : g2 ^ 2 = 1)
    (h12 : g1 * g2 + g2 * g1 = 0) :
    braidExchange g1 g2 θ * braidExchange g1 g2 (-θ) = 1 := by
  have h12_sq : (g1 * g2) ^ 2 = -1 := by
    have h_comm : g2 * g1 = - (g1 * g2) := eq_neg_of_add_eq_zero_right h12
    have hg1_m : g1 * g1 = 1 := by rw [← sq, hg1]
    have hg2_m : g2 * g2 = 1 := by rw [← sq, hg2]
    calc (g1 * g2) ^ 2
      _ = (g1 * g2) * (g1 * g2) := by rw [sq]
      _ = g1 * (g2 * g1) * g2 := by simp only [mul_assoc]
      _ = g1 * (- (g1 * g2)) * g2 := by rw [h_comm]
      _ = - (g1 * g1 * (g2 * g2)) := by simp only [mul_neg, neg_mul, mul_assoc]
      _ = - (1 * 1) := by rw [hg1_m, hg2_m]
      _ = -1 := by rw [mul_one]
  have h_cos_neg : Real.cos (-θ / 2) = Real.cos (θ / 2) := by
    have : -θ / 2 = -(θ / 2) := by ring
    rw [this, Real.cos_neg]
  have h_sin_neg : Real.sin (-θ / 2) = - Real.sin (θ / 2) := by
    have : -θ / 2 = -(θ / 2) := by ring
    rw [this, Real.sin_neg]
  have h_trig_c : (Real.cos (θ / 2) : ℂ) ^ 2 + (Real.sin (θ / 2) : ℂ) ^ 2 = 1 := by
    norm_cast
    exact Real.cos_sq_add_sin_sq (θ / 2)
  have hA : ((Real.cos (θ / 2) : ℂ) • (1 : R)) * ((Real.cos (θ / 2) : ℂ) • (1 : R)) = ((Real.cos (θ / 2) : ℂ) ^ 2) • (1 : R) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_one, ← sq]
  have hB : ((Real.sin (θ / 2) : ℂ) • (g1 * g2)) * ((Real.sin (θ / 2) : ℂ) • (g1 * g2)) = ((Real.sin (θ / 2) : ℂ) ^ 2) • ((g1 * g2) ^ 2) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, ← sq, ← sq]
  have h_comm_cross : ((Real.cos (θ / 2) : ℂ) • (1 : R)) * ((Real.sin (θ / 2) : ℂ) • (g1 * g2)) =
        ((Real.sin (θ / 2) : ℂ) • (g1 * g2)) * ((Real.cos (θ / 2) : ℂ) • (1 : R)) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_smul, mul_one, one_mul]
    congr 1
    ring
  have h_exp_sub : ((Real.cos (θ / 2) : ℂ) • (1 : R) + (Real.sin (θ / 2) : ℂ) • (g1 * g2)) *
        ((Real.cos (θ / 2) : ℂ) • (1 : R) - (Real.sin (θ / 2) : ℂ) • (g1 * g2)) =
      ((Real.cos (θ / 2) : ℂ) ^ 2) • (1 : R) - ((Real.sin (θ / 2) : ℂ) ^ 2) • ((g1 * g2) ^ 2) := by
    calc ((Real.cos (θ / 2) : ℂ) • (1 : R) + (Real.sin (θ / 2) : ℂ) • (g1 * g2)) *
          ((Real.cos (θ / 2) : ℂ) • (1 : R) - (Real.sin (θ / 2) : ℂ) • (g1 * g2))
      _ = ((Real.cos (θ / 2) : ℂ) • (1 : R)) * ((Real.cos (θ / 2) : ℂ) • (1 : R)) +
          ((Real.sin (θ / 2) : ℂ) • (g1 * g2)) * ((Real.cos (θ / 2) : ℂ) • (1 : R)) -
          ((Real.cos (θ / 2) : ℂ) • (1 : R)) * ((Real.sin (θ / 2) : ℂ) • (g1 * g2)) -
          ((Real.sin (θ / 2) : ℂ) • (g1 * g2)) * ((Real.sin (θ / 2) : ℂ) • (g1 * g2)) := by
        simp only [add_mul, sub_mul, mul_sub]
        abel
      _ = ((Real.cos (θ / 2) : ℂ) ^ 2) • (1 : R) + ((Real.sin (θ / 2) : ℂ) • (g1 * g2)) * ((Real.cos (θ / 2) : ℂ) • (1 : R)) -
          ((Real.sin (θ / 2) : ℂ) • (g1 * g2)) * ((Real.cos (θ / 2) : ℂ) • (1 : R)) -
          ((Real.sin (θ / 2) : ℂ) ^ 2) • ((g1 * g2) ^ 2) := by rw [hA, hB, h_comm_cross]
      _ = ((Real.cos (θ / 2) : ℂ) ^ 2) • (1 : R) - ((Real.sin (θ / 2) : ℂ) ^ 2) • ((g1 * g2) ^ 2) := by abel
  have h_exp : ((Real.cos (θ / 2) : ℂ) • (1 : R) + (Real.sin (θ / 2) : ℂ) • (g1 * g2)) *
        ((Real.cos (θ / 2) : ℂ) • (1 : R) + (-Real.sin (θ / 2) : ℂ) • (g1 * g2)) =
      ((Real.cos (θ / 2) : ℂ) ^ 2) • (1 : R) - ((Real.sin (θ / 2) : ℂ) ^ 2) • ((g1 * g2) ^ 2) := by
    rw [neg_smul, ← sub_eq_add_neg, h_exp_sub]
  calc braidExchange g1 g2 θ * braidExchange g1 g2 (-θ)
    _ = ((Real.cos (θ / 2) : ℂ) • (1 : R) + (Real.sin (θ / 2) : ℂ) • (g1 * g2)) *
        ((Real.cos (-θ / 2) : ℂ) • (1 : R) + (Real.sin (-θ / 2) : ℂ) • (g1 * g2)) := rfl
    _ = ((Real.cos (θ / 2) : ℂ) • (1 : R) + (Real.sin (θ / 2) : ℂ) • (g1 * g2)) *
        ((Real.cos (θ / 2) : ℂ) • (1 : R) + ((ofReal (-Real.sin (θ / 2))) • (g1 * g2))) := by rw [h_cos_neg, h_sin_neg]
    _ = ((Real.cos (θ / 2) : ℂ) • (1 : R) + (Real.sin (θ / 2) : ℂ) • (g1 * g2)) *
        ((Real.cos (θ / 2) : ℂ) • (1 : R) + (-Real.sin (θ / 2) : ℂ) • (g1 * g2)) := by simp only [ofReal_neg]
    _ = ((Real.cos (θ / 2) : ℂ) ^ 2) • (1 : R) - ((Real.sin (θ / 2) : ℂ) ^ 2) • ((g1 * g2) ^ 2) := h_exp
    _ = ((Real.cos (θ / 2) : ℂ) ^ 2) • (1 : R) - ((Real.sin (θ / 2) : ℂ) ^ 2) • (-1 : R) := by rw [h12_sq]
    _ = (((Real.cos (θ / 2) : ℂ) ^ 2 + (Real.sin (θ / 2) : ℂ) ^ 2) • (1 : R)) := by simp only [smul_neg, sub_neg_eq_add, ← add_smul]
    _ = 1 := by rw [h_trig_c, one_smul]

end InfoGeometry.Categorical.CuntzCliffordFibonacciBraid
