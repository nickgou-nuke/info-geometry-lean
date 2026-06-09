import Mathlib

/-!
# Trifactor Decomposition — Lean 4

For any ring R with 2 invertible:
  T³ = T  ⇒  spec(T) ⊆ {-1, 0, +1}

Projectors: P₀ = 1 - T², P₊ = ½(T²+T), P₋ = ½(T²-T)
Properties: idempotent, orthogonal, partition of unity, spectral action.
-/

noncomputable section

namespace TrifactorDecomposition

variable {R : Type*} [Ring R] [Invertible (2 : R)]
variable (T : R)
variable (h_cube : T ^ 3 = T)

/-- The Null Boundary Projector (det = 0). -/
def P_zero : R := 1 - T ^ 2

/-- The Positive Conformal Flow Projector (det = 1). -/
def P_plus : R := ⅟(2 : R) * (T ^ 2 + T)

/-- The Negative Mirror Projector (det = -1). -/
def P_minus : R := ⅟(2 : R) * (T ^ 2 - T)

/-! ## 1. Idempotent Properties (P² = P) -/

theorem P_zero_idempotent : P_zero T * P_zero T = P_zero T := by
  unfold P_zero
  calc
    (1 - T ^ 2) * (1 - T ^ 2) = 1 - 2 * T ^ 2 + T ^ 4 := by ring
    _ = 1 - 2 * T ^ 2 + T * (T ^ 3) := by ring
    _ = 1 - 2 * T ^ 2 + T * T := by rw [h_cube]
    _ = 1 - T ^ 2 := by ring

theorem P_plus_idempotent : P_plus T * P_plus T = P_plus T := by
  unfold P_plus
  calc
    (⅟(2 : R) * (T ^ 2 + T)) * (⅟(2 : R) * (T ^ 2 + T))
        = (⅟(2 : R) * ⅟(2 : R)) * (T ^ 4 + 2 * T ^ 3 + T ^ 2) := by ring
    _ = (⅟(2 : R) * ⅟(2 : R)) * (T ^ 2 + 2 * T + T ^ 2) := by rw [h_cube, ← pow_two]; ring
    _ = ⅟(2 : R) * (⅟(2 : R) * (2 * (T ^ 2 + T))) := by ring
    _ = ⅟(2 : R) * ((⅟(2 : R) * 2) * (T ^ 2 + T)) := by simp [mul_assoc]
    _ = ⅟(2 : R) * (1 * (T ^ 2 + T)) := by rw [invOf_mul_self (2 : R)]
    _ = P_plus T := by unfold P_plus; ring

theorem P_minus_idempotent : P_minus T * P_minus T = P_minus T := by
  unfold P_minus
  calc
    (⅟(2 : R) * (T ^ 2 - T)) * (⅟(2 : R) * (T ^ 2 - T))
        = (⅟(2 : R) * ⅟(2 : R)) * (T ^ 4 - 2 * T ^ 3 + T ^ 2) := by ring
    _ = (⅟(2 : R) * ⅟(2 : R)) * (T ^ 2 - 2 * T + T ^ 2) := by rw [h_cube, ← pow_two]; ring
    _ = ⅟(2 : R) * (⅟(2 : R) * (2 * (T ^ 2 - T))) := by ring
    _ = ⅟(2 : R) * ((⅟(2 : R) * 2) * (T ^ 2 - T)) := by simp [mul_assoc]
    _ = ⅟(2 : R) * (1 * (T ^ 2 - T)) := by rw [invOf_mul_self (2 : R)]
    _ = P_minus T := by unfold P_minus; ring

/-! ## 2. Mutual Orthogonality (P_i * P_j = 0) -/

theorem P_plus_P_minus_orthogonal : P_plus T * P_minus T = 0 := by
  unfold P_plus P_minus
  calc
    (⅟(2 : R) * (T ^ 2 + T)) * (⅟(2 : R) * (T ^ 2 - T))
        = (⅟(2 : R) * ⅟(2 : R)) * (T ^ 4 - T ^ 2) := by ring
    _ = (⅟(2 : R) * ⅟(2 : R)) * (T * (T ^ 3) - T ^ 2) := by ring
    _ = (⅟(2 : R) * ⅟(2 : R)) * (T * T - T ^ 2) := by rw [h_cube]
    _ = 0 := by ring

theorem P_zero_P_plus_orthogonal : P_zero T * P_plus T = 0 := by
  unfold P_zero P_plus
  calc
    (1 - T ^ 2) * (⅟(2 : R) * (T ^ 2 + T))
        = ⅟(2 : R) * (T ^ 2 + T - T ^ 4 - T ^ 3) := by ring
    _ = ⅟(2 : R) * (T ^ 2 + T - T ^ 2 - T) := by rw [h_cube, ← pow_two]; ring
    _ = 0 := by ring

/-! ## 3. Partition of Unity (P_0 + P_plus + P_minus = I) -/

theorem partition_of_unity : P_zero T + P_plus T + P_minus T = 1 := by
  unfold P_zero P_plus P_minus
  calc
    (1 - T ^ 2) + ⅟(2 : R) * (T ^ 2 + T) + ⅟(2 : R) * (T ^ 2 - T)
        = 1 - T ^ 2 + ⅟(2 : R) * (2 * T ^ 2) := by ring
    _ = 1 - T ^ 2 + (⅟(2 : R) * 2) * T ^ 2 := by simp [mul_assoc]
    _ = 1 - T ^ 2 + 1 * T ^ 2 := by rw [invOf_mul_self (2 : R)]
    _ = 1 := by ring

/-! ## 4. Spectral Action -/

theorem T_on_P_zero : T * P_zero T = 0 := by
  unfold P_zero
  calc
    T * (1 - T ^ 2) = T - T ^ 3 := by ring
    _ = T - T := by rw [h_cube]
    _ = 0 := by ring

theorem T_on_P_plus : T * P_plus T = P_plus T := by
  unfold P_plus
  calc
    T * (⅟(2 : R) * (T ^ 2 + T)) = ⅟(2 : R) * (T ^ 3 + T ^ 2) := by ring
    _ = ⅟(2 : R) * (T + T ^ 2) := by rw [h_cube]
    _ = P_plus T := by unfold P_plus; ring

theorem T_on_P_minus : T * P_minus T = -P_minus T := by
  unfold P_minus
  calc
    T * (⅟(2 : R) * (T ^ 2 - T)) = ⅟(2 : R) * (T ^ 3 - T ^ 2) := by ring
    _ = ⅟(2 : R) * (T - T ^ 2) := by rw [h_cube]
    _ = -(⅟(2 : R) * (T ^ 2 - T)) := by
      simp [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_comm, add_left_comm]

end TrifactorDecomposition
