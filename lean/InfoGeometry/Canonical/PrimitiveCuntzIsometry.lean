import InfoGeometry.Canonical.CuntzUHFAlgebra

open InfoGeometry.GrandUnification.UHF

noncomputable section

namespace InfoGeometry.Canonical.PrimitiveCuntzIsometry

variable {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A]
variable [UHF : UHFAlgebra A]

/-- The left cylinder projection `P_L = S_L * S_L^*`. -/
def P_L : A := UHFAlgebra.S_L * star UHFAlgebra.S_L

/-- The right cylinder projection `P_R = S_R * S_R^*`. -/
def P_R : A := UHFAlgebra.S_R * star UHFAlgebra.S_R

/--
The primitive exactness of the Cuntz partition:
The sum of the left and right projections strictly reconstructs the identity,
leaving no topological defect or anomaly.
-/
theorem cuntz_partition_exactness : P_L (A := A) + P_R (A := A) = 1 := by
  exact UHFAlgebra.cuntz_relation

/-- `P_L` is an idempotent projection. -/
theorem P_L_sq : P_L (A := A) * P_L (A := A) = P_L (A := A) := by
  dsimp [P_L]
  calc
    (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_L (A := A))) * (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_L (A := A)))
      = UHFAlgebra.S_L (A := A) * (star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_L (A := A)) * star (UHFAlgebra.S_L (A := A)) := by simp [mul_assoc]
    _ = UHFAlgebra.S_L (A := A) * 1 * star (UHFAlgebra.S_L (A := A)) := by rw [UHFAlgebra.isometry_L]
    _ = UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_L (A := A)) := by rw [mul_one]

/-- `P_R` is an idempotent projection. -/
theorem P_R_sq : P_R (A := A) * P_R (A := A) = P_R (A := A) := by
  dsimp [P_R]
  calc
    (UHFAlgebra.S_R (A := A) * star (UHFAlgebra.S_R (A := A))) * (UHFAlgebra.S_R (A := A) * star (UHFAlgebra.S_R (A := A)))
      = UHFAlgebra.S_R (A := A) * (star (UHFAlgebra.S_R (A := A)) * UHFAlgebra.S_R (A := A)) * star (UHFAlgebra.S_R (A := A)) := by simp [mul_assoc]
    _ = UHFAlgebra.S_R (A := A) * 1 * star (UHFAlgebra.S_R (A := A)) := by rw [UHFAlgebra.isometry_R]
    _ = UHFAlgebra.S_R (A := A) * star (UHFAlgebra.S_R (A := A)) := by rw [mul_one]

/--
Theorem: Primitive Exactness guarantees Orthogonality.
Because the total partition has no topological defects (`P_L + P_R = 1`),
and the operators are isometries, the cross-term `S_L^* S_R` must strictly vanish.
This is the discrete equivalent of the continuous vanishing of holonomy.
-/
theorem cuntz_orthogonality : star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_R (A := A) = 0 := by
  have h1 : star (UHFAlgebra.S_L (A := A)) * (P_L (A := A) + P_R (A := A)) = star (UHFAlgebra.S_L (A := A)) * 1 := by
    rw [cuntz_partition_exactness]
  rw [mul_add, mul_one] at h1
  have h2 : star (UHFAlgebra.S_L (A := A)) * P_L (A := A) = star (UHFAlgebra.S_L (A := A)) := by
    dsimp [P_L]
    calc
      star (UHFAlgebra.S_L (A := A)) * (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_L (A := A)))
        = (star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_L (A := A)) * star (UHFAlgebra.S_L (A := A)) := by simp [mul_assoc]
      _ = 1 * star (UHFAlgebra.S_L (A := A)) := by rw [UHFAlgebra.isometry_L]
      _ = star (UHFAlgebra.S_L (A := A)) := by rw [one_mul]
  rw [h2] at h1
  have h3 : star (UHFAlgebra.S_L (A := A)) * P_R (A := A) = 0 := by
    calc
      star (UHFAlgebra.S_L (A := A)) * P_R (A := A)
        = star (UHFAlgebra.S_L (A := A)) + star (UHFAlgebra.S_L (A := A)) * P_R (A := A) - star (UHFAlgebra.S_L (A := A)) := by abel
      _ = star (UHFAlgebra.S_L (A := A)) - star (UHFAlgebra.S_L (A := A)) := by rw [h1]
      _ = 0 := by abel
  dsimp [P_R] at h3
  have h4 : star (UHFAlgebra.S_L (A := A)) * (UHFAlgebra.S_R (A := A) * star (UHFAlgebra.S_R (A := A))) * UHFAlgebra.S_R (A := A) = 0 * UHFAlgebra.S_R (A := A) := by
    rw [h3]
  rw [zero_mul] at h4
  have h5 : star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_R (A := A) * (star (UHFAlgebra.S_R (A := A)) * UHFAlgebra.S_R (A := A)) = 0 := by
    calc
      star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_R (A := A) * (star (UHFAlgebra.S_R (A := A)) * UHFAlgebra.S_R (A := A))
        = star (UHFAlgebra.S_L (A := A)) * (UHFAlgebra.S_R (A := A) * star (UHFAlgebra.S_R (A := A))) * UHFAlgebra.S_R (A := A) := by simp [mul_assoc]
      _ = 0 := h4
  rw [UHFAlgebra.isometry_R, mul_one] at h5
  exact h5

/-- The projections are mutually exclusive (zero intersection). -/
theorem P_L_mul_P_R_eq_zero : P_L (A := A) * P_R (A := A) = 0 := by
  dsimp [P_L, P_R]
  calc
    (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_L (A := A))) * (UHFAlgebra.S_R (A := A) * star (UHFAlgebra.S_R (A := A)))
      = UHFAlgebra.S_L (A := A) * (star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_R (A := A)) * star (UHFAlgebra.S_R (A := A)) := by simp [mul_assoc]
    _ = UHFAlgebra.S_L (A := A) * 0 * star (UHFAlgebra.S_R (A := A)) := by rw [cuntz_orthogonality]
    _ = 0 := by simp

end InfoGeometry.Canonical.PrimitiveCuntzIsometry
