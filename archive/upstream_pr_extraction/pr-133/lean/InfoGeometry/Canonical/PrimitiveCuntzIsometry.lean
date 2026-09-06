import InfoGeometry.Canonical.CuntzUHFAlgebra
import Mathlib.Tactic

open InfoGeometry.GrandUnification.UHF

noncomputable section

namespace InfoGeometry.Canonical.PrimitiveCuntzIsometry

variable {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A]
variable [UHF : CuntzIsometryData A]

/-- The left cylinder projection `P_L = S_L * S_L^*`. -/
def P_L : A := CuntzIsometryData.S_L * star CuntzIsometryData.S_L

/-- The right cylinder projection `P_R = S_R * S_R^*`. -/
def P_R : A := CuntzIsometryData.S_R * star CuntzIsometryData.S_R

/--
The primitive exactness of the Cuntz partition:
The sum of the left and right projections strictly reconstructs the identity,
leaving no topological defect or anomaly.
-/
theorem cuntz_partition_exactness : P_L (A := A) + P_R (A := A) = 1 := by
  exact CuntzIsometryData.cuntz_relation

/-- `P_L` is an idempotent projection. -/
theorem P_L_sq : P_L (A := A) * P_L (A := A) = P_L (A := A) := by
  dsimp [P_L]
  calc
    (CuntzIsometryData.S_L (A := A) * star (CuntzIsometryData.S_L (A := A))) *
        (CuntzIsometryData.S_L (A := A) * star (CuntzIsometryData.S_L (A := A)))
        = CuntzIsometryData.S_L (A := A) *
          ((star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_L (A := A)) *
            star (CuntzIsometryData.S_L (A := A))) := by
            simp only [mul_assoc]
    _ = CuntzIsometryData.S_L (A := A) * (1 * star (CuntzIsometryData.S_L (A := A))) := by
          rw [CuntzIsometryData.isometry_L]
    _ = CuntzIsometryData.S_L (A := A) * star (CuntzIsometryData.S_L (A := A)) := by
          simp

/-- `P_R` is an idempotent projection. -/
theorem P_R_sq : P_R (A := A) * P_R (A := A) = P_R (A := A) := by
  dsimp [P_R]
  calc
    (CuntzIsometryData.S_R (A := A) * star (CuntzIsometryData.S_R (A := A))) *
        (CuntzIsometryData.S_R (A := A) * star (CuntzIsometryData.S_R (A := A)))
        = CuntzIsometryData.S_R (A := A) *
          ((star (CuntzIsometryData.S_R (A := A)) * CuntzIsometryData.S_R (A := A)) *
            star (CuntzIsometryData.S_R (A := A))) := by
            simp only [mul_assoc]
    _ = CuntzIsometryData.S_R (A := A) * (1 * star (CuntzIsometryData.S_R (A := A))) := by
          rw [CuntzIsometryData.isometry_R]
    _ = CuntzIsometryData.S_R (A := A) * star (CuntzIsometryData.S_R (A := A)) := by
          simp

/--
Theorem: Primitive Exactness guarantees Orthogonality.
Because the total partition has no topological defects (`P_L + P_R = 1`),
and the operators are isometries, the cross-term `S_L^* S_R` must strictly vanish.
This is the discrete equivalent of the continuous vanishing of holonomy.
-/
theorem cuntz_orthogonality : star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A) = 0 := by
  let x : A := star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A)
  have hL :
      star (CuntzIsometryData.S_L (A := A)) * P_L (A := A) * CuntzIsometryData.S_R (A := A) = x := by
    dsimp [x, P_L]
    calc
      star (CuntzIsometryData.S_L (A := A)) *
          (CuntzIsometryData.S_L (A := A) * star (CuntzIsometryData.S_L (A := A))) *
          CuntzIsometryData.S_R (A := A)
        = (star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_L (A := A)) *
            star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A) := by
            rw [← mul_assoc, mul_assoc]
      _ = (1 : A) * star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A) := by
            rw [CuntzIsometryData.isometry_L]
      _ = star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A) := by
            simp
  have hR :
      star (CuntzIsometryData.S_L (A := A)) * P_R (A := A) * CuntzIsometryData.S_R (A := A) = x := by
    dsimp [x, P_R]
    calc
      star (CuntzIsometryData.S_L (A := A)) *
          (CuntzIsometryData.S_R (A := A) * star (CuntzIsometryData.S_R (A := A))) *
          CuntzIsometryData.S_R (A := A)
        = (star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A)) *
            (star (CuntzIsometryData.S_R (A := A)) * CuntzIsometryData.S_R (A := A)) := by
            rw [← mul_assoc, mul_assoc]
      _ = (star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A)) * (1 : A) := by
            rw [CuntzIsometryData.isometry_R]
      _ = star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A) := by
            simp
  have hx' : x = x + x := by
    change
      star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A) =
        star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A) +
          star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A)
    calc
      star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A)
          = star (CuntzIsometryData.S_L (A := A)) * 1 * CuntzIsometryData.S_R (A := A) := by
              simp
      _ = star (CuntzIsometryData.S_L (A := A)) *
            (P_L (A := A) + P_R (A := A)) * CuntzIsometryData.S_R (A := A) := by
              rw [cuntz_partition_exactness]
      _ = star (CuntzIsometryData.S_L (A := A)) * P_L (A := A) * CuntzIsometryData.S_R (A := A) +
            star (CuntzIsometryData.S_L (A := A)) * P_R (A := A) * CuntzIsometryData.S_R (A := A) := by
              rw [mul_add, add_mul]
      _ = star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A) +
            star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A) := by
              rw [hL, hR]
  have hx : x + x = x := hx'.symm
  have hzero : x + x - x = x - x := by
    rw [hx]
  have hx0 : x = 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
  exact hx0

/-- The projections are mutually exclusive (zero intersection). -/
theorem P_L_mul_P_R_eq_zero : P_L (A := A) * P_R (A := A) = 0 := by
  dsimp [P_L, P_R]
  calc
    (CuntzIsometryData.S_L (A := A) * star (CuntzIsometryData.S_L (A := A))) *
        (CuntzIsometryData.S_R (A := A) * star (CuntzIsometryData.S_R (A := A)))
      = CuntzIsometryData.S_L (A := A) *
          (star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A)) *
            star (CuntzIsometryData.S_R (A := A)) := by
          repeat rw [mul_assoc]
    _ = CuntzIsometryData.S_L (A := A) * 0 * star (CuntzIsometryData.S_R (A := A)) := by
          rw [cuntz_orthogonality]
    _ = 0 := by
          simp

end InfoGeometry.Canonical.PrimitiveCuntzIsometry
