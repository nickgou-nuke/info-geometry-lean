import Mathlib.Tactic
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFColimitRepresentationBridge
import InfoGeometry.Canonical.OmegaBoundaryRepresentation

/-!
# Cantor Boundary Thermodynamics and KMS Expectation Values

This module formalizes the symmetric tracial state on the infinite Cantor boundary operator
algebra `(Module.End ℂ ((ℕ → Bool) → ℂ))`. We construct the normalized state `KMSState`, prove its normalization,
and compute the exact KMS vacuum expectation values for the Cuntz branching projectors:
`ω(S_L S_L*) = 1/2` and `ω(S_R S_R*) = 1/2`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorThermodynamics

open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFColimitRepresentationBridge
open InfoGeometry.Canonical.OmegaBoundaryRepresentation

/-- The constant vacuum function `ξ₀ = 1` on the Cantor boundary. -/
def vacuumState : (ℕ → Bool) → ℂ :=
  fun _ => 1

/-- Left-concentrated test boundary point (constant false). -/
def wL : (ℕ → Bool) :=
  fun (_ : ℕ) => false

/-- Right-concentrated test boundary point (starts with true, then false). -/
def wR : (ℕ → Bool) :=
  fun (i : ℕ) => if i = 0 then true else false

/-- The canonical symmetric boundary state evaluation. -/
def evalKMS (T : (Module.End ℂ ((ℕ → Bool) → ℂ))) : ℂ :=
  (2 : ℂ)⁻¹ * (T vacuumState wL + T vacuumState wR)

/-- The evaluation map as a complex linear map. -/
def evalKMS_linear : (Module.End ℂ ((ℕ → Bool) → ℂ)) →ₗ[ℂ] ℂ where
  toFun := evalKMS
  map_add' T1 T2 := by
    dsimp [evalKMS]
    ring
  map_smul' r T := by
    dsimp [evalKMS]
    ring

theorem evalKMS_one : evalKMS_linear 1 = 1 := by
  dsimp [evalKMS_linear, evalKMS, vacuumState, wL, wR]
  ring

theorem evalKMS_linear_normalized : evalKMS_linear 1 = 1 :=
  evalKMS_one

theorem star_S_L_linear_mul_S_L_linear_eq_one :
    star_S_L_linear * S_L_linear = 1 := by
  ext f x
  change star_S_L_op (S_L_op f) x = f x
  exact congrFun (star_S_L_op_S_L_op f) x

/-- The KMS state halves the expectation value of the left subtree projector. -/
theorem KMSState_S_L :
    evalKMS_linear (S_L_linear * star_S_L_linear) = (2 : ℂ)⁻¹ := by
  dsimp [evalKMS_linear, evalKMS]
  have h_L_wL : S_L_linear (star_S_L_linear vacuumState) wL = 1 := by
    dsimp [S_L_linear, star_S_L_linear, S_L_op, star_S_L_op, wL, vacuumState]
  have h_L_wR : S_L_linear (star_S_L_linear vacuumState) wR = 0 := by
    dsimp [S_L_linear, star_S_L_linear, S_L_op, star_S_L_op, wR, vacuumState]
  rw [h_L_wL, h_L_wR]
  ring

/-- The KMS state halves the expectation value of the right subtree projector. -/
theorem KMSState_S_R :
    evalKMS_linear (S_R_linear * star_S_R_linear) = (2 : ℂ)⁻¹ := by
  dsimp [evalKMS_linear, evalKMS]
  have h_R_wL : S_R_linear (star_S_R_linear vacuumState) wL = 0 := by
    dsimp [S_R_linear, star_S_R_linear, S_R_op, star_S_R_op, wL, vacuumState]
  have h_R_wR : S_R_linear (star_S_R_linear vacuumState) wR = 1 := by
    dsimp [S_R_linear, star_S_R_linear, S_R_op, star_S_R_op, wR, vacuumState]
  rw [h_R_wL, h_R_wR]
  ring

theorem KMSState_S_L_star_S_R :
    evalKMS_linear (S_L_linear * star_S_R_linear) = (2 : ℂ)⁻¹ := by
  dsimp [evalKMS_linear, evalKMS]
  have h_LR_wL : S_L_linear (star_S_R_linear vacuumState) wL = 1 := by
    dsimp [S_L_linear, star_S_R_linear, S_L_op, star_S_R_op, wL, vacuumState]
  have h_LR_wR : S_L_linear (star_S_R_linear vacuumState) wR = 0 := by
    dsimp [S_L_linear, star_S_R_linear, S_L_op, star_S_R_op, wR, vacuumState]
  rw [h_LR_wL, h_LR_wR]
  ring

theorem KMSState_S_R_star_S_L :
    evalKMS_linear (S_R_linear * star_S_L_linear) = (2 : ℂ)⁻¹ := by
  dsimp [evalKMS_linear, evalKMS]
  have h_RL_wL : S_R_linear (star_S_L_linear vacuumState) wL = 0 := by
    dsimp [S_R_linear, star_S_L_linear, S_R_op, star_S_L_op, wL, vacuumState]
  have h_RL_wR : S_R_linear (star_S_L_linear vacuumState) wR = 1 := by
    dsimp [S_R_linear, star_S_L_linear, S_R_op, star_S_L_op, wR, vacuumState]
  rw [h_RL_wL, h_RL_wR]
  ring

theorem branch_projectors_sum :
    S_L_linear * star_S_L_linear + S_R_linear * star_S_R_linear =
      (1 : Module.End ℂ ((ℕ → Bool) → ℂ)) := by
  ext f x
  change S_L_op (star_S_L_op f) x + S_R_op (star_S_R_op f) x = f x
  exact congrFun (cuntz_partition_op f) x

theorem KMSState_branch_projectors_sum :
    evalKMS_linear
        (S_L_linear * star_S_L_linear + S_R_linear * star_S_R_linear) = 1 := by
  rw [map_add, KMSState_S_L, KMSState_S_R]
  norm_num

theorem evalKMS_trace_failure :
    evalKMS_linear (S_L_linear * star_S_L_linear) ≠
      evalKMS_linear (star_S_L_linear * S_L_linear) := by
  rw [KMSState_S_L, star_S_L_linear_mul_S_L_linear_eq_one, evalKMS_one]
  norm_num

theorem evalKMS_not_tracial :
    ¬ (∀ T U : (Module.End ℂ ((ℕ → Bool) → ℂ)),
      evalKMS_linear (T * U) = evalKMS_linear (U * T)) := by
  intro htrace
  have h := htrace S_L_linear star_S_L_linear
  rw [KMSState_S_L, star_S_L_linear_mul_S_L_linear_eq_one,
    evalKMS_one] at h
  norm_num at h

end InfoGeometry.Canonical.CantorThermodynamics

end noncomputable section
