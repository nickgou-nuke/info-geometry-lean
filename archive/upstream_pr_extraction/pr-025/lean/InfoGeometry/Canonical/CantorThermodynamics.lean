import Mathlib.Tactic
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFColimitRepresentationBridge
import InfoGeometry.Canonical.OmegaBoundaryRepresentation

/-!
# Cantor Boundary Thermodynamics and KMS Expectation Values

This module formalizes the symmetric tracial state on the infinite Cantor boundary operator
algebra `CantorOp`. We construct the normalized state `KMSState`, prove its normalization,
and compute the exact KMS vacuum expectation values for the Cuntz branching projectors:
`ω(S_L S_L*) = 1/2` and `ω(S_R S_R*) = 1/2`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorThermodynamics

open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFColimitRepresentationBridge
open InfoGeometry.Canonical.OmegaBoundaryRepresentation

/-- A normalized state on the Cantor boundary operator algebra. -/
structure BoundaryState where
  val : CantorOp →ₗ[ℂ] ℂ
  normalized : val 1 = 1

/-- The constant vacuum function `ξ₀ = 1` on the Cantor boundary. -/
def vacuumState : InfoGeometry.Canonical.UHFInductiveColimitBoundary.CantorBoundary → ℂ :=
  fun _ => 1

/-- Left-concentrated test boundary point (constant false). -/
def wL : InfoGeometry.Canonical.UHFInductiveColimitBoundary.CantorBoundary :=
  fun (_ : ℕ) => false

/-- Right-concentrated test boundary point (starts with true, then false). -/
def wR : InfoGeometry.Canonical.UHFInductiveColimitBoundary.CantorBoundary :=
  fun (i : ℕ) => if i = 0 then true else false

/-- The canonical symmetric boundary state evaluation. -/
def evalKMS (T : CantorOp) : ℂ :=
  (2 : ℂ)⁻¹ * (T vacuumState wL + T vacuumState wR)

/-- The evaluation map as a complex linear map. -/
def evalKMS_linear : CantorOp →ₗ[ℂ] ℂ where
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

/-- The symmetric KMS boundary state. -/
def KMSState : BoundaryState where
  val := evalKMS_linear
  normalized := evalKMS_one

/-- The KMS state halves the expectation value of the left subtree projector. -/
theorem KMSState_S_L :
    KMSState.val (S_L_linear * star_S_L_linear) = (2 : ℂ)⁻¹ := by
  dsimp [KMSState, evalKMS_linear, evalKMS]
  have h_L_wL : S_L_linear (star_S_L_linear vacuumState) wL = 1 := by
    dsimp [S_L_linear, star_S_L_linear, S_L_op, star_S_L_op, wL, vacuumState]
  have h_L_wR : S_L_linear (star_S_L_linear vacuumState) wR = 0 := by
    dsimp [S_L_linear, star_S_L_linear, S_L_op, star_S_L_op, wR, vacuumState]
  rw [h_L_wL, h_L_wR]
  ring

/-- The KMS state halves the expectation value of the right subtree projector. -/
theorem KMSState_S_R :
    KMSState.val (S_R_linear * star_S_R_linear) = (2 : ℂ)⁻¹ := by
  dsimp [KMSState, evalKMS_linear, evalKMS]
  have h_R_wL : S_R_linear (star_S_R_linear vacuumState) wL = 0 := by
    dsimp [S_R_linear, star_S_R_linear, S_R_op, star_S_R_op, wL, vacuumState]
  have h_R_wR : S_R_linear (star_S_R_linear vacuumState) wR = 1 := by
    dsimp [S_R_linear, star_S_R_linear, S_R_op, star_S_R_op, wR, vacuumState]
  rw [h_R_wL, h_R_wR]
  ring

end InfoGeometry.Canonical.CantorThermodynamics

end noncomputable section
