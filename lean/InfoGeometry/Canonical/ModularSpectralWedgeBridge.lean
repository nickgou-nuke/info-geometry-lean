import InfoGeometry.Canonical.ModularSpectralWedge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ModularSpectralWedgeBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealTomitaCore
open InfoGeometry.Canonical.ModularSpectralWedge

section Bridge

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/--
Compatibility between an abstract modular spectral wedge and owned operators.
-/
@[rep_depth transport]
structure IsCompatibleWedge
    (W : HasModularSpectralWedge E)
    (owned_epsilon owned_P_D : EndH) : Prop where
  epsilon_eq : W.wedgeSign = owned_epsilon
  pzero_eq : W.PZero = owned_P_D

namespace IsCompatibleWedge

variable {W : HasModularSpectralWedge E}

/--
The owned wedge-sign square law: `owned_epsilon^2 = 1 - owned_P_D`.
-/
@[rep_depth transport]
theorem owned_epsilon_sq
    (owned_epsilon owned_P_D : EndH)
    (comp : IsCompatibleWedge W owned_epsilon owned_P_D) :
    owned_epsilon * owned_epsilon = (1 : EndH) - owned_P_D := by
  rw [← comp.epsilon_eq, ← comp.pzero_eq]
  exact W.wedgeSign_sq

/-- Right annihilation of the apex by the owned wedge sign. -/
@[rep_depth transport]
theorem owned_epsilon_mul_P_D_eq_zero
    (owned_epsilon owned_P_D : EndH)
    (comp : IsCompatibleWedge W owned_epsilon owned_P_D) :
    owned_epsilon * owned_P_D = 0 := by
  rw [← comp.epsilon_eq, ← comp.pzero_eq]
  unfold HasModularSpectralWedge.wedgeSign
  calc
    (W.PiPlus - W.PiMinus) * W.PZero
        = W.PiPlus * W.PZero - W.PiMinus * W.PZero := by
            simp [sub_mul]
    _ = 0 - 0 := by rw [W.PiPlus_PZero, W.PiMinus_PZero]
    _ = 0 := by simp

/-- Left annihilation of the apex by the owned wedge sign. -/
@[rep_depth transport]
theorem P_D_mul_owned_epsilon_eq_zero
    (owned_epsilon owned_P_D : EndH)
    (comp : IsCompatibleWedge W owned_epsilon owned_P_D) :
    owned_P_D * owned_epsilon = 0 := by
  rw [← comp.epsilon_eq, ← comp.pzero_eq]
  unfold HasModularSpectralWedge.wedgeSign
  calc
    W.PZero * (W.PiPlus - W.PiMinus)
        = W.PZero * W.PiPlus - W.PZero * W.PiMinus := by
            simp [mul_sub]
    _ = 0 - 0 := by rw [W.PZero_PiPlus, W.PZero_PiMinus]
    _ = 0 := by simp

end IsCompatibleWedge

end Bridge

end InfoGeometry.Canonical.ModularSpectralWedgeBridge
