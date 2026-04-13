import InfoGeometry.Canonical.ModularSpectralWedgeBridge
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ModularSpectralConjugationBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealTomitaCore
open InfoGeometry.Canonical.ModularSpectralWedge
open InfoGeometry.Canonical.ModularSpectralWedgeBridge
open InfoGeometry.Canonical.TomitaTakesaki

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Active modular conjugation induced by the bridged wedge sign. -/
@[rep_depth transport]
noncomputable def activeModularConjugation
    (owned_epsilon _owned_P_D : EndH) : EndH :=
  (modularComplexI (E := E)) * owned_epsilon

namespace Compatibility

variable {W : HasModularSpectralWedge E}

/--
Active-sector modular conjugation law:
`K ε = J (1 - P_D)` once the active phase identity
`K = J ε` is supplied for the bridged sign.
-/
@[rep_depth transport]
theorem activeModularConjugation_eq_modular_j_mul_active
    (owned_epsilon owned_P_D : EndH)
    (comp :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.IsCompatibleWedge
        W owned_epsilon owned_P_D)
    (hActivePhase :
      modularComplexI (E := E) = (modular_j (E := E)) * owned_epsilon) :
    activeModularConjugation (E := E) owned_epsilon owned_P_D
      =
    (modular_j (E := E)) * ((1 : EndH) - owned_P_D) := by
  unfold activeModularConjugation
  rw [hActivePhase]
  calc
    ((modular_j (E := E)) * owned_epsilon) * owned_epsilon
        = (modular_j (E := E)) * (owned_epsilon * owned_epsilon) := by
            simp [mul_assoc]
    _ = (modular_j (E := E)) * ((1 : EndH) - owned_P_D) := by
          rw [InfoGeometry.Canonical.ModularSpectralWedgeBridge.IsCompatibleWedge.owned_epsilon_sq
            (W := W) owned_epsilon owned_P_D comp]

/-- The active modular conjugation annihilates the Drazin apex on the right. -/
@[rep_depth transport]
theorem activeModularConjugation_mul_P_D_eq_zero
    (owned_epsilon owned_P_D : EndH)
    (comp :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.IsCompatibleWedge
        W owned_epsilon owned_P_D)
    (hActivePhase :
      modularComplexI (E := E) = (modular_j (E := E)) * owned_epsilon) :
    activeModularConjugation (E := E) owned_epsilon owned_P_D * owned_P_D = 0 := by
  rw [activeModularConjugation_eq_modular_j_mul_active
    (E := E) (W := W) owned_epsilon owned_P_D comp hActivePhase]
  have hIdem : owned_P_D * owned_P_D = owned_P_D := by
    simpa [comp.pzero_eq] using W.PZero_idem
  have hRight : ((1 : EndH) - owned_P_D) * owned_P_D = 0 := by
    calc
      ((1 : EndH) - owned_P_D) * owned_P_D
          = owned_P_D - owned_P_D * owned_P_D := by
              simp [sub_mul]
      _ = owned_P_D - owned_P_D := by rw [hIdem]
      _ = 0 := by simp
  calc
    (modular_j (E := E)) * ((1 : EndH) - owned_P_D) * owned_P_D
        = (modular_j (E := E)) * (((1 : EndH) - owned_P_D) * owned_P_D) := by
            simp [mul_assoc]
    _ = (modular_j (E := E)) * 0 := by rw [hRight]
    _ = 0 := by simp

/--
If the apex commutes with `modular_j`, left annihilation also holds.
-/
@[rep_depth transport]
theorem P_D_mul_activeModularConjugation_eq_zero
    (owned_epsilon owned_P_D : EndH)
    (comp :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.IsCompatibleWedge
        W owned_epsilon owned_P_D)
    (hActivePhase :
      modularComplexI (E := E) = (modular_j (E := E)) * owned_epsilon)
    (hComm : Commute owned_P_D (modular_j (E := E))) :
    owned_P_D * activeModularConjugation (E := E) owned_epsilon owned_P_D = 0 := by
  rw [activeModularConjugation_eq_modular_j_mul_active
    (E := E) (W := W) owned_epsilon owned_P_D comp hActivePhase]
  have hIdem : owned_P_D * owned_P_D = owned_P_D := by
    simpa [comp.pzero_eq] using W.PZero_idem
  have hLeft : owned_P_D * ((1 : EndH) - owned_P_D) = 0 := by
    calc
      owned_P_D * ((1 : EndH) - owned_P_D)
          = owned_P_D - owned_P_D * owned_P_D := by
              simp [mul_sub]
      _ = owned_P_D - owned_P_D := by rw [hIdem]
      _ = 0 := by simp
  calc
    owned_P_D * ((modular_j (E := E)) * ((1 : EndH) - owned_P_D))
        = (owned_P_D * (modular_j (E := E))) * ((1 : EndH) - owned_P_D) := by
            simp [mul_assoc]
    _ = ((modular_j (E := E)) * owned_P_D) * ((1 : EndH) - owned_P_D) := by
          rw [hComm.eq]
    _ = (modular_j (E := E)) * (owned_P_D * ((1 : EndH) - owned_P_D)) := by
          simp [mul_assoc]
    _ = (modular_j (E := E)) * 0 := by rw [hLeft]
    _ = 0 := by simp

end Compatibility

end Core

end InfoGeometry.Canonical.ModularSpectralConjugationBridge
