import InfoGeometry.Canonical.ModularSpectralWedgeBridge
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.ProjectorEquivariance
import InfoGeometry.Canonical.WindingOrbitClosure
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ModularSpectralConjugationBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealTomitaCore
open InfoGeometry.Canonical.ModularSpectralWedge
open InfoGeometry.Canonical.ModularSpectralWedgeBridge
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.WindingOrbitClosure

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
  (clockAxis E) * owned_epsilon

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
      clockAxis E = (modular_j (E := E)) * owned_epsilon) :
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
      clockAxis E = (modular_j (E := E)) * owned_epsilon) :
    activeModularConjugation (E := E) owned_epsilon owned_P_D * owned_P_D = 0 := by
  rw [activeModularConjugation_eq_modular_j_mul_active
    (E := E) (W := W) owned_epsilon owned_P_D comp hActivePhase]
  have hIdem : owned_P_D * owned_P_D = owned_P_D := by
    simpa [comp.2] using W.PZero_idem
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
      clockAxis E = (modular_j (E := E)) * owned_epsilon)
    (hComm : Commute owned_P_D (modular_j (E := E))) :
    owned_P_D * activeModularConjugation (E := E) owned_epsilon owned_P_D = 0 := by
  rw [activeModularConjugation_eq_modular_j_mul_active
    (E := E) (W := W) owned_epsilon owned_P_D comp hActivePhase]
  have hIdem : owned_P_D * owned_P_D = owned_P_D := by
    simpa [comp.2] using W.PZero_idem
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

/--
Certified-kernel comparison theorem:
if the bridged apex is the property spectral complement `Q₀`,
then active modular conjugation is exactly `J * P_D` on the regular lane.
-/
@[rep_depth transport]
theorem activeModularConjugation_eq_modular_j_mul_spectralProjector
    (CIK : CertifiedInverseKernel H₂)
    (owned_epsilon : EndH)
    (comp :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.IsCompatibleWedge
        W owned_epsilon CIK.spectralComplementaryProjector)
    (hActivePhase :
      clockAxis E = (modular_j (E := E)) * owned_epsilon) :
    activeModularConjugation (E := E) owned_epsilon CIK.spectralComplementaryProjector
      =
    (modular_j (E := E)) * CIK.spectralProjector := by
  calc
    activeModularConjugation (E := E) owned_epsilon CIK.spectralComplementaryProjector
        = (modular_j (E := E)) * ((1 : EndH) - CIK.spectralComplementaryProjector) := by
            exact activeModularConjugation_eq_modular_j_mul_active
              (E := E) (W := W) owned_epsilon CIK.spectralComplementaryProjector comp hActivePhase
    _ = (modular_j (E := E)) * CIK.spectralProjector := by
          simp [CertifiedInverseKernel.spectralComplementaryProjector]

/--
Owned active-phase identity on the projector-first lane:
`K = J * (P₊ - P₋)`.
-/
@[rep_depth transport]
theorem clockAxis_eq_modular_j_mul_modularSign :
    clockAxis E
      =
    (modular_j (E := E))
      * InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E) := by
  calc
    clockAxis E
        = (modular_j (E := E)) * (spectral_epsilon (E := E)) := by
            unfold InfoGeometry.Canonical.WindingOrbitClosure.clockAxis
            simp [ContinuousLinearMap.mul_def]
    _ = (modular_j (E := E))
          * InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E) := by
            rw [InfoGeometry.Canonical.ProjectorEquivariance.spectral_epsilon_eq_modularSign (E := E)]

/--
Projector-first specialization of the property-kernel comparison theorem:
if the bridged wedge sign is `P₊ - P₋`, active modular conjugation is exactly
`J * P_D` on the regular lane.
-/
@[rep_depth transport]
theorem activeModularConjugation_eq_modular_j_mul_spectralProjector_of_modularSign
    (CIK : CertifiedInverseKernel H₂)
    (comp :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.IsCompatibleWedge
        W (InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E))
          CIK.spectralComplementaryProjector) :
    activeModularConjugation (E := E)
      (InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E))
      CIK.spectralComplementaryProjector
      =
    (modular_j (E := E)) * CIK.spectralProjector := by
  exact activeModularConjugation_eq_modular_j_mul_spectralProjector
    (E := E) (W := W) CIK
    (InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E))
    comp
    (clockAxis_eq_modular_j_mul_modularSign (E := E))

end Compatibility

end Core

end InfoGeometry.Canonical.ModularSpectralConjugationBridge
