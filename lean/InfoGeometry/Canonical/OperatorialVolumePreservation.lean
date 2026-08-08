import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.RelativeModularBlockDiagonalCore
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic.Abel

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialVolumePreservation

Operatorial highest-form volume transport on the doubled real Krein carrier.

This file keeps the construction strictly in bounded endomorphism algebra:
- left/right operatorial Maurer forms,
- bi-Maurer volume drift,
- active/apex projector quarantine for drift blocks,
- and a Krein-isometric Bogoliubov transport closure property.
-/

namespace InfoGeometry.Canonical.OperatorialVolumePreservation

open InfoGeometry.Krein
open InfoGeometry.Canonical.RelativeModularBlockDiagonalCore

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Highest-form operator on the doubled Krein carrier (operatorial volume form). -/
noncomputable def volumeOperator (Ωtop : EndH) : EndH := Ωtop

/-- Left operatorial Maurer form `Θ_L = U⁻¹ \dot U`. -/
noncomputable def leftMaurerForm (Uinv Udot : EndH) : EndH := Uinv * Udot

/-- Right operatorial Maurer form `Θ_R = \dot U U⁻¹`. -/
noncomputable def rightMaurerForm (Udot Uinv : EndH) : EndH := Udot * Uinv

/--
Bi-Maurer highest-form drift:
`D_vol(V) = \dot V + Θ_L V - V Θ_R`.
-/
noncomputable def biMaurerVolumeDrift
    (Vdot ΘL ΘR V : EndH) : EndH :=
  Vdot + ΘL * V - V * ΘR

/-- Operatorial volume preservation means vanishing bi-Maurer highest-form drift. -/
def IsBiMaurerVolumePreserving
    (Vdot ΘL ΘR V : EndH) : Prop :=
  biMaurerVolumeDrift Vdot ΘL ΘR V = 0

/-- Active-lane compression of an operator by the Drazin spectral projector. -/
noncomputable def activeVolumeOperator
    (CIK : CertifiedInverseKernel H₂) (V : EndH) : EndH :=
  CIK.spectralProjector * V * CIK.spectralProjector

/-- Apex/kernel-lane compression of an operator by the complementary projector. -/
noncomputable def apexVolumeOperator
    (CIK : CertifiedInverseKernel H₂) (V : EndH) : EndH :=
  CIK.spectralComplementaryProjector * V * CIK.spectralComplementaryProjector

-- theorem-class: closure
omit [CompleteSpace E] in
theorem biMaurerVolumeDrift_eq_zero_of_transportLaw
    {Vdot ΘL ΘR V : EndH}
    (hDyn : Vdot = V * ΘR - ΘL * V) :
    biMaurerVolumeDrift Vdot ΘL ΘR V = 0 := by
  unfold biMaurerVolumeDrift
  rw [hDyn]
  abel

@[rep_depth transport]
-- theorem-class: bridge
theorem biMaurerVolumeDrift_mixed_blocks_vanish_of_commute_active
    (CIK : CertifiedInverseKernel H₂)
    (Vdot ΘL ΘR V : EndH)
    (hComm : Commute CIK.spectralProjector (biMaurerVolumeDrift Vdot ΘL ΘR V)) :
    CIK.spectralComplementaryProjector
        * biMaurerVolumeDrift Vdot ΘL ΘR V
        * CIK.spectralProjector = 0
      ∧
    CIK.spectralProjector
        * biMaurerVolumeDrift Vdot ΘL ΘR V
        * CIK.spectralComplementaryProjector = 0 := by
  have hP : CIK.spectralProjector * CIK.spectralProjector = CIK.spectralProjector :=
    CIK.spectralProjector_idempotent
  have hCore :=
    block_diagonal_of_commute_idempotent
      (E := E)
      (P := CIK.spectralProjector)
      (R := biMaurerVolumeDrift Vdot ΘL ΘR V)
      hP
      hComm
  constructor
  · calc
      CIK.spectralComplementaryProjector
          * biMaurerVolumeDrift Vdot ΘL ΘR V
          * CIK.spectralProjector
          =
        ((1 : EndH) - CIK.spectralProjector)
          * biMaurerVolumeDrift Vdot ΘL ΘR V
          * CIK.spectralProjector := by
            rw [CertifiedInverseKernel.spectralComplementaryProjector,
              CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
      _ = 0 := hCore.1
  · calc
      CIK.spectralProjector
          * biMaurerVolumeDrift Vdot ΘL ΘR V
          * CIK.spectralComplementaryProjector
          =
        CIK.spectralProjector
          * biMaurerVolumeDrift Vdot ΘL ΘR V
          * ((1 : EndH) - CIK.spectralProjector) := by
            rw [CertifiedInverseKernel.spectralComplementaryProjector,
              CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
      _ = 0 := hCore.2

@[rep_depth transport, capstone]
-- theorem-class: closure
theorem volumePreserving_of_bogoliubov_kreinIsometry
    (U Uinv Udot V Vdot : EndH)
    (hIso : KreinSpace.IsKreinIsometry (H := H₂) U)
    (hInv : Uinv = KreinSpace.kreinAdjoint (H := H₂) U)
    (hDyn :
      Vdot =
        V * rightMaurerForm Udot Uinv
          - leftMaurerForm Uinv Udot * V) :
    IsBiMaurerVolumePreserving
        Vdot
        (leftMaurerForm Uinv Udot)
        (rightMaurerForm Udot Uinv)
        V
      ∧
    Uinv * U = (1 : EndH) := by
  have hLeftAdj :
      (KreinSpace.kreinAdjoint (H := H₂) U).comp U = (ContinuousLinearMap.id ℝ H₂) :=
    (KreinSpace.isKreinIsometry_iff_star_comp_self (H := H₂) U).1 hIso
  have hLeftAdjMul : (KreinSpace.kreinAdjoint (H := H₂) U) * U = (1 : EndH) := by
    change (KreinSpace.kreinAdjoint (H := H₂) U).comp U = (ContinuousLinearMap.id ℝ H₂)
    exact hLeftAdj
  have hLeftInv : Uinv * U = (1 : EndH) := by
    calc
      Uinv * U = (KreinSpace.kreinAdjoint (H := H₂) U) * U := by
        rw [hInv]
      _ = (1 : EndH) := hLeftAdjMul
  refine ⟨?_, hLeftInv⟩
  unfold IsBiMaurerVolumePreserving leftMaurerForm rightMaurerForm
  exact biMaurerVolumeDrift_eq_zero_of_transportLaw (hDyn := hDyn)

end Core

end InfoGeometry.Canonical.OperatorialVolumePreservation
