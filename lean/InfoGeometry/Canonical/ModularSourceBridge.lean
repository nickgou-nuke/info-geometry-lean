import InfoGeometry.Canonical.ObserverDefect
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ModularSourceBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.ObserverDefect

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Baseline modular generator packaged with Drazin-cut compatibility.
-/
structure BackgroundModularFlow (CIK : CertifiedInverseKernel H₂) where
  K0 : EndH
  commutesQ0 : Commute K0 CIK.spectralComplementaryProjector

/--
Sourced modular generator: baseline plus defect residual source term.
-/
noncomputable def sourcedModularGenerator
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK) : EndH :=
  flow.K0 + observerDefectResidual CIK obs

/--
Quarantine bridge: adding defect source preserves the Drazin cut.
-/
theorem sourcedModularGenerator_respects_spectral_cut
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK) :
    Commute (sourcedModularGenerator CIK obs flow) CIK.spectralComplementaryProjector := by
  have hDef :
      Commute (observerDefectResidual CIK obs) CIK.spectralComplementaryProjector :=
    observerDefectResidual_commutes_complementaryProjector (CIK := CIK) (obs := obs)
  simpa [sourcedModularGenerator] using (Commute.add_left flow.commutesQ0 hDef)

/--
Bulk invariance: any lane orthogonal to `Q₀` does not see the defect source.
-/
theorem sourcedModularGenerator_bulk_invariant
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (P : EndH)
    (hPQ0 : P * CIK.spectralComplementaryProjector = 0) :
    P * sourcedModularGenerator CIK obs flow * P = P * flow.K0 * P := by
  let Z := observerDefectResidual CIK obs
  have hPZP : P * Z * P = 0 := by
    unfold Z observerDefectResidual
    calc
      P *
          (CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
            CIK.spectralComplementaryProjector) *
        P
          =
        ((P * CIK.spectralComplementaryProjector) * observerOrientationResidual CIK obs *
            CIK.spectralComplementaryProjector) * P := by
            simp [mul_assoc]
      _ = 0 := by simp [hPQ0]
  calc
    P * sourcedModularGenerator CIK obs flow * P
      = P * (flow.K0 + Z) * P := by rfl
    _ = P * flow.K0 * P + P * Z * P := by
          simp [mul_add, add_mul, mul_assoc]
    _ = P * flow.K0 * P := by simp [hPZP]

/--
Boundary excitation: the `Q₀` lane absorbs the sourced defect term.
-/
theorem sourcedModularGenerator_boundary_excitation
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK) :
    let Q0 := CIK.spectralComplementaryProjector
    Q0 * sourcedModularGenerator CIK obs flow * Q0
      = Q0 * flow.K0 * Q0 + observerDefectResidual CIK obs := by
  let Q0 := CIK.spectralComplementaryProjector
  have hDef := observerDefectResidual_isDefectSupported (CIK := CIK) (obs := obs)
  have hLeft : Q0 * observerDefectResidual CIK obs = observerDefectResidual CIK obs := by
    change CIK.spectralComplementaryProjector * observerDefectResidual CIK obs =
      observerDefectResidual CIK obs
    exact hDef.1
  have hRight : observerDefectResidual CIK obs * Q0 = observerDefectResidual CIK obs := by
    change observerDefectResidual CIK obs * CIK.spectralComplementaryProjector =
      observerDefectResidual CIK obs
    exact hDef.2
  have hQ0ZQ0 :
      Q0 * observerDefectResidual CIK obs * Q0 = observerDefectResidual CIK obs := by
    calc
      Q0 * observerDefectResidual CIK obs * Q0
          = (Q0 * observerDefectResidual CIK obs) * Q0 := by rw [mul_assoc]
      _ = observerDefectResidual CIK obs * Q0 := by rw [hLeft]
      _ = observerDefectResidual CIK obs := hRight
  calc
    Q0 * sourcedModularGenerator CIK obs flow * Q0
      = Q0 * (flow.K0 + observerDefectResidual CIK obs) * Q0 := by rfl
    _ = Q0 * flow.K0 * Q0 + Q0 * observerDefectResidual CIK obs * Q0 := by
          simp [mul_add, add_mul, mul_assoc]
    _ = Q0 * flow.K0 * Q0 + observerDefectResidual CIK obs := by simp [hQ0ZQ0]

end Core

end InfoGeometry.Canonical.ModularSourceBridge
