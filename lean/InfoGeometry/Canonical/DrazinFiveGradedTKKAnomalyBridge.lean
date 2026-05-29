import InfoGeometry.Canonical.DrazinCentralChargeBridge
import InfoGeometry.Canonical.CentralChargeAnomaly
import InfoGeometry.OperatorAlgebra.TKKConformalClosure
import InfoGeometry.OperatorAlgebra.FiveGradedDefectAbsorption
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# Drazin / Five-Graded TKK Anomaly Bridge

This file bridges two already-owned anomaly languages through an explicit
calibration witness:

* the operatorial/Drazin language, where the central-charge defect is the
  intrinsic `operatorialCentralDefectShadow`;
* the TKK/five-graded language, where the anomaly is a TKK closure defect whose
  representative is absorbed in the `g_+2` memory grade.

No global index theorem is asserted.  The equality between the Drazin shadow and
the TKK closure defect is a field of `DrazinTKKAnomalyCalibration`.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinFiveGradedTKKAnomalyBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.DrazinCentralChargeBridge
open InfoGeometry.Canonical.CentralChargeAnomaly
open InfoGeometry.OperatorAlgebra.TKKConformalClosure
open InfoGeometry.OperatorAlgebra.FiveGradedDefectAbsorption
open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein

section Bridge

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

variable {L State Geometry : Type*}
variable [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable [AddCommGroup State] [Module ℝ State]
variable [AddCommGroup Geometry] [Module ℝ Geometry]

/--
Calibration between the operatorial Drazin central-charge shadow and the
TKK/five-graded anomaly surface.

`shadowReadout` is the explicit map from endomorphism-valued Drazin defect
shadow to the geometric readout codomain of the TKK closure defect.  The core
calibration field states that this readout is the supplied TKK anomaly readout.

The second field aligns the anomaly datum's closure defect with the Ricci-flux
datum's closure defect, so that the five-graded absorption witness applies to
the same defect.
-/
@[rep_depth transport]
structure DrazinTKKAnomalyCalibration
    (CIK : CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (TKK_A : AnomalyClosureDefectDatum L State Geometry)
    (TKK_R : TKKRicciFluxDatum L State Geometry)
    (G : FiveGrading L)
    (Absorp : TKKDefectAbsorbedInPlusTwo L State Geometry TKK_R G) where
  /-- Readout translating the Drazin endomorphism shadow into TKK geometry. -/
  shadowReadout : EndH → Geometry

  /-- The mapped operatorial shadow equals the supplied TKK anomaly readout. -/
  shadow_calibrates_anomaly :
    ∀ (X_L : L) (s : State),
      shadowReadout (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) =
        TKK_A.anomalyReadout X_L s

  /-- The anomaly datum and Ricci-flux datum use the same closure defect. -/
  defect_alignment :
    ∀ (X_L : L) (s : State),
      TKKClosureDefect.defect TKK_A.closureDefect X_L s =
        TKKClosureDefect.defect TKK_R.closureDefect X_L s

namespace DrazinTKKAnomalyCalibration

variable {CIK : CertifiedInverseKernel H₂}
variable {X : RealSplitKreinDiracFredholmModule A B H₂}
variable {hX : ChiralFredholmSurface X}
variable {TKK_A : AnomalyClosureDefectDatum L State Geometry}
variable {TKK_R : TKKRicciFluxDatum L State Geometry}
variable {G : FiveGrading L}
variable {Absorp : TKKDefectAbsorbedInPlusTwo L State Geometry TKK_R G}

/-- The operatorial Drazin shadow readout equals the TKK closure defect. -/
@[rep_depth transport]
theorem operatorial_shadow_eq_closure_defect
    (calib : DrazinTKKAnomalyCalibration CIK X hX TKK_A TKK_R G Absorp)
    (X_L : L)
    (s : State) :
    DrazinTKKAnomalyCalibration.shadowReadout calib
        (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) =
      TKKClosureDefect.defect (AnomalyClosureDefectDatum.closureDefect TKK_A) X_L s :=
  (DrazinTKKAnomalyCalibration.shadow_calibrates_anomaly calib X_L s).trans
    (TKK_A.anomaly_eq_defect X_L s)

/--
The operatorial Drazin shadow readout is the five-graded `g_+2` representative
readout supplied by the absorption witness.
-/
@[rep_depth transport]
theorem operatorial_shadow_eq_plusTwoReadout
    (calib : DrazinTKKAnomalyCalibration CIK X hX TKK_A TKK_R G Absorp)
    (X_L : L)
    (s : State) :
    DrazinTKKAnomalyCalibration.shadowReadout calib
        (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) =
      Absorp.plusTwoReadout (Absorp.defectToPlusTwo X_L s) :=
  (operatorial_shadow_eq_closure_defect calib X_L s).trans
    ((DrazinTKKAnomalyCalibration.defect_alignment calib X_L s).trans
      (Absorp.closureDefect_eq_plusTwo X_L s))

/-- The five-graded representative of the calibrated anomaly lies in `g_+2`. -/
@[rep_depth transport]
theorem operatorial_shadow_has_plusTwo_representative
    (_calib : DrazinTKKAnomalyCalibration CIK X hX TKK_A TKK_R G Absorp)
    (X_L : L)
    (s : State) :
    Absorp.defectToPlusTwo X_L s ∈ G.gPosTwo :=
  Absorp.defect_has_plus_two_representative X_L s

/--
If curvature is stationary, the Ricci flux is exactly the calibrated Drazin
shadow readout.
-/
@[rep_depth transport]
theorem ricciFlux_eq_operatorial_shadow_of_curvature_stationary
    (calib : DrazinTKKAnomalyCalibration CIK X hX TKK_A TKK_R G Absorp)
    (X_L : L)
    (s : State)
    (hstat :
      TKK_R.derivativeAlong.deriv TKK_R.curvatureReadout.curvature X_L s = 0) :
    TKK_R.ricciFlux X_L s =
      DrazinTKKAnomalyCalibration.shadowReadout calib
        (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) := by
  have hflux :
      TKK_R.ricciFlux X_L s =
        TKKClosureDefect.defect (TKKRicciFluxDatum.closureDefect TKK_R) X_L s := by
    rw [TKK_R.ricciFlux_def X_L s, hstat, zero_add]
  exact hflux.trans
    ((DrazinTKKAnomalyCalibration.defect_alignment calib X_L s).symm.trans
      (operatorial_shadow_eq_closure_defect calib X_L s).symm)

/-- The operatorial shadow remains Drazin defect-supported on the source lane. -/
@[rep_depth transport]
theorem operatorial_shadow_isDefectSupported :
    CertifiedInverseKernel.IsDefectSupportedK CIK
      (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) :=
  operatorialCentralDefectShadow_isDefectSupported (A := A) (B := B) CIK X hX

/-- The operatorial shadow remains central on the Drazin lane. -/
@[rep_depth transport]
theorem operatorial_shadow_isDrazinLaneCentral :
    CertifiedInverseKernel.IsDrazinLaneCentralK CIK
      (operatorialCentralDefectShadow (A := A) (B := B) CIK X hX) :=
  operatorialCentralDefectShadow_isDrazinLaneCentral (A := A) (B := B) CIK X hX

end DrazinTKKAnomalyCalibration

end Bridge

end InfoGeometry.Canonical.DrazinFiveGradedTKKAnomalyBridge
