import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Canonical.SuperchargeGapHessianBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ChiralHodgeLichnerowiczBridge

Thin transport bridge projecting the already-owned root supercharge
Lichnerowicz closure onto the `ε`-chiral sectors.
-/

namespace InfoGeometry.Canonical.ChiralHodgeLichnerowiczBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.ChiralHodgeDecomposition
open InfoGeometry.Canonical.SuperchargeGapHessianBridge
open InfoGeometry.Canonical.BogoliubovTransport

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- The transported root Lichnerowicz closure projected to the `ε = +1` sector. -/
@[rep_depth transport]
theorem root_supercharge_lichnerowicz_plus_sector
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    (spectralChiralPlusProjector (E := E)).comp
        ((deriv
            (fun t : ℝ =>
              deriv
                (fun s : ℝ =>
                  InfoGeometry.Canonical.SuperchargeTransportBridge.transportedParitySupercharge
                    (E := E) V s)
                t)
            0).comp
          (spectralChiralPlusProjector (E := E)))
      =
    (spectralChiralPlusProjector (E := E)).comp
        (((operatorInformationMetricPart (E := E) V.connectionGenerator V.connectionGenerator
            (modular_j (E := E)))
          + ((2 : ℝ)⁻¹) •
              (operatorInformationCurvaturePart (E := E) V.connectionGenerator V.connectionGenerator
                (modular_j (E := E)))).comp
          (spectralChiralPlusProjector (E := E))) := by
  have hRoot :
      deriv
          (fun t : ℝ =>
            deriv
              (fun s : ℝ =>
                InfoGeometry.Canonical.SuperchargeTransportBridge.transportedParitySupercharge
                  (E := E) V s)
              t)
          0
        =
      operatorInformationMetricPart (E := E) V.connectionGenerator V.connectionGenerator (modular_j (E := E))
        + ((2 : ℝ)⁻¹) •
            operatorInformationCurvaturePart (E := E) V.connectionGenerator V.connectionGenerator
              (modular_j (E := E)) :=
    InfoGeometry.Canonical.SuperchargeGapHessianBridge.root_supercharge_lichnerowicz_closure (E := E) V
  simpa only [ContinuousLinearMap.comp_assoc] using
    congrArg
      (fun T : EndH =>
        (spectralChiralPlusProjector (E := E)).comp
          (T.comp (spectralChiralPlusProjector (E := E))))
      hRoot

/-- The transported root Lichnerowicz closure projected to the `ε = -1` sector. -/
@[rep_depth transport]
theorem root_supercharge_lichnerowicz_minus_sector
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    (spectralChiralMinusProjector (E := E)).comp
        ((deriv
            (fun t : ℝ =>
              deriv
                (fun s : ℝ =>
                  InfoGeometry.Canonical.SuperchargeTransportBridge.transportedParitySupercharge
                    (E := E) V s)
                t)
            0).comp
          (spectralChiralMinusProjector (E := E)))
      =
    (spectralChiralMinusProjector (E := E)).comp
        (((operatorInformationMetricPart (E := E) V.connectionGenerator V.connectionGenerator
            (modular_j (E := E)))
          + ((2 : ℝ)⁻¹) •
              (operatorInformationCurvaturePart (E := E) V.connectionGenerator V.connectionGenerator
                (modular_j (E := E)))).comp
          (spectralChiralMinusProjector (E := E))) := by
  have hRoot :
      deriv
          (fun t : ℝ =>
            deriv
              (fun s : ℝ =>
                InfoGeometry.Canonical.SuperchargeTransportBridge.transportedParitySupercharge
                  (E := E) V s)
              t)
          0
        =
      operatorInformationMetricPart (E := E) V.connectionGenerator V.connectionGenerator (modular_j (E := E))
        + ((2 : ℝ)⁻¹) •
            operatorInformationCurvaturePart (E := E) V.connectionGenerator V.connectionGenerator
              (modular_j (E := E)) :=
    InfoGeometry.Canonical.SuperchargeGapHessianBridge.root_supercharge_lichnerowicz_closure (E := E) V
  simpa only [ContinuousLinearMap.comp_assoc] using
    congrArg
      (fun T : EndH =>
        (spectralChiralMinusProjector (E := E)).comp
          (T.comp (spectralChiralMinusProjector (E := E))))
      hRoot

end Core

end InfoGeometry.Canonical.ChiralHodgeLichnerowiczBridge
