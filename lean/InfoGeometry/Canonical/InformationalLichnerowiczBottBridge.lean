import InfoGeometry.Canonical.GrandSynthesisBott
import InfoGeometry.Canonical.InformationalLichnerowicz
import InfoGeometry.Canonical.AnalyticalIndexCore
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.InformationalLichnerowiczBottBridge

Thin descent bridge from the owned operatorial transport Lichnerowicz lane
(`InformationalLichnerowicz`) to the Bott capstone closure witness
`LichnerowiczBalancedCl11`.

This file does not add a new ontology. It only packages the precise
compatibility assumptions required to route the transport lane into the Bott
presentation.
-/

namespace InfoGeometry.Canonical.InformationalLichnerowiczBottBridge

open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.GrandSynthesis
open InfoGeometry.Canonical.InformationalLichnerowicz
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Krein

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Compatibility data needed to descend the operatorial transport Lichnerowicz lane
to the Bott `LichnerowiczBalancedCl11` witness.
-/
@[rep_depth transport]
def InformationalLichnerowiczBottCompatibility
    (V : BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂) : Prop :=
  IST.D.comp IST.D
      =
    deriv (fun t => deriv (fun s => quasilatticeDirac V IST.D s) t) 0 ∧
  operatorInformationMetricPart
      V.connectionGenerator
      V.connectionGenerator
      IST.D
    =
  -(ContinuousLinearMap.id ℝ H₂)

/--
Under transport compatibility, the spectral Dirac square closes to `-Id`.
-/
@[rep_depth transport]
theorem spectralDirac_sq_eq_neg_id_of_operatorialTransport
    (V : BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility V IST) :
    IST.D.comp IST.D
      =
    -(ContinuousLinearMap.id ℝ H₂) := by
  calc
    IST.D.comp IST.D
      =
    deriv (fun t => deriv (fun s => quasilatticeDirac V IST.D s) t) 0 :=
      hCompat.1
    _ =
    operatorInformationMetricPart
        V.connectionGenerator
        V.connectionGenerator
        IST.D := by
          simpa using
            (deriv2_quasilatticeDirac_at_zero_eq_operatorInformationMetricPart
              (V := V) (D := IST.D))
    _ = -(ContinuousLinearMap.id ℝ H₂) :=
      hCompat.2

/--
Bott-balanced closure derived from the operatorial transport Lichnerowicz lane.
-/
@[rep_depth transport]
theorem lichnerowiczBalancedCl11_of_operatorialTransport
    (V : BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility V IST) :
    LichnerowiczBalancedCl11 (A := E) IST := by
  unfold LichnerowiczBalancedCl11
  have hSqCLM :
      IST.D.comp IST.D = -(ContinuousLinearMap.id ℝ H₂) :=
    spectralDirac_sq_eq_neg_id_of_operatorialTransport
      (V := V) (IST := IST) hCompat
  have hSqLinear :
      (spectralDiracLinear IST).comp (spectralDiracLinear IST)
        = -(LinearMap.id : Endomorphism H₂) := by
    simpa [spectralDiracLinear] using
      congrArg ContinuousLinearMap.toLinearMap hSqCLM
  have hSqZero :
      (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST))
        =
      0 :=
    InfoGeometry.Canonical.AnalyticalIndex.cl11_bottDirac_sq_eq_zero_of_dirac_sq_eq_neg_id
      (E := E) (F := H₂) (Dn := spectralDiracLinear IST)
      hSqLinear
  calc
    cl11BottLaplacian (E := E) (spectralDiracLinear IST)
      =
    (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
      (cl11BottDirac (E := E) (spectralDiracLinear IST)) := by
        symm
        exact cl11_bottDirac_sq_eq_cl11BottLaplacian
          (E := E) (F := H₂) (Dn := spectralDiracLinear IST)
    _ = 0 := hSqZero

/--
Operatorial-transport version of Bott-square closure.
-/
@[rep_depth transport]
theorem cl11_bottDirac_sq_eq_zero_of_operatorialTransport
    (V : BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility V IST) :
    (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
      (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0 := by
  exact cl11_bottDirac_sq_eq_zero_of_lichnerowiczBalanced
    (A := E) IST
    (lichnerowiczBalancedCl11_of_operatorialTransport
      (V := V) (IST := IST) hCompat)

end Core

end InfoGeometry.Canonical.InformationalLichnerowiczBottBridge
