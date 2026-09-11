import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SuperchargeGapBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SuperchargeRoleBridge

Narrow role/coherence bridge for the operatorial supercharge lane.

This file does not introduce a new supercharge ontology. It only makes explicit
the division already owned elsewhere:

- the concrete null-mode Majorana pair `u_-`,`u_+` is the genuine CAR branch,
- the primitive doubled-carrier odd operators are `J` and `ε`,
- the derived CPT supercharge is `Q = Jε`,
- the even-even `J/ε` commutator carries that derived `Q`,
- and the transported parity/modular gap seed is the first odd-odd deformation
  of this supercharge lane, while the second transport landing is the existing
  operatorial Hessian/metric/curvature split.
-/

namespace InfoGeometry.Canonical.SuperchargeRoleBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.SuperchargeGapBridge
open InfoGeometry.Canonical.SuperchargeTransportBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- At the undeformed base point, the transported parity supercharge is the primitive `J` lane. -/
@[rep_depth transport, simp] theorem transportedParitySupercharge_zero_eq_paritySuperchargeOp
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedParitySupercharge (E := E) V 0 = paritySuperchargeOp (E := E) := by
  exact transportedParitySupercharge_zero (E := E) V

/-- Root-name form of the undeformed transported parity lane. -/
@[rep_depth transport, simp] theorem transportedParitySupercharge_zero_eq_modular_j
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedParitySupercharge (E := E) V 0 = modular_j (E := E) := by
  rw [transportedParitySupercharge_zero_eq_paritySuperchargeOp (E := E) V]

/-- At the undeformed base point, the transported modular supercharge is the primitive `ε` lane. -/
@[rep_depth transport, simp] theorem transportedModularSupercharge_zero_eq_modularSuperchargeOp
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedModularSupercharge (E := E) V 0 = modularSuperchargeOp (E := E) := by
  exact transportedModularSupercharge_zero (E := E) V

/-- Root-name form of the undeformed transported modular lane. -/
@[rep_depth transport, simp] theorem transportedModularSupercharge_zero_eq_spectral_epsilon
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedModularSupercharge (E := E) V 0 = spectral_epsilon (E := E) := by
  rw [transportedModularSupercharge_zero_eq_modularSuperchargeOp (E := E) V]

/--
The transported gap seed is exactly the odd-odd CAR deformation of the
infinitesimal transported parity supercharge against the static modular
supercharge.
-/
@[rep_depth transport]
theorem transportedParityModularGapSeed_eq_car_of_infinitesimalParitySupercharge
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedParityModularGapSeed (E := E) V
      =
    CARBracket (E := E)
      (transportCommutator (E := E) V.connectionGenerator (paritySuperchargeOp (E := E)))
      (modularSuperchargeOp (E := E)) := by
  simpa [CARBracket, paritySuperchargeOp, modularSuperchargeOp] using
    transportedParityModularGapSeed_eq_transportSeed (E := E) V

/-- Root-name form of the first odd-odd transported gap seed. -/
@[rep_depth transport]
theorem transportedParityModularGapSeed_eq_car_root
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedParityModularGapSeed (E := E) V
      =
    CARBracket (E := E)
      (transportCommutator (E := E) V.connectionGenerator (modular_j (E := E)))
      (spectral_epsilon (E := E)) := by
  simpa using transportedParityModularGapSeed_eq_car_of_infinitesimalParitySupercharge (E := E) V

/--
If the phase-linear channel commutes with the primitive parity supercharge `J`,
the transported gap seed is carried purely by the phase-antilinear odd-odd
channel.
-/
@[rep_depth transport]
theorem transportedParityModularGapSeed_eq_phaseAntilinearCAR_of_commute_phaseLinearPart
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm :
      Commute (paritySuperchargeOp (E := E))
        (phaseLinearPart (E := E) V.connectionGenerator)) :
    transportedParityModularGapSeed (E := E) V
      =
    CARBracket (E := E)
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E) V.connectionGenerator)
        (paritySuperchargeOp (E := E)))
      (modularSuperchargeOp (E := E)) := by
  simpa [CARBracket, paritySuperchargeOp, modularSuperchargeOp] using
    transportedParityModularGapSeed_eq_phaseAntilinearSeed_of_commute_phaseLinearPart
      (E := E) V hComm

/-- Root-name form of the phase-antilinear odd-odd transported gap seed. -/
@[rep_depth transport]
theorem transportedParityModularGapSeed_eq_phaseAntilinearCAR_root_of_commute_phaseLinearPart
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm :
      Commute (modular_j (E := E))
        (phaseLinearPart (E := E) V.connectionGenerator)) :
    transportedParityModularGapSeed (E := E) V
      =
    CARBracket (E := E)
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E) V.connectionGenerator)
        (modular_j (E := E)))
      (spectral_epsilon (E := E)) := by
  simpa using
    transportedParityModularGapSeed_eq_phaseAntilinearCAR_of_commute_phaseLinearPart
      (E := E) V hComm

/--
The second transport landing of the primitive parity supercharge is exactly
the operatorial Hessian evaluated on the same carrier operator `J`.
-/
@[rep_depth transport]
theorem deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian_of_paritySuperchargeOp
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    let X := V.connectionGenerator
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationHessian
      (E := E) X (paritySuperchargeOp (E := E)) := by
  simpa [paritySuperchargeOp] using
    deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian
      (E := E) V

/-- Root-name form of the second transport landing as operatorial Hessian. -/
@[rep_depth transport]
theorem deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian_of_modular_j
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    let X := V.connectionGenerator
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationHessian
      (E := E) X (modular_j (E := E)) := by
  simpa using
    deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian_of_paritySuperchargeOp
      (E := E) V

/--
The second transport landing of the primitive parity supercharge splits into
the operatorial metric sector plus the half-curvature correction.
-/
@[rep_depth transport]
theorem deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart_of_paritySuperchargeOp
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    let X := V.connectionGenerator
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart
      (E := E) X X (paritySuperchargeOp (E := E))
      + ((2 : ℝ)⁻¹) •
        InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
          (E := E) X X (paritySuperchargeOp (E := E)) := by
  simpa [paritySuperchargeOp] using
    deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart
      (E := E) V

/-- Root-name form of the metric plus half-curvature split. -/
@[rep_depth transport]
theorem deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart_of_modular_j
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    let X := V.connectionGenerator
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart
      (E := E) X X (modular_j (E := E))
      + ((2 : ℝ)⁻¹) •
        InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
          (E := E) X X (modular_j (E := E)) := by
  simpa using
    deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart_of_paritySuperchargeOp
      (E := E) V

end Core

end InfoGeometry.Canonical.SuperchargeRoleBridge
