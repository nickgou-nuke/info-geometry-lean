import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.SuperchargeGapBridge
import InfoGeometry.Canonical.SuperchargeRoleBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SuperchargeGapHessianBridge

Coherence bridge for the transported parity/modular gap seed and the
operatorial Hessian/curvature landing on the same CPT-supercharge lane.

This file does not introduce new owners; it repackages existing ones:
- `SuperchargeCARCCRBridge` for the primitive/CPT supercharge surface,
- `SuperchargeGapBridge` for the transported odd-odd gap seed,
- `SuperchargeRoleBridge` for the explicit first/second landing role split,
- `SuperchargeTransportBridge` for the second-derivative Hessian landing.
-/

namespace InfoGeometry.Canonical.SuperchargeGapHessianBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.SuperchargeTransportBridge
open InfoGeometry.Canonical.SuperchargeGapBridge
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.SuperchargeRoleBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
The transported parity/modular gap seed is exactly the odd-odd transport seed on
the canonical CPT lane notation.
-/
@[rep_depth transport]
theorem transportedParityModularGapSeed_eq_cpt_lane_transportSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedParityModularGapSeed (E := E) V
      =
    fockAnticommutator (E := E)
      (transportCommutator (E := E) V.connectionGenerator (paritySuperchargeOp (E := E)))
      (modularSuperchargeOp (E := E)) := by
  simpa [paritySuperchargeOp, modularSuperchargeOp] using
    (transportedParityModularGapSeed_eq_transportSeed (E := E) V)

/--
On the same lane, the transported parity supercharge second derivative lands on
the metric plus half-curvature operatorial split.
-/
@[rep_depth transport]
theorem deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart_cpt_lane
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    let X := V.connectionGenerator
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    operatorInformationMetricPart (E := E) X X (paritySuperchargeOp (E := E))
      + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) X X (paritySuperchargeOp (E := E)) := by
  simpa [paritySuperchargeOp] using
    (deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart
      (E := E) V)

/--
First and second transport landings of the primitive parity supercharge on the
same CPT lane:
1. the first landing is the odd-odd transported gap seed,
2. the second landing is the operatorial Hessian,
3. the same Hessian splits into metric plus half-curvature.
-/
@[rep_depth transport]
theorem transportedParitySupercharge_first_second_landings
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    (transportedParityModularGapSeed (E := E) V
        =
      CARBracket (E := E)
        (transportCommutator (E := E) V.connectionGenerator (paritySuperchargeOp (E := E)))
        (modularSuperchargeOp (E := E)))
      ∧
    (let X := V.connectionGenerator;
      deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
        =
      operatorInformationHessian (E := E) X (paritySuperchargeOp (E := E)))
      ∧
    (let X := V.connectionGenerator;
      deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
        =
      operatorInformationMetricPart (E := E) X X (paritySuperchargeOp (E := E))
        + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) X X (paritySuperchargeOp (E := E))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact transportedParityModularGapSeed_eq_car_of_infinitesimalParitySupercharge (E := E) V
  · exact deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian_of_paritySuperchargeOp
      (E := E) V
  · exact
      deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart_of_paritySuperchargeOp
        (E := E) V

/--
Packaged CPT-lane closure statement:
1. primitive `J/ε` CCR anchor (`[J, ε] = 2Q`),
2. first transport landing as the odd-odd gap seed,
3. second transport landing as the operatorial Hessian,
4. Hessian split into metric plus half-curvature.
-/
@[rep_depth transport]
theorem transported_gapSeed_hessian_curvature_cpt_package
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    ((paritySuperchargeOp (E := E)).comp (modularSuperchargeOp (E := E))
        - (modularSuperchargeOp (E := E)).comp (paritySuperchargeOp (E := E))
        = (2 : ℝ) • cptSuperchargeOp (E := E))
      ∧
    (transportedParityModularGapSeed (E := E) V
        =
      CARBracket (E := E)
        (transportCommutator (E := E) V.connectionGenerator (paritySuperchargeOp (E := E)))
        (modularSuperchargeOp (E := E)))
      ∧
    (let X := V.connectionGenerator;
      deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
        =
      operatorInformationHessian (E := E) X (paritySuperchargeOp (E := E)))
      ∧
    (let X := V.connectionGenerator;
      deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
        =
      operatorInformationMetricPart (E := E) X X (paritySuperchargeOp (E := E))
        + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) X X (paritySuperchargeOp (E := E))) := by
  rcases transportedParitySupercharge_first_second_landings (E := E) V with ⟨hGap, hHess, hSplit⟩
  refine ⟨?_, hGap, hHess, hSplit⟩
  · exact parity_modular_supercharge_ccr_eq_two_cpt (E := E)

end Core

end InfoGeometry.Canonical.SuperchargeGapHessianBridge
