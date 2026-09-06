import InfoGeometry.Krein.Superphysics
import InfoGeometry.Quantum.SuperchargeMultiplet
import InfoGeometry.Canonical.RelationalInformationCore
import InfoGeometry.Canonical.ModularHessian
import InfoGeometry.Canonical.PhaseVolumeDynamics
import InfoGeometry.Canonical.OperatorialUncertainty
import InfoGeometry.Canonical.RelativeModularPotential
import InfoGeometry.Canonical.ThermodynamicAction

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.FisherVolumeBridge

Bridge theorems connecting the currently owned Fisher, uncertainty, and phase
surfaces on the doubled-carrier theorem spine.

This file records the explicit connections proven in the repository.
-/

namespace InfoGeometry.Canonical.FisherVolumeBridge

open InfoGeometry.Canonical.ModularHessian
open InfoGeometry.Canonical.OperatorialUncertainty
open InfoGeometry.Canonical.PhaseVolumeDynamics
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.ThermodynamicAction
open InfoGeometry.Krein
open InfoGeometry.Quantum

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
The thermodynamic Fisher metric is exactly the modular Hessian read as a
bilinear form on perturbation channels.
-/
theorem action_hessian_eq_fisher
    (R : RelationalInformationDatum (E := E)) :
    fisherInformationMetric (E := E) R
      =
    fun X Y => modularHessian (E := E) R X Y := by
  rfl

/--
The induced relational datum satisfies the operatorial Robertson-Schrödinger
area law on the comparison-channel surface.
-/
theorem operatorial_uncertainty_area_law
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear X) :
    (comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y) ^ 2
      +
    (comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y) ^ 2
      ≤
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X X
      *
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) Y Y := by
  -- Invokes the proof from OperatorialUncertainty.lean
  simpa using
    toRelationalInformationDatum_comparisonGeneratorMetric_sq_add_phase_sq_le_of_IsPhaseLinear
      (E := E) P reference comparison X Y hX

/--
The comparison-state phase readout is the metric readout with a left
`K = Jε` twist.
-/
theorem metric_to_phase_readout_bridge
    (P : PotentialDatum (E := E))
    (comparison : H₂)
    (A : EndH) :
    comparisonPhaseReadout (E := E) P comparison A
      =
    (comparisonMetricReadout (E := E) P comparison A).compLeft
      (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E)).toLinearMap := by
  rw [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i]
  exact RelativeModularPotential.comparisonPhaseReadout_eq_metric_comp_complex_i
    (E := E) P comparison A

theorem metric_to_phase_readout_bridge_comp_complex_i
    (P : PotentialDatum (E := E))
    (comparison : H₂)
    (A : EndH) :
    comparisonPhaseReadout (E := E) P comparison A
      =
    (comparisonMetricReadout (E := E) P comparison A).compLeft
      (InfoGeometry.Krein.complex_i (E := E)).toLinearMap := by
  exact RelativeModularPotential.comparisonPhaseReadout_eq_metric_comp_complex_i
    (E := E) P comparison A

attribute [deprecated metric_to_phase_readout_bridge_comp_complex_i (since := "2026-04-11")]
  metric_to_phase_readout_bridge

/--
Dynamic rotation is exactly the preservation of the modular Hessian under the
phase-volume axis.
-/
theorem dynamic_rotation_preserves_hessian
    (M : SuperchargeMultiplet (E := E))
    (R : RelationalInformationDatum (E := E))
    (hRot : IsDynamicRotation (E := E) M R)
    (X Y : PerturbationChannel E) :
    modularHessian (E := E) R ((phaseVolumeAxis (E := E) M).comp X) Y
      +
    modularHessian (E := E) R X ((phaseVolumeAxis (E := E) M).comp Y) = 0 := by
  -- Follows directly from the definition of IsDynamicRotation
  exact hRot X Y

end InfoGeometry.Canonical.FisherVolumeBridge
