import InfoGeometry.Canonical.DensityWeightIntertwinerBridge
import InfoGeometry.Canonical.SouriauPlanckVector

open scoped InnerProductSpace

namespace ScratchWeight

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DensityWeightIntertwinerBridge
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.ThermodynamicGenerator
open InfoGeometry.Canonical.SouriauPlanckVector
open InfoGeometry.Krein

section

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

theorem densityWeightLiftedReadout_zero_pair_eq_comparisonReadout_pair
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    ((densityWeightLiftedReadout (E := E) P ψ A 0).metric,
      (densityWeightLiftedReadout (E := E) P ψ A 0).phase)
      =
    (comparisonMetricReadout (E := E) P ψ A,
      comparisonPhaseReadout (E := E) P ψ A) := by
  apply Prod.ext
  · ext u v
    simp [densityWeightLiftedReadout, DensityWeightIntertwinerBridge.densityWeightLiftedDynamics_zero,
      StateDependentTransport.stateInducedDynamics,
      StateDependentTransport.stateTransportGenerator,
      StateDependentTransport.stateRelativeModularGenerator,
      BogoliubovTransport.relativeModularDeriv,
      BogoliubovTransport.relativeModularKGenerator,
      BogoliubovTransport.modularDeriv,
      BogoliubovTransport.modularTransportGenerator,
      comparisonMetricReadout_apply]
  · ext u v
    simp [densityWeightLiftedReadout, DensityWeightIntertwinerBridge.densityWeightLiftedDynamics_zero,
      StateDependentTransport.stateInducedDynamics,
      StateDependentTransport.stateTransportGenerator,
      StateDependentTransport.stateRelativeModularGenerator,
      BogoliubovTransport.relativeModularDeriv,
      BogoliubovTransport.relativeModularKGenerator,
      BogoliubovTransport.modularDeriv,
      BogoliubovTransport.modularTransportGenerator]

theorem densityWeightLiftedReadout_zero_pair_eq_zero_of_equilibriumSeed
    {P : PotentialDatum (E := E)} {ψ : H₂} {A : EndH}
    (hEq : GibbsSouriauEquilibriumSeed (E := E) P ψ A) :
    ((densityWeightLiftedReadout (E := E) P ψ A 0).metric,
      (densityWeightLiftedReadout (E := E) P ψ A 0).phase)
      = (0, 0) := by
  rw [densityWeightLiftedReadout_zero_pair_eq_comparisonReadout_pair (E := E) P ψ A]
  exact comparisonReadout_pair_eq_zero_of_equilibriumSeed (E := E) hEq

end

end ScratchWeight
