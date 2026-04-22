import InfoGeometry.Canonical.WeightedWeylNormalizationBridge
import InfoGeometry.Canonical.SouriauPlanckVector

open scoped InnerProductSpace

namespace ScratchWeighted

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DensityWeightIntertwinerBridge
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.SouriauPlanckVector
open InfoGeometry.Canonical.WeightedWeylNormalizationBridge
open InfoGeometry.Krein

section

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

theorem densityWeightLiftedReadout_pair_eq_weighted_phaseAxisReadout_of_equilibriumSeed
    {P : PotentialDatum (E := E)} {ψ : H₂} {A : EndH}
    (hEq : GibbsSouriauEquilibriumSeed (E := E) P ψ A)
    (w : ℝ) :
    ((densityWeightLiftedReadout (E := E) P ψ A w).metric,
      (densityWeightLiftedReadout (E := E) P ψ A w).phase)
      =
    (w • InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
          (E := E)
          (BogoliubovTransport.transportCommutator (E := E)
            (densityWeightPhaseAxis (E := E)) A),
      w • InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
          (E := E)
          (BogoliubovTransport.transportCommutator (E := E)
            (densityWeightPhaseAxis (E := E)) A)) := by
  have hSplit :=
    densityWeightLiftedReadout_pair_eq_zeroWeight_add_weighted_phaseAxisReadout
      (E := E) (P := P) (ψ := ψ) (A := A) (w := w)
  have hZero :=
    densityWeightLiftedReadout_zero_pair_eq_zero_of_equilibriumSeed (E := E) hEq
  have hMetricZero : (densityWeightLiftedReadout (E := E) P ψ A 0).metric = 0 := by
    exact congrArg Prod.fst hZero
  have hPhaseZero : (densityWeightLiftedReadout (E := E) P ψ A 0).phase = 0 := by
    exact congrArg Prod.snd hZero
  simpa [hMetricZero, hPhaseZero] using hSplit

end

end ScratchWeighted
