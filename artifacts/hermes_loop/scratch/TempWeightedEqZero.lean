import InfoGeometry.Canonical.WeightedWeylNormalizationBridge
import InfoGeometry.Canonical.SouriauPlanckVector

open scoped InnerProductSpace

namespace ScratchWeighted2

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

theorem densityWeightLiftedReadout_pair_eq_zero_of_equilibriumSeed_of_commute_phaseAxis
    {P : PotentialDatum (E := E)} {ψ : H₂} {A : EndH}
    (hEq : GibbsSouriauEquilibriumSeed (E := E) P ψ A)
    (hComm : Commute A (densityWeightPhaseAxis (E := E)))
    (w : ℝ) :
    ((densityWeightLiftedReadout (E := E) P ψ A w).metric,
      (densityWeightLiftedReadout (E := E) P ψ A w).phase)
      = (0, 0) := by
  have hWeighted :=
    densityWeightLiftedReadout_pair_eq_weighted_phaseAxisReadout_of_equilibriumSeed
      (E := E) hEq w
  have hCommZeroComplex :
      BogoliubovTransport.transportCommutator (E := E)
        (InfoGeometry.Krein.complex_i (E := E)) A = 0 := by
    unfold BogoliubovTransport.transportCommutator
    rw [← densityWeightPhaseAxis_eq_complex_i]
    exact sub_eq_zero.mpr hComm.eq.symm
  have hMetricZero :
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator (E := E)
        (BogoliubovTransport.transportCommutator (E := E)
          (InfoGeometry.Krein.complex_i (E := E)) A) = 0 := by
    rw [hCommZeroComplex]
    ext u v
    simp [InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator]
  have hBerryZero :
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator (E := E)
        (BogoliubovTransport.transportCommutator (E := E)
          (InfoGeometry.Krein.complex_i (E := E)) A) = 0 := by
    rw [hCommZeroComplex]
    ext u v
    simp [InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator]
  apply Prod.ext
  · have hMetric := congrArg Prod.fst hWeighted
    simpa [hMetricZero] using hMetric
  · have hPhase := congrArg Prod.snd hWeighted
    simpa [hBerryZero] using hPhase

end

end ScratchWeighted2
