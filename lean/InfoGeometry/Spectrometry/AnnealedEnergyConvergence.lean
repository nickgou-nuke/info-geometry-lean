import InfoGeometry.Spectrometry.AnnealedDescentLemma
import Mathlib.Topology.Order.MonotoneConvergence

namespace InfoGeometry.Spectrometry.DecoupledThermodynamics

theorem lineFreeEnergy_zero_le (energy cutoff temperature : ℝ)
    (energy_nonneg : 0 ≤ energy) (temperature_pos : 0 < temperature) :
    lineFreeEnergy 0 cutoff temperature ≤ lineFreeEnergy energy cutoff temperature := by
  have exponential_bound : Real.exp (-energy / temperature) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr energy_nonneg) temperature_pos.le)
  have partition_bound : linePartition energy cutoff temperature ≤
      linePartition 0 cutoff temperature := by
    simpa only [linePartition, neg_zero, zero_div, Real.exp_zero] using
      add_le_add_right exponential_bound (Real.exp (-cutoff / temperature))
  have logarithm_bound := Real.log_le_log
    (line_partition_pos energy cutoff temperature) partition_bound
  exact mul_le_mul_of_nonpos_left logarithm_bound (neg_nonpos.mpr temperature_pos.le)

end InfoGeometry.Spectrometry.DecoupledThermodynamics

namespace InfoGeometry.Spectrometry.AitchisonGeometricMedian

open scoped BigOperators Topology
open GeometricMedianCore DecoupledThermodynamics Filter

noncomputable section

variable {Line Space : Type*} [Fintype Line]
variable [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

theorem annealedObjective_lower_bound
    (observed : Line → Space) (cutoff temperature : ℝ) (point : Space)
    (temperature_pos : 0 < temperature) :
    (∑ _line : Line, lineFreeEnergy 0 cutoff temperature) ≤
      annealedObjective observed cutoff temperature point := by
  exact Finset.sum_le_sum (fun line _ =>
    lineFreeEnergy_zero_le _ cutoff temperature (norm_nonneg _) temperature_pos)

theorem annealed_iterates_energy_tendsto [Nonempty Line]
    (observed : Line → Space) (cutoff temperature : ℝ) (initial : Space)
    (temperature_pos : 0 < temperature)
    (regular : ∀ iteration : ℕ,
      RegularAt observed ((annealedStep observed cutoff temperature)^[iteration] initial)) :
    Tendsto (fun iteration : ℕ => annealedObjective observed cutoff temperature
        ((annealedStep observed cutoff temperature)^[iteration] initial)) atTop
      (𝓝 (⨅ iteration : ℕ, annealedObjective observed cutoff temperature
        ((annealedStep observed cutoff temperature)^[iteration] initial))) := by
  apply tendsto_atTop_ciInf
    (annealed_iterates_energy_antitone observed cutoff temperature initial temperature_pos regular)
  refine ⟨∑ _line : Line, lineFreeEnergy 0 cutoff temperature, ?_⟩
  rintro value ⟨iteration, rfl⟩
  exact annealedObjective_lower_bound observed cutoff temperature _ temperature_pos

end

end InfoGeometry.Spectrometry.AitchisonGeometricMedian
