import InfoGeometry.Spectrometry.WeiszfeldDescentLemma
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section

namespace InfoGeometry.Spectrometry.WeiszfeldDescentLemma

open scoped Topology BigOperators
open GeometricMedianCore Filter

variable {Line Space : Type*} [Fintype Line] [Nonempty Line]
variable [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

theorem iterates_energy_antitone (observed : Line → Space) (initial : Space)
    (regular : ∀ iteration : ℕ, RegularAt observed ((weiszfeldStep observed)^[iteration] initial)) :
    Antitone (fun iteration : ℕ =>
      distanceObjective observed ((weiszfeldStep observed)^[iteration] initial)) := by
  apply antitone_nat_of_succ_le
  intro iteration
  rw [Function.iterate_succ_apply']
  exact weiszfeld_monotone_descent observed _ (regular iteration)

theorem iterates_energy_tendsto (observed : Line → Space) (initial : Space)
    (regular : ∀ iteration : ℕ, RegularAt observed ((weiszfeldStep observed)^[iteration] initial)) :
    Tendsto (fun iteration : ℕ =>
        distanceObjective observed ((weiszfeldStep observed)^[iteration] initial)) atTop
      (𝓝 (⨅ iteration : ℕ,
        distanceObjective observed ((weiszfeldStep observed)^[iteration] initial))) := by
  apply tendsto_atTop_ciInf (iterates_energy_antitone observed initial regular)
  refine ⟨0, ?_⟩
  rintro value ⟨iteration, rfl⟩
  exact Finset.sum_nonneg (fun line _ => norm_nonneg _)

end InfoGeometry.Spectrometry.WeiszfeldDescentLemma
