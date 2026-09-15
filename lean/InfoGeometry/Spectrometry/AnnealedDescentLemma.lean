import InfoGeometry.Spectrometry.AitchisonGeometricMedian
import InfoGeometry.Spectrometry.WeightedQuadraticDescent
import InfoGeometry.Spectrometry.ThermalFreeEnergyMajorization

namespace InfoGeometry.Spectrometry.AitchisonGeometricMedian

open scoped BigOperators RealInnerProductSpace
open GeometricMedianCore DecoupledThermodynamics

noncomputable section

variable {Line Space : Type*} [Fintype Line]
variable [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

def anchoredSurrogate (observed : Line → Space) (cutoff temperature : ℝ)
    (anchor candidate : Space) : ℝ :=
  annealedObjective observed cutoff temperature anchor +
    ∑ line, thermalWeights observed anchor cutoff temperature line / 2 *
      (‖candidate - observed line‖ ^ 2 - ‖anchor - observed line‖ ^ 2)

theorem anchoredSurrogate_eq_quadratic
    (observed : Line → Space) (cutoff temperature : ℝ) (anchor candidate : Space) :
    anchoredSurrogate observed cutoff temperature anchor candidate =
      annealedObjective observed cutoff temperature anchor +
        (weightedQuadratic (thermalWeights observed anchor cutoff temperature) observed candidate -
          weightedQuadratic (thermalWeights observed anchor cutoff temperature) observed anchor) / 2 := by
  unfold anchoredSurrogate weightedQuadratic
  congr 1
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro line _
  ring

theorem anchoredSurrogate_touches
    (observed : Line → Space) (cutoff temperature : ℝ) (anchor : Space) :
    anchoredSurrogate observed cutoff temperature anchor anchor =
      annealedObjective observed cutoff temperature anchor := by
  simp [anchoredSurrogate]

theorem annealedObjective_le_surrogate
    (observed : Line → Space) (cutoff temperature : ℝ) (anchor candidate : Space)
    (temperature_pos : 0 < temperature) (regular : RegularAt observed anchor) :
    annealedObjective observed cutoff temperature candidate ≤
      anchoredSurrogate observed cutoff temperature anchor candidate := by
  unfold anchoredSurrogate annealedObjective totalFreeEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro line _
  exact lineFreeEnergy_le_quadratic _ _ cutoff temperature
    (norm_pos_iff.mpr (sub_ne_zero.mpr (regular line))) temperature_pos

theorem annealedStep_minimizes_surrogate [Nonempty Line]
    (observed : Line → Space) (cutoff temperature : ℝ) (anchor candidate : Space)
    (regular : RegularAt observed anchor) :
    anchoredSurrogate observed cutoff temperature anchor
        (annealedStep observed cutoff temperature anchor) ≤
      anchoredSurrogate observed cutoff temperature anchor candidate := by
  have positive := thermal_weights_pos observed anchor cutoff temperature regular
  have minimum := weightedCenter_minimizes_quadratic
    (thermalWeights observed anchor cutoff temperature) observed candidate
    (fun line => (positive line).le) (ne_of_gt (mass_pos _ positive))
  rw [anchoredSurrogate_eq_quadratic, anchoredSurrogate_eq_quadratic]
  change annealedObjective observed cutoff temperature anchor +
    (weightedQuadratic _ observed (weightedCenter _ observed) - _) / 2 ≤ _
  linarith

theorem annealedStep_surrogate_gap [Nonempty Line]
    (observed : Line → Space) (cutoff temperature : ℝ) (anchor : Space)
    (regular : RegularAt observed anchor) :
    anchoredSurrogate observed cutoff temperature anchor
        (annealedStep observed cutoff temperature anchor) =
      annealedObjective observed cutoff temperature anchor -
        (∑ line, thermalWeights observed anchor cutoff temperature line) / 2 *
          ‖anchor - annealedStep observed cutoff temperature anchor‖ ^ 2 := by
  have positive := thermal_weights_pos observed anchor cutoff temperature regular
  have expansion := weightedQuadratic_completed_square
    (thermalWeights observed anchor cutoff temperature) observed anchor
    (ne_of_gt (mass_pos _ positive))
  rw [anchoredSurrogate_eq_quadratic, expansion]
  unfold annealedStep
  ring

theorem annealedStep_quantitative_descent [Nonempty Line]
    (observed : Line → Space) (cutoff temperature : ℝ) (anchor : Space)
    (temperature_pos : 0 < temperature) (regular : RegularAt observed anchor) :
    annealedObjective observed cutoff temperature (annealedStep observed cutoff temperature anchor) +
        (∑ line, thermalWeights observed anchor cutoff temperature line) / 2 *
          ‖anchor - annealedStep observed cutoff temperature anchor‖ ^ 2 ≤
      annealedObjective observed cutoff temperature anchor := by
  have bound := annealedObjective_le_surrogate observed cutoff temperature anchor
    (annealedStep observed cutoff temperature anchor) temperature_pos regular
  rw [annealedStep_surrogate_gap observed cutoff temperature anchor regular] at bound
  linarith

theorem annealedStep_descent [Nonempty Line]
    (observed : Line → Space) (cutoff temperature : ℝ) (anchor : Space)
    (temperature_pos : 0 < temperature) (regular : RegularAt observed anchor) :
    annealedObjective observed cutoff temperature (annealedStep observed cutoff temperature anchor) ≤
      annealedObjective observed cutoff temperature anchor := by
  have positive := thermal_weights_pos observed anchor cutoff temperature regular
  have decrement_nonneg :
      0 ≤ (∑ line, thermalWeights observed anchor cutoff temperature line) / 2 *
        ‖anchor - annealedStep observed cutoff temperature anchor‖ ^ 2 :=
    mul_nonneg (div_nonneg (mass_pos _ positive).le (by norm_num)) (sq_nonneg _)
  have bound := annealedStep_quantitative_descent observed cutoff temperature anchor
    temperature_pos regular
  linarith

theorem annealedStep_strict_descent [Nonempty Line]
    (observed : Line → Space) (cutoff temperature : ℝ) (anchor : Space)
    (temperature_pos : 0 < temperature) (regular : RegularAt observed anchor)
    (not_fixed : annealedStep observed cutoff temperature anchor ≠ anchor) :
    annealedObjective observed cutoff temperature (annealedStep observed cutoff temperature anchor) <
      annealedObjective observed cutoff temperature anchor := by
  have positive := thermal_weights_pos observed anchor cutoff temperature regular
  have displacement_pos : 0 < ‖anchor - annealedStep observed cutoff temperature anchor‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm not_fixed))
  have decrement_pos := mul_pos (div_pos (mass_pos _ positive) two_pos)
    (sq_pos_of_pos displacement_pos)
  have bound := annealedStep_quantitative_descent observed cutoff temperature anchor
    temperature_pos regular
  linarith

theorem annealedStep_energy_eq_iff_fixed [Nonempty Line]
    (observed : Line → Space) (cutoff temperature : ℝ) (anchor : Space)
    (temperature_pos : 0 < temperature) (regular : RegularAt observed anchor) :
    annealedObjective observed cutoff temperature (annealedStep observed cutoff temperature anchor) =
        annealedObjective observed cutoff temperature anchor ↔
      annealedStep observed cutoff temperature anchor = anchor := by
  constructor
  · intro equal
    by_contra not_fixed
    exact (ne_of_lt (annealedStep_strict_descent observed cutoff temperature anchor
      temperature_pos regular not_fixed)) equal
  · intro fixed
    rw [fixed]

theorem annealed_iterates_energy_antitone [Nonempty Line]
    (observed : Line → Space) (cutoff temperature : ℝ) (initial : Space)
    (temperature_pos : 0 < temperature)
    (regular : ∀ iteration : ℕ,
      RegularAt observed ((annealedStep observed cutoff temperature)^[iteration] initial)) :
    Antitone (fun iteration : ℕ => annealedObjective observed cutoff temperature
      ((annealedStep observed cutoff temperature)^[iteration] initial)) := by
  apply antitone_nat_of_succ_le
  intro iteration
  rw [Function.iterate_succ_apply']
  exact annealedStep_descent observed cutoff temperature _ temperature_pos (regular iteration)

end

end InfoGeometry.Spectrometry.AitchisonGeometricMedian
