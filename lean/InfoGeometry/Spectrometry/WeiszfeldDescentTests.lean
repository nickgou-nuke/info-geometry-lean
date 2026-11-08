import InfoGeometry.Spectrometry.WeiszfeldEnergyConvergence

namespace InfoGeometry.Spectrometry.WeiszfeldDescentTests

open GeometricMedianCore WeiszfeldDescentLemma

noncomputable section

def observed : Unit → ℝ := fun _ => 3

theorem initial_regular : RegularAt observed (0 : ℝ) := by
  intro line
  norm_num [observed]

theorem first_step : weiszfeldStep observed 0 = 3 := by
  norm_num [weiszfeldStep, weightedCenter, Finset.centerMass, inverseDistance, observed]

example : distanceObjective observed (weiszfeldStep observed 0) <
    distanceObjective observed 0 :=
  weiszfeld_strict_descent observed 0 initial_regular (by rw [first_step]; norm_num)

example : ¬ RegularAt observed (weiszfeldStep observed 0) := by
  rw [first_step]
  intro regular
  exact regular () rfl

example : surrogate observed 3 0 < distanceObjective observed 0 := by
  norm_num [surrogate, distanceObjective, observed]

example : distanceObjective observed 3 < distanceObjective observed (weiszfeldStep observed 3) := by
  norm_num [distanceObjective, weiszfeldStep, weightedCenter, Finset.centerMass,
    inverseDistance, observed]

example (candidate : ℝ) : surrogate observed 0 candidate = surrogate observed 0 3 ↔
    candidate = 3 := by
  simpa only [first_step] using surrogate_minimum_unique observed 0 candidate initial_regular

example (candidate : ℝ) : distanceObjective (fun empty : Fin 0 => Fin.elim0 empty) candidate = 0 := by
  simp [distanceObjective]

#print axioms surrogate_majorization
#print axioms surrogate_minimum_unique
#print axioms weiszfeld_quantitative_descent
#print axioms weiszfeld_energy_eq_iff_fixed
#print axioms iterates_energy_tendsto

end

end InfoGeometry.Spectrometry.WeiszfeldDescentTests
