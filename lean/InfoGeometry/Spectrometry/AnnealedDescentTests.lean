import InfoGeometry.Spectrometry.AnnealedEnergyConvergence
import InfoGeometry.Spectrometry.AnnealedDescentDependency

namespace InfoGeometry.Spectrometry.AnnealedDescentTests

open scoped BigOperators
open GeometricMedianCore DecoupledThermodynamics AitchisonGeometricMedian

noncomputable section

def singleObservation : Unit → ℝ := fun _ => 0

theorem singleObservation_regular : RegularAt singleObservation (1 : ℝ) := by
  intro line
  norm_num [singleObservation]

theorem singleObservation_step (cutoff temperature : ℝ) :
    annealedStep singleObservation cutoff temperature 1 = 0 := by
  simp [annealedStep, weightedCenter, Finset.centerMass, singleObservation]

example (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    annealedObjective singleObservation cutoff temperature 0 <
      annealedObjective singleObservation cutoff temperature 1 := by
  have strict := annealedStep_strict_descent singleObservation cutoff temperature 1
    temperature_pos singleObservation_regular
    (by rw [singleObservation_step]; norm_num)
  simpa only [singleObservation_step] using strict

example (cutoff temperature : ℝ) :
    ¬ RegularAt singleObservation (annealedStep singleObservation cutoff temperature 1) := by
  rw [singleObservation_step]
  intro regular
  exact regular () rfl

example (cutoff temperature : ℝ) :
    anchoredSurrogate singleObservation cutoff temperature 1 1 =
      annealedObjective singleObservation cutoff temperature 1 :=
  anchoredSurrogate_touches _ _ _ _

example (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    annealedObjective singleObservation cutoff temperature 0 ≤
      anchoredSurrogate singleObservation cutoff temperature 1 0 :=
  annealedObjective_le_surrogate _ _ _ _ _ temperature_pos singleObservation_regular

example : weightedQuadratic (fun _ : Unit => (2 : ℝ)) singleObservation 3 = 18 := by
  norm_num [weightedQuadratic, singleObservation]

example (candidate : ℝ) :
    weightedQuadratic (fun _ : Unit => (2 : ℝ)) singleObservation 0 ≤
      weightedQuadratic (fun _ : Unit => (2 : ℝ)) singleObservation candidate := by
  have minimum := weightedCenter_minimizes_quadratic
    (fun _ : Unit => (2 : ℝ)) singleObservation candidate
    (by intro line; norm_num) (by simp)
  simpa [weightedCenter, Finset.centerMass, singleObservation] using minimum

example (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    lineFreeEnergy 0 cutoff temperature ≤ lineFreeEnergy 3 cutoff temperature :=
  lineFreeEnergy_zero_le _ _ _ (by norm_num) temperature_pos

#print axioms weightedQuadratic_completed_square
#print axioms lineFreeEnergy_le_tangent
#print axioms lineFreeEnergy_le_quadratic
#print axioms annealedObjective_le_surrogate
#print axioms annealedStep_minimizes_surrogate
#print axioms annealedStep_quantitative_descent
#print axioms annealedStep_strict_descent
#print axioms annealedStep_energy_eq_iff_fixed
#print axioms annealed_iterates_energy_antitone
#print axioms annealed_iterates_energy_tendsto
#print axioms AnnealedDescentDependency.majorization_and_minimization_incomparable

end

end InfoGeometry.Spectrometry.AnnealedDescentTests
