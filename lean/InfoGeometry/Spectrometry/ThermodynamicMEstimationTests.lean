import InfoGeometry.Spectrometry.ThermodynamicMEstimation

namespace InfoGeometry.Spectrometry.ThermodynamicMEstimationTests

open GeometricMedianCore AitchisonGeometricMedian ThermodynamicMEstimation

example : HasFDerivAt (gaussianEnergy (3 : ℝ)) (innerSL ℝ (2 : ℝ)) 5 := by
  convert hasFDerivAt_gaussianEnergy (3 : ℝ) 5 using 1
  norm_num

example : fderiv ℝ (gaussianObjective (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => (3 : ℝ))) 3 = 0 := by
  apply (gaussian_stationary_iff_barycenter _ _ _ (by norm_num)).mpr
  norm_num [weightedCenter, Finset.centerMass]

example : IsGeometricMedian (fun _ : Fin 1 => (3 : ℝ)) 3 :=
  coincident_is_geometricMedian 3

example : ¬ RegularAt (fun _ : Fin 1 => (3 : ℝ)) 3 := by
  simp [RegularAt]

example : weightedScore (inverseDistance (fun _ : Fin 1 => (3 : ℝ)) 3)
    (fun _ => (3 : ℝ)) 3 = 0 := by
  simp [weightedScore]

example : weiszfeldStep (fun _ : Fin 1 => (3 : ℝ)) 3 ≠ 3 := by
  norm_num [weiszfeldStep, weightedCenter, Finset.centerMass, inverseDistance]

example (temperature : ℝ) : compoundWeight 2 2 temperature = 1 / 4 := by
  rw [compound_weight_formula]
  norm_num

#print axioms hasFDerivAt_gaussianEnergy
#print axioms hasFDerivAt_gaussianObjective
#print axioms gaussian_stationary_iff_barycenter
#print axioms laplace_stationary_iff_weiszfeld
#print axioms compound_weight_formula
#print axioms annealed_fixed_point_hasFDerivAt_zero

end InfoGeometry.Spectrometry.ThermodynamicMEstimationTests
