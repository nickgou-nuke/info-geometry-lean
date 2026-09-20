import InfoGeometry.Nuclear.AndreevCascadeInterferometer

namespace InfoGeometry.Nuclear.AndreevCascadeInterferometerTests

open AndreevCascadeInterferometer
open DetectorGeometry.ApollonianBalanceParabola
open InfoGeometry.Algebra.CyclotomicPhaseReadout

example : singleObserved 1 1 (balancePoint 1) = 1 / 4 := by
  norm_num [singleObserved, balancePoint]

example : coincidenceRate 1 1 (balancePoint 1) = 1 / 4 := by
  norm_num [coincidenceRate, balancePoint]

example : Real.binEntropy (coincidenceRate 1 1 (balancePoint 1) /
    (1 * balancePoint 1)) / Real.log 2 = 1 :=
  conditional_entropy_at_balance 1 1 (by norm_num) (by norm_num)

example (coupling efficiency : ℝ) :
    Real.binEntropy (coincidenceRate 0 coupling efficiency / (0 * efficiency)) = 0 := by
  simp

example : (∑ exponent ∈ Finset.range 3, (1 : ℂ) * phase 3 ^ exponent) = 0 :=
  three_phase_amplitude_sum 1

example : (1 : ℂ) * (1 * phase 3) * (1 * phase 3 ^ 2) = 1 := by
  simpa using three_phase_product 1

#print axioms conditional_entropy_eq_one_iff
#print axioms nonnegative_equipartition_energy
#print axioms three_phase_amplitude_sum
#print axioms three_phase_product

end InfoGeometry.Nuclear.AndreevCascadeInterferometerTests
