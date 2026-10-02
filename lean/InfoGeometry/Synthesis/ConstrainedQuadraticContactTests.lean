import InfoGeometry.Synthesis.ConstrainedQuadraticContact

namespace InfoGeometry.Synthesis.ConstrainedQuadraticContactTests

open ConstrainedQuadraticContact ImpedanceMatchingDuality

example : constrainedGap (1 / 4) = 1 / 16 := by
  rw [constrainedGap_formula _ (by norm_num)]
  norm_num

example : constrainedGap 0 = 1 / 4 := by
  rw [constrainedGap_formula _ (by norm_num)]
  norm_num

example : constrainedGap (1 / 2) = 0 :=
  (constrainedGap_zero_iff _ (by norm_num)).mpr (by norm_num)

example : optimalEfficiency 1 = 1 / 2 := by
  norm_num [optimalEfficiency]

example : optimalEfficiency (1 / 4) = 1 := by
  norm_num [optimalEfficiency]

example : IsGreatest (fisher_capacity (1 / 4) '' Set.Icc (0 : ℝ) 1) (3 / 16) := by
  convert capacity_isGreatest_on_unitInterval (1 / 4) (by norm_num) using 1
  norm_num [optimalCapacity]

example : channel_duality_gap (1 / 4) = 0 ∧ constrainedGap (1 / 4) ≠ 0 := by
  constructor
  · exact duality_gap_vanishes _ (by norm_num)
  · rw [constrainedGap_formula _ (by norm_num)]
    norm_num

#print axioms capacity_isGreatest_on_unitInterval
#print axioms constrainedGap_zero_iff
#print axioms constrainedGap_le_pointwise
#print axioms constrainedGap_attained
#print axioms constrainedGap_isLeast

end InfoGeometry.Synthesis.ConstrainedQuadraticContactTests
