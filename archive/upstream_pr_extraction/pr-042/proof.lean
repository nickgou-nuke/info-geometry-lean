import InfoGeometry.Lie.SplitOctonionCircularProjectiveFixedLocus

open InfoGeometry.Lie.SplitOctonionCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
open InfoGeometry.Lie

lemma fixed_iff_of_ne_zero (t : ℝ) (ht : t ≠ 0)
    (p : CircularNullBoundary) :
    circularNullBoundaryFlow t p = p ↔
      (p.1.rep ∈ positiveWeightSubmodule ∨
       p.1.rep ∈ negativeWeightSubmodule ∨
       (p.1.rep ∈ zeroWeightSubmodule ∧ (p.1.rep 0 = 0 ∨ p.1.rep 4 = 0))) := by
  sorry
