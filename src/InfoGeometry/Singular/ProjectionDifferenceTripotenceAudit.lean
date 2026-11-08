/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.ProjectionDifferenceTripotence
import InfoGeometry.Core.NilpotentCartanRegression

namespace InfoGeometry.Singular.ProjectionSectors

open InfoGeometry.Core.NilpotentCartanRegression

-- The original noncommuting MP witness fails the exact compression criterion.
example :
    (obliqueInverse * oblique) * (oblique * obliqueInverse) * (obliqueInverse * oblique) ≠
      (oblique * obliqueInverse) * (obliqueInverse * oblique) * (oblique * obliqueInverse) := by
  obtain ⟨hq, hp⟩ := mp_supports mp_difference_not_tripotent.1
  exact fun h => mp_difference_not_tripotent.2
    ((difference_tripotent_iff_compressions hp.isIdempotentElem.eq hq.isIdempotentElem.eq).2 h)

-- Overlapping commuting projections: the product is nonzero, yet tripotence holds.
example :
    let p : RationalMatrix := 1
    let q : RationalMatrix := !![1, 0; 0, 0]
    p * q ≠ 0 ∧ (p - q)^3 = p - q := by
  dsimp only
  constructor
  · intro h
    have h00 := congrArg (fun a : RationalMatrix => a 0 0) h
    norm_num at h00
  · apply difference_tripotent_of_commute (one_mul _)
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · exact Commute.one_left _

-- A concrete C-star specialization uses mathlib's scalar C-star ring instance.
example : ((1 : ℂ) - 0)^3 = 1 - 0 := by
  exact (difference_tripotent_iff_commute (p := (1 : ℂ)) (q := 0)
    (by simp [isStarProjection_iff']) (by simp [isStarProjection_iff'])).2
    (Commute.one_left _)

#print axioms difference_cube_defect
#print axioms difference_tripotent_iff_compressions
#print axioms difference_tripotent_of_commute
#print axioms difference_tripotent_iff_commute
#print axioms mp_support_difference_tripotent_iff
#print axioms InfoGeometry.Core.NilpotentCartanRegression.mp_difference_not_tripotent

end InfoGeometry.Singular.ProjectionSectors
