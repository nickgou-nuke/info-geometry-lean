import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# The finite colour symmetry is genuinely non-Abelian

The existing owner supplies the two adjacent Coxeter reflections and their
braid relation.  This file records the missing non-commutation statement, so
the finite colour symmetry is not described merely by its presentation: the
two generators are provably distinct in order.
-/

namespace InfoGeometry.Physics.SplitOctonionBraidSU3

open Color

theorem S3_generators_noncommute :
    swapRGPerm * swapGBPerm ≠ swapGBPerm * swapRGPerm := by
  intro h
  have hc := Equiv.congr_fun h red
  simp [swapRGPerm, swapGBPerm, swapRG, swapGB] at hc

end InfoGeometry.Physics.SplitOctonionBraidSU3
