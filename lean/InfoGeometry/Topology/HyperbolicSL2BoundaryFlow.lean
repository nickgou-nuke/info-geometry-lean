import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ProjectiveBoundarySL2Flow

namespace InfoGeometry.Topology

/-!
# The diagonal hyperbolic `SL(2, ℝ)` boundary flow

This is the explicit algebraic boost model.  Continuity on a chosen projective
boundary topology remains a separate obligation in
`ContinuousSL2BoundaryFlow`.
-/

noncomputable def hyperbolicSL2Matrix (t : ℝ) : SL2BoundaryMatrix ℝ where
  matrix := ![![Real.exp t, 0], ![0, Real.exp (-t)]]
  det_eq_one := by
    simp [det2, ← Real.exp_add]

theorem hyperbolicSL2Matrix_zero :
    hyperbolicSL2Matrix 0 = SL2BoundaryMatrix.identity := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyperbolicSL2Matrix,
    SL2BoundaryMatrix.identity]

theorem hyperbolicSL2Matrix_add (s t : ℝ) :
    hyperbolicSL2Matrix (s + t) =
      (hyperbolicSL2Matrix s).mul (hyperbolicSL2Matrix t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicSL2Matrix, SL2BoundaryMatrix.mul,
      Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add] <;> ring

noncomputable def hyperbolicSL2Flow : SL2BoundaryFlow ℝ where
  act := hyperbolicSL2Matrix
  zero_law := hyperbolicSL2Matrix_zero
  add_law := hyperbolicSL2Matrix_add

theorem hyperbolicSL2Flow_onBoundary_zero
    (p : ProjectiveBoundary ℝ) :
    hyperbolicSL2Flow.onBoundary 0 p = p :=
  hyperbolicSL2Flow.onBoundary_zero p

theorem hyperbolicSL2Flow_onBoundary_add
    (s t : ℝ) (p : ProjectiveBoundary ℝ) :
    hyperbolicSL2Flow.onBoundary (s + t) p =
      hyperbolicSL2Flow.onBoundary s
        (hyperbolicSL2Flow.onBoundary t p) :=
  hyperbolicSL2Flow.onBoundary_add s t p

end InfoGeometry.Topology
