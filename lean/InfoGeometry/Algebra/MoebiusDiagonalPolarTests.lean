import InfoGeometry.Algebra.MoebiusDiagonalPolar

namespace InfoGeometry.Algebra.MoebiusDiagonalPolarTests

open MoebiusTraceInvariant MoebiusDiagonalPolar

example (angle : ℝ) (hangle : Real.sin (2 * angle) ≠ 0) :
    (traceRatio (diagonalRepresentative (polarParameter 2 angle)) - 4).im ≠ 0 :=
  polar_traceRatio_nonreal 2 angle (by norm_num) hangle

example : (traceRatio (diagonalRepresentative (polarParameter 2 0)) - 4).im = 0 := by
  rw [polar_traceRatio_sub_four_im 2 0 (by norm_num)]
  simp

#print axioms polar_traceRatio_nonreal

end InfoGeometry.Algebra.MoebiusDiagonalPolarTests
