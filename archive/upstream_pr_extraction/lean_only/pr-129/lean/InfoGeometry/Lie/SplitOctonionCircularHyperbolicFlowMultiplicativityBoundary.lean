import InfoGeometry.Lie.SplitOctonionCircularZ3Grading

/-!
# Multiplicativity boundary for the uniform circular hyperbolic flow

The coordinate flow is a quadratic isometry, but its uniform weights do not
preserve the same-chirality octonion product.  The explicit obstruction is
proved in `SplitOctonionCircularZ3Grading`; this file exports the existential
form useful to downstream consumers.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlowMultiplicativityBoundary

open InfoGeometry.Lie.SplitOctonionCircularZ3Grading
open InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow

abbrev CZ := InfoGeometry.Lie.SplitOctonionCircularZ3Grading.CZ

theorem hyperbolicFlowZorn_not_multiplicative_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    ∃ X Y : CZ,
      hyperbolicFlowZorn t (X * Y) ≠
        hyperbolicFlowZorn t X * hyperbolicFlowZorn t Y := by
  by_contra h
  push_neg at h
  exact hyperbolicFlowZorn_not_mul_of_ne_zero t ht h

end InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlowMultiplicativityBoundary
