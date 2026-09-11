import InfoGeometry.Canonical.HestenesLoxodromicCasimirs
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

theorem continuous_loxodromicScalarInvariant :
    Continuous (fun p : ℝ × ℝ => loxodromicScalarInvariant p.1 p.2) := by
  exact continuous_fst.pow 2 |>.sub (continuous_snd.pow 2)

theorem continuous_loxodromicPseudoscalarInvariant :
    Continuous (fun p : ℝ × ℝ =>
      loxodromicPseudoscalarInvariant p.1 p.2) := by
  exact (continuous_const.mul continuous_fst).mul continuous_snd

theorem continuous_loxodromicNormSquare :
    Continuous (fun p : ℝ × ℝ => loxodromicNormSquare p.1 p.2) := by
  exact continuous_fst.pow 2 |>.add (continuous_snd.pow 2)

end InfoGeometry.Canonical
