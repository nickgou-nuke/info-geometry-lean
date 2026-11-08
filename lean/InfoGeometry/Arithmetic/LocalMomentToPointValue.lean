import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace InfoGeometry.Arithmetic.LocalMomentToPointValue

/--
A pointwise lower bound on a norm over an interval gives the corresponding
finite `L^q` lower bound.  This is the measure-theoretic step needed after a
derivative/Lipschitz persistence estimate; no asymptotic statement is used.
-/
theorem intervalIntegral_norm_pow_lower_bound
    (f : ℝ → ℂ) (a b r : ℝ) (q : ℕ)
    (hab : a ≤ b)
    (hfi : IntervalIntegrable (fun x => ‖f x‖ ^ q) volume a b)
    (hr : 0 ≤ r)
    (hpoint : ∀ x ∈ Set.Icc a b, r ≤ ‖f x‖) :
    (b - a) * r ^ q ≤ ∫ x in a..b, ‖f x‖ ^ q := by
  have hmono : (∫ x in a..b, r ^ q) ≤
      ∫ x in a..b, ‖f x‖ ^ q := by
    apply intervalIntegral.integral_mono_on hab
    · exact intervalIntegrable_const
    · exact hfi
    · intro x hx
      gcongr
      exact hpoint x hx
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono

end InfoGeometry.Arithmetic.LocalMomentToPointValue
