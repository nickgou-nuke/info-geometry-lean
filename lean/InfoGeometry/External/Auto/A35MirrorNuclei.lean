import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace A35MirrorNuclei

def real_add_identity (x : ℝ) : ℝ := x + 0

theorem real_add_identity_eq (x : ℝ) : real_add_identity x = x := by
  exact add_zero x

theorem real_mul_identity (x : ℝ) : x * 1 = x := by
  exact mul_one x

end A35MirrorNuclei