import Mathlib
import InfoGeometry.Algebra.DualQuaternion

noncomputable section

open TrivSqZeroExt

abbrev SE3TwistCarrier := TrivSqZeroExt (Quaternion ℝ) (Quaternion ℝ)

def test_pow (ω v : Quaternion ℝ) (n : ℕ) : SE3TwistCarrier :=
  (inl ω + inr v : SE3TwistCarrier) ^ n

