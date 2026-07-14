import Mathlib
import InfoGeometry.Algebra.DualQuaternion

noncomputable section

open TrivSqZeroExt

abbrev SE3TwistCarrier := TrivSqZeroExt (Quaternion ℝ) (Quaternion ℝ)

def test_mul (ω v : Quaternion ℝ) : SE3TwistCarrier :=
  (inl ω + inr v : SE3TwistCarrier) * (inl ω + inr v : SE3TwistCarrier)

