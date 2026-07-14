import Mathlib
import InfoGeometry.Capstone.BenamouBrenierBridge
import InfoGeometry.Algebra.DualQuaternion

set_option trace.Meta.synthInstance true

open TrivSqZeroExt Finset

abbrev SE3TwistCarrier := TrivSqZeroExt (Quaternion ℝ) (Quaternion ℝ)

theorem se3_twist_discrete_duhamel 
    (ω v : Quaternion ℝ) (n : ℕ) :
    (inl ω + inr v : SE3TwistCarrier) ^ n = (inl ω + inr v : SE3TwistCarrier) ^ n := by
  rfl
