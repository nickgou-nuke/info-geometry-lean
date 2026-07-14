import Mathlib
import InfoGeometry.Capstone.BenamouBrenierBridge
import InfoGeometry.Algebra.DualQuaternion

noncomputable section

open InfoGeometry.Algebra
open InfoGeometry.Capstone.BenamouBrenierBridge
open TrivSqZeroExt Finset

abbrev SE3TwistCarrier := TrivSqZeroExt (Quaternion ℝ) (Quaternion ℝ)

theorem se3_twist_discrete_duhamel 
    (ω v : Quaternion ℝ) (n : ℕ) :
    (inl ω + inr v : SE3TwistCarrier) ^ n =
    inl (ω ^ n) + discreteDuhamelSum ω v n := by
  apply discrete_duhamel_expansion
