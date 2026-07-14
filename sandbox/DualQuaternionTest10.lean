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
  exact @discrete_duhamel_expansion (Quaternion ℝ) (Quaternion ℝ) _ _ _ _ _ ω v n
