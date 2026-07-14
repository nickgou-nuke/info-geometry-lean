import Mathlib
import InfoGeometry.Capstone.BenamouBrenierBridge
import InfoGeometry.Algebra.DualQuaternion

namespace InfoGeometry.Sandbox.DualQuaternionTest

open InfoGeometry.Algebra
open InfoGeometry.Capstone.BenamouBrenierBridge
open TrivSqZeroExt Finset

-- A twist vector has a real (rotational) vector part and a dual (translational) vector part.
-- We can model the dual quaternion algebra as `TrivSqZeroExt (Quaternion ℝ) (Quaternion ℝ)`
-- for the purposes of applying the exact operator-level expansion.

abbrev SE3TwistCarrier := TrivSqZeroExt (Quaternion ℝ) (Quaternion ℝ)

theorem se3_twist_discrete_duhamel 
    (ω v : Quaternion ℝ) (n : ℕ) :
    (inl ω + inr v : SE3TwistCarrier) ^ n =
    inl (ω ^ n) + discreteDuhamelSum ω v n := by
  -- We apply the non-commutative operator discrete Duhamel expansion proven in BenamouBrenierBridge
  apply discrete_duhamel_expansion
