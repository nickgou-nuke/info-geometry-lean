import Mathlib
import InfoGeometry.Capstone.BenamouBrenierBridge
import InfoGeometry.Algebra.DualQuaternion

open TrivSqZeroExt Finset

abbrev SE3TwistCarrier := TrivSqZeroExt (Quaternion ℝ) (Quaternion ℝ)

instance : Ring SE3TwistCarrier := TrivSqZeroExt.ring
