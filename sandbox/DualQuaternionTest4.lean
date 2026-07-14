import Mathlib
import InfoGeometry.Capstone.BenamouBrenierBridge
import InfoGeometry.Algebra.DualQuaternion

open TrivSqZeroExt Finset

abbrev SE3TwistCarrier := TrivSqZeroExt (Quaternion ℝ) (Quaternion ℝ)

-- Let's manually check if SMulCommClass exists
#check (inferInstance : SMulCommClass (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ (Quaternion ℝ))
