import Mathlib
import InfoGeometry.Capstone.BenamouBrenierBridge

noncomputable section

open InfoGeometry.Capstone.BenamouBrenierBridge
open TrivSqZeroExt Finset

abbrev SE3TwistCarrier := TrivSqZeroExt (Quaternion ℝ) (Quaternion ℝ)

def test_sum (ω v : Quaternion ℝ) (n : ℕ) : SE3TwistCarrier :=
  discreteDuhamelSum ω v n
