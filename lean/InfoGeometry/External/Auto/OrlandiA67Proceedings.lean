import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace OrlandiA67Proceedings

structure MirrorPair where
  A : ℕ
  protonRich : String
  neutronRich : String

def As67Se67 : MirrorPair where
  A := 67
  protonRich := "67As"
  neutronRich := "67Se"

def channelCalibration_ns_per_channel : ℚ := 56 / 100

def centroidShiftTime (cForward cReverse : ℚ) : ℚ :=
  ((cReverse - cForward) * channelCalibration_ns_per_channel) / 2

def centroidForward_As67_943_725 : ℚ := 409497 / 100
def centroidReverse_As67_943_725 : ℚ := 409805 / 100

theorem raw_centroid_lifetime_As67_943_725 :
    centroidShiftTime centroidForward_As67_943_725 centroidReverse_As67_943_725 =
      1078 / 1250 := by
  norm_num [centroidShiftTime, channelCalibration_ns_per_channel,
    centroidForward_As67_943_725, centroidReverse_As67_943_725]

def promptContribution_As67_ns : ℚ := 20 / 100
def tau_As67_9half_prelim_ns : ℚ := 7 / 10
def tau_Se67_9half_prelim_ns : ℚ := 13 / 10

theorem Se67_lifetime_longer_prelim :
    tau_As67_9half_prelim_ns < tau_Se67_9half_prelim_ns := by
  norm_num [tau_As67_9half_prelim_ns, tau_Se67_9half_prelim_ns]

def tau_As69_known_ns : ℚ := 194 / 100
def tau_As69_corrected_centroid_ns : ℚ := 21 / 10

theorem As69_centroid_validation_window :
    |tau_As69_corrected_centroid_ns - tau_As69_known_ns| < (1 / 5 : ℚ) := by
  norm_num [tau_As69_corrected_centroid_ns, tau_As69_known_ns]

def branching_Se67_304 : ℚ := 10 / 100
def branching_Se67_717 : ℚ := 84 / 100
def branching_Se67_1365 : ℚ := 6 / 100

theorem branching_Se67_sum :
    branching_Se67_304 + branching_Se67_717 + branching_Se67_1365 = 1 := by
  norm_num [branching_Se67_304, branching_Se67_717, branching_Se67_1365]

def BE1u_As67_725 : ℚ := 13 / 10
def BE1u_Se67_717 : ℚ := 1
def BE1u_As67_319 : ℚ := 81 / 10
def BE1u_Se67_304 : ℚ := 17 / 10

def mirrorRatio (x y : ℚ) : ℚ := x / y

theorem BE1_first_ratio_prelim :
    mirrorRatio BE1u_As67_725 BE1u_Se67_717 = 13 / 10 := by
  norm_num [mirrorRatio, BE1u_As67_725, BE1u_Se67_717]

theorem BE1_second_ratio_prelim :
    mirrorRatio BE1u_As67_319 BE1u_Se67_304 = 81 / 17 := by
  norm_num [mirrorRatio, BE1u_As67_319, BE1u_Se67_304]

theorem first_pair_near_symmetric :
    |mirrorRatio BE1u_As67_725 BE1u_Se67_717 - 1| ≤ (3 / 10 : ℚ) := by
  norm_num [mirrorRatio, BE1u_As67_725, BE1u_Se67_717]

theorem second_pair_asymmetric :
    (4 : ℚ) < mirrorRatio BE1u_As67_319 BE1u_Se67_304 := by
  norm_num [mirrorRatio, BE1u_As67_319, BE1u_Se67_304]

def noLongLifetimeObserved (tauMeasured tauClaimed : ℚ) : Prop :=
  tauMeasured < tauClaimed / 4

theorem As67_not_12ns_centroid_scale :
    noLongLifetimeObserved tau_As67_9half_prelim_ns 12 := by
  norm_num [noLongLifetimeObserved, tau_As67_9half_prelim_ns]

def formalSummary : Prop :=
  tau_As67_9half_prelim_ns < tau_Se67_9half_prelim_ns ∧
    branching_Se67_304 + branching_Se67_717 + branching_Se67_1365 = 1 ∧
    mirrorRatio BE1u_As67_725 BE1u_Se67_717 = 13 / 10 ∧
    mirrorRatio BE1u_As67_319 BE1u_Se67_304 = 81 / 17 ∧
    noLongLifetimeObserved tau_As67_9half_prelim_ns 12

theorem formalSummary_proved : formalSummary := by
  exact ⟨Se67_lifetime_longer_prelim, branching_Se67_sum,
    BE1_first_ratio_prelim, BE1_second_ratio_prelim,
    As67_not_12ns_centroid_scale⟩

end OrlandiA67Proceedings

end noncomputable section
