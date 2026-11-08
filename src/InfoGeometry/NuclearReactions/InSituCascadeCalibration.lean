import InfoGeometry.Probability.DetectorCopulaDecoupling
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace InfoGeometry.NuclearReactions.InSituCascadeCalibration

open InfoGeometry.Probability.DetectorCopulaDecoupling

noncomputable section

structure CascadeCalibration where
  firstYield : ℝ
  secondYield : ℝ
  jointYield : ℝ
  angularFactor : ℝ
  firstEfficiency : ℝ
  secondEfficiency : ℝ
  first_yield_pos : 0 < firstYield
  second_yield_pos : 0 < secondYield
  joint_yield_pos : 0 < jointYield
  angular_pos : 0 < angularFactor
  first_efficiency_pos : 0 < firstEfficiency
  second_efficiency_pos : 0 < secondEfficiency

def activityFromSlope (slope : ℝ) (calibration : CascadeCalibration) : ℝ :=
  slope * (calibration.jointYield / (calibration.firstYield * calibration.secondYield)) *
    calibration.angularFactor

theorem cascade_activity_from_product (activity : ℝ) (calibration : CascadeCalibration)
    (activity_ne : activity ≠ 0) :
    activityFromSlope
        (microscopicProduct activity calibration.firstYield calibration.secondYield
            calibration.firstEfficiency calibration.secondEfficiency /
          microscopicCoincidence activity calibration.jointYield
            calibration.firstEfficiency calibration.secondEfficiency calibration.angularFactor)
        calibration = activity := by
  unfold activityFromSlope
  rw [copula_activity_recovery _ _ _ _ _ _ _ activity_ne
    (ne_of_gt calibration.joint_yield_pos) (ne_of_gt calibration.first_efficiency_pos)
    (ne_of_gt calibration.second_efficiency_pos) (ne_of_gt calibration.angular_pos)]
  have first_ne := ne_of_gt calibration.first_yield_pos
  have second_ne := ne_of_gt calibration.second_yield_pos
  have joint_ne := ne_of_gt calibration.joint_yield_pos
  have angular_ne := ne_of_gt calibration.angular_pos
  field_simp

theorem cascade_activity_from_linear_rays
    (activity coordinate firstSlope secondSlope : ℝ) (calibration : CascadeCalibration)
    (activity_ne : activity ≠ 0)
    (coordinate_sq : coordinate ^ 2 = microscopicCoincidence activity calibration.jointYield
      calibration.firstEfficiency calibration.secondEfficiency calibration.angularFactor)
    (first_ray : firstSlope * coordinate = activity * calibration.firstYield * calibration.firstEfficiency)
    (second_ray : secondSlope * coordinate = activity * calibration.secondYield * calibration.secondEfficiency) :
    activityFromSlope (firstSlope * secondSlope) calibration = activity := by
  have coincidence_ne : microscopicCoincidence activity calibration.jointYield
      calibration.firstEfficiency calibration.secondEfficiency calibration.angularFactor ≠ 0 := by
    unfold microscopicCoincidence
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero activity_ne
      (ne_of_gt calibration.joint_yield_pos)) (ne_of_gt calibration.first_efficiency_pos))
      (ne_of_gt calibration.second_efficiency_pos)) (ne_of_gt calibration.angular_pos)
  have slope_identity : firstSlope * secondSlope =
      microscopicProduct activity calibration.firstYield calibration.secondYield
          calibration.firstEfficiency calibration.secondEfficiency /
        microscopicCoincidence activity calibration.jointYield
          calibration.firstEfficiency calibration.secondEfficiency calibration.angularFactor := by
    apply (eq_div_iff coincidence_ne).mpr
    rw [← coordinate_sq]
    calc
      firstSlope * secondSlope * coordinate ^ 2 =
          (firstSlope * coordinate) * (secondSlope * coordinate) := by ring
      _ = microscopicProduct activity calibration.firstYield calibration.secondYield
          calibration.firstEfficiency calibration.secondEfficiency := by
        rw [first_ray, second_ray]
        rfl
  rw [slope_identity]
  exact cascade_activity_from_product activity calibration activity_ne

def restoredRate (observed loss coincidence : ℝ) : ℝ := observed + loss * coincidence

theorem restored_rate_of_quadratic (slope loss coincidence : ℝ) (coincidence_nonneg : 0 ≤ coincidence) :
    restoredRate (singlesResponse slope loss (Real.sqrt coincidence)) loss coincidence =
      restoredMarginal slope (Real.sqrt coincidence) := by
  simpa only [restoredRate, Real.sq_sqrt coincidence_nonneg] using
    quadratic_marginal_restoration slope loss (Real.sqrt coincidence)

theorem restored_rate_of_loss_model (observed ideal loss coincidence : ℝ)
    (loss_model : observed = ideal - loss * coincidence) :
    restoredRate observed loss coincidence = ideal := by
  rw [restoredRate, loss_model]
  ring

def activityRatioFromRates
    (targetRate referenceRate targetYield referenceYield relativeEfficiency : ℝ) : ℝ :=
  targetRate * referenceYield / (referenceRate * targetYield * relativeEfficiency)

def transferredActivity
    (targetRate referenceRate targetYield referenceYield relativeEfficiency referenceActivity : ℝ) : ℝ :=
  referenceActivity *
    activityRatioFromRates targetRate referenceRate targetYield referenceYield relativeEfficiency

theorem activity_ratio_from_rates
    (targetActivity referenceActivity targetYield referenceYield referenceEfficiency relativeEfficiency : ℝ)
    (reference_activity_ne : referenceActivity ≠ 0) (target_yield_ne : targetYield ≠ 0)
    (reference_yield_ne : referenceYield ≠ 0) (reference_efficiency_ne : referenceEfficiency ≠ 0)
    (relative_efficiency_ne : relativeEfficiency ≠ 0) :
    activityRatioFromRates (targetActivity * targetYield * (relativeEfficiency * referenceEfficiency))
        (referenceActivity * referenceYield * referenceEfficiency)
        targetYield referenceYield relativeEfficiency = targetActivity / referenceActivity := by
  unfold activityRatioFromRates
  field_simp

theorem transferred_activity_exact
    (targetActivity referenceActivity targetYield referenceYield referenceEfficiency relativeEfficiency : ℝ)
    (reference_activity_ne : referenceActivity ≠ 0) (target_yield_ne : targetYield ≠ 0)
    (reference_yield_ne : referenceYield ≠ 0) (reference_efficiency_ne : referenceEfficiency ≠ 0)
    (relative_efficiency_ne : relativeEfficiency ≠ 0) :
    transferredActivity (targetActivity * targetYield * (relativeEfficiency * referenceEfficiency))
        (referenceActivity * referenceYield * referenceEfficiency)
        targetYield referenceYield relativeEfficiency referenceActivity = targetActivity := by
  unfold transferredActivity
  rw [activity_ratio_from_rates _ _ _ _ _ _ reference_activity_ne target_yield_ne
    reference_yield_ne reference_efficiency_ne relative_efficiency_ne]
  exact mul_div_cancel₀ _ reference_activity_ne

end

end InfoGeometry.NuclearReactions.InSituCascadeCalibration
