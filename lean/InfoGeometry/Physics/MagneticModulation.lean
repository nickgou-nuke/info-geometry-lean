import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace InfoGeometry.Physics.MagneticModulation

noncomputable section

def signedReadout (gap shift sign : ℝ) : ℝ :=
  sign * (gap + sign * shift)

theorem positive_readout (gap shift : ℝ) : signedReadout gap shift 1 = gap + shift := by
  simp [signedReadout]

theorem negative_readout (gap shift : ℝ) : signedReadout gap shift (-1) = shift - gap := by
  unfold signedReadout
  ring

theorem readout_difference (gap shift : ℝ) :
    signedReadout gap shift 1 - signedReadout gap shift (-1) = 2 * gap := by
  unfold signedReadout
  ring

theorem readouts_distinct_iff (gap shift : ℝ) :
    signedReadout gap shift 1 ≠ signedReadout gap shift (-1) ↔ gap ≠ 0 := by
  rw [← sub_ne_zero, readout_difference, mul_ne_zero_iff]
  simp

theorem opposite_signs_iff (gap shift : ℝ) :
    (0 < signedReadout gap shift 1 ∧ signedReadout gap shift (-1) < 0) ↔
      |shift| < gap := by
  rw [positive_readout, negative_readout, abs_lt]
  constructor
  · rintro ⟨positive, negative⟩
    constructor <;> linarith
  · rintro ⟨lower, upper⟩
    constructor <;> linarith

theorem distinct_readouts_can_have_the_same_sign :
    signedReadout 1 2 1 ≠ signedReadout 1 2 (-1) ∧
      0 < signedReadout 1 2 1 ∧ 0 < signedReadout 1 2 (-1) := by
  norm_num [signedReadout]

theorem zero_shift_does_not_remove_readout_separation (gap : ℝ) (gap_ne : gap ≠ 0) :
    signedReadout gap 0 1 ≠ signedReadout gap 0 (-1) :=
  (readouts_distinct_iff gap 0).mpr gap_ne

def phaseDifference (coupling field duration : ℝ) : ℝ :=
  coupling * field * duration - (-coupling) * field * duration

theorem phaseDifference_eq (coupling field duration : ℝ) :
    phaseDifference coupling field duration = 2 * coupling * field * duration := by
  unfold phaseDifference
  ring

theorem phaseDifference_ne_zero_iff (coupling field duration : ℝ) :
    phaseDifference coupling field duration ≠ 0 ↔
      coupling ≠ 0 ∧ field ≠ 0 ∧ duration ≠ 0 := by
  rw [phaseDifference_eq]
  simp [mul_ne_zero_iff, and_assoc]

end

end InfoGeometry.Physics.MagneticModulation
