import GrandPartitionRobustPoisson
import Mathlib

noncomputable section

section OnlineLayer

/-- Discounted online sufficient statistics and a separate admission-rate
observable. -/
structure OnlineState where
  weightedSum : ℝ
  effectiveMass : ℝ
  admissionRate : ℝ

/-- Current background estimate. -/
def OnlineState.estimate (st : OnlineState) : ℝ :=
  st.weightedSum / st.effectiveMass

/-- One online generalized-EM / stochastic fixed-point update.  The
responsibility is evaluated externally at the previous estimate. -/
def OnlineState.update
    (st : OnlineState) (ρ ρa r x : ℝ) : OnlineState where
  weightedSum := ρ * st.weightedSum + r * x
  effectiveMass := ρ * st.effectiveMass + r
  admissionRate := ρa * st.admissionRate + (1 - ρa) * r

@[simp]
theorem OnlineState.update_weightedSum
    (st : OnlineState) (ρ ρa r x : ℝ) :
    (st.update ρ ρa r x).weightedSum =
      ρ * st.weightedSum + r * x := rfl

@[simp]
theorem OnlineState.update_effectiveMass
    (st : OnlineState) (ρ ρa r x : ℝ) :
    (st.update ρ ρa r x).effectiveMass =
      ρ * st.effectiveMass + r := rfl

@[simp]
theorem OnlineState.update_admissionRate
    (st : OnlineState) (ρ ρa r x : ℝ) :
    (st.update ρ ρa r x).admissionRate =
      ρa * st.admissionRate + (1 - ρa) * r := rfl

/-- Exact recursive barycentric identity. -/
theorem OnlineState.estimate_update
    (st : OnlineState) (ρ ρa r x : ℝ)
    (hN : st.effectiveMass ≠ 0)
    (hN' : ρ * st.effectiveMass + r ≠ 0) :
    (st.update ρ ρa r x).estimate =
      st.estimate +
        (r / (ρ * st.effectiveMass + r)) * (x - st.estimate) := by
  unfold OnlineState.estimate OnlineState.update
  field_simp [hN, hN']
  ring

/-- If a datum is completely rejected, the discounted ratio remains frozen. -/
theorem OnlineState.estimate_update_zero_responsibility
    (st : OnlineState) (ρ ρa x : ℝ)
    (hρ : ρ ≠ 0) (hN : st.effectiveMass ≠ 0) :
    (st.update ρ ρa 0 x).estimate = st.estimate := by
  unfold OnlineState.estimate OnlineState.update
  field_simp [hρ, hN]
  ring

/-- Effective mass remains nonnegative under nonnegative discount and
responsibility. -/
theorem OnlineState.update_effectiveMass_nonneg
    (st : OnlineState) {ρ ρa r x : ℝ}
    (hN : 0 ≤ st.effectiveMass) (hρ : 0 ≤ ρ) (hr : 0 ≤ r) :
    0 ≤ (st.update ρ ρa r x).effectiveMass := by
  simp [OnlineState.update, add_nonneg (mul_nonneg hρ hN) hr]

/-- Admission-rate invariance of the unit interval. -/
theorem OnlineState.update_admissionRate_mem_unit
    (st : OnlineState) {ρ ρa r x : ℝ}
    (ha0 : 0 ≤ st.admissionRate) (ha1 : st.admissionRate ≤ 1)
    (hρa0 : 0 ≤ ρa) (hρa1 : ρa ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ (st.update ρ ρa r x).admissionRate ∧
      (st.update ρ ρa r x).admissionRate ≤ 1 := by
  constructor
  · exact add_nonneg (mul_nonneg hρa0 ha0)
      (mul_nonneg (sub_nonneg.mpr hρa1) hr0)
  · nlinarith [mul_nonneg hρa0 (sub_nonneg.mpr ha1),
      mul_nonneg (sub_nonneg.mpr hρa1) (sub_nonneg.mpr hr1)]

/-- Persistent exact rejection causes both sufficient statistics to decay by
the same discount factor while preserving their ratio. -/
theorem OnlineState.lockout_step
    (st : OnlineState) (ρ ρa x : ℝ) :
    (st.update ρ ρa 0 x).weightedSum = ρ * st.weightedSum ∧
    (st.update ρ ρa 0 x).effectiveMass = ρ * st.effectiveMass := by
  simp [OnlineState.update]

/-- Simple re-annealing controller: impose a responsibility floor. -/
def responsibilityFloor (r rmin : ℝ) : ℝ :=
  max rmin r

theorem responsibilityFloor_ge_floor (r rmin : ℝ) :
    rmin ≤ responsibilityFloor r rmin := by
  exact le_max_left _ _

theorem responsibilityFloor_ge_input (r rmin : ℝ) :
    r ≤ responsibilityFloor r rmin := by
  exact le_max_right _ _

theorem responsibilityFloor_mem_unit
    {r rmin : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hm0 : 0 ≤ rmin) (hm1 : rmin ≤ 1) :
    0 ≤ responsibilityFloor r rmin ∧ responsibilityFloor r rmin ≤ 1 := by
  constructor
  · exact le_trans hr0 (le_max_right _ _)
  · exact max_le hm1 hr1

end OnlineLayer
