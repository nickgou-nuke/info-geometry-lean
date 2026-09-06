import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Phase-consistent `U(1)` volume. -/
def volU1 : ℝ :=
  2 * Real.pi

/-- `SU(2) ≃ S³` with radius fixed by phase consistency. -/
def volSU2 (su2Radius : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * su2Radius ^ 3

/-- `SO(3)` is the free twofold quotient of `SU(2)`. -/
def volSO3 (su2Radius : ℝ) : ℝ :=
  volSU2 su2Radius / 2

/-- `RP¹ = U(1) / {±1}` is the free twofold quotient of the phase circle. -/
def volRP1 : ℝ :=
  volU1 / 2

lemma su2Radius_eq_one (su2Radius : ℝ)
    (phaseConsistentRadius : 2 * Real.pi * su2Radius = 2 * Real.pi) : su2Radius = 1 := by
  nlinarith [Real.pi_pos, phaseConsistentRadius]

/-- Paper label: `prop:phase-gate-rank1-volume-rigidity`. The phase-normalized `U(1)` circle has
length `2π`, the induced `SU(2)` volume is `2π²`, and the free twofold quotients halve those
volumes to `π²` and `π`. -/
theorem paper_phase_gate_rank1_volume_rigidity
    (su2Radius : ℝ)
    (phaseConsistentRadius : 2 * Real.pi * su2Radius = 2 * Real.pi) :
    volU1 = 2 * Real.pi ∧ volSU2 su2Radius = 2 * Real.pi ^ 2 ∧
      volSO3 su2Radius = Real.pi ^ 2 ∧ volRP1 = Real.pi := by
  have hr : su2Radius = 1 := su2Radius_eq_one su2Radius phaseConsistentRadius
  have hsu2 : volSU2 su2Radius = 2 * Real.pi ^ 2 := by
    simp [volSU2, hr]
  refine ⟨rfl, hsu2, ?_, ?_⟩
  · calc
      volSO3 su2Radius = volSU2 su2Radius / 2 := rfl
      _ = (2 * Real.pi ^ 2) / 2 := by rw [hsu2]
      _ = Real.pi ^ 2 := by ring
  · calc
      volRP1 = volU1 / 2 := rfl
      _ = (2 * Real.pi) / 2 := by rfl
      _ = Real.pi := by ring

end

end Omega.UnitCirclePhaseArithmetic
