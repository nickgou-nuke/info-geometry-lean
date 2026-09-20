import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Millennium.YangMillsMassGapAudit

structure PositiveEnergyState where
  kineticSquared : ℝ
  couplingSquared : ℝ
  kinetic_nonneg : 0 ≤ kineticSquared
  coupling_pos : 0 < couplingSquared

def totalSquared (state : PositiveEnergyState) : ℝ :=
  state.kineticSquared + state.couplingSquared

theorem totalSquared_pos (state : PositiveEnergyState) :
    0 < totalSquared state :=
  add_pos_of_nonneg_of_pos state.kinetic_nonneg state.coupling_pos

theorem coupling_le_totalSquared (state : PositiveEnergyState) :
    state.couplingSquared ≤ totalSquared state := by
  exact le_add_of_nonneg_left state.kinetic_nonneg

theorem arbitrarily_small_positive_energy (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ state : PositiveEnergyState, 0 < totalSquared state ∧ totalSquared state < epsilon := by
  refine ⟨⟨0, epsilon / 2, le_rfl, by positivity⟩, ?_⟩
  dsimp [totalSquared]
  constructor <;> linarith

theorem no_uniform_positive_lower_bound :
    ¬ ∃ gap : ℝ, 0 < gap ∧ ∀ state : PositiveEnergyState, gap ≤ totalSquared state := by
  rintro ⟨gap, positive, lowerBound⟩
  obtain ⟨state, _, belowGap⟩ := arbitrarily_small_positive_energy gap positive
  exact (not_le_of_gt belowGap) (lowerBound state)

theorem lower_bound_of_uniform_coupling_bound {Index : Type*}
    (states : Index → PositiveEnergyState) (gap : ℝ)
    (couplingBound : ∀ index, gap ≤ (states index).couplingSquared) :
    ∀ index, gap ≤ totalSquared (states index) := by
  intro index
  exact (couplingBound index).trans (coupling_le_totalSquared (states index))

end InfoGeometry.Millennium.YangMillsMassGapAudit
