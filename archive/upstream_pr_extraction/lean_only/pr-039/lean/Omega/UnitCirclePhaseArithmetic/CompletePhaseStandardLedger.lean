import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The visible ledger rank of the standard prototype. -/
def visibleLedger (rank : ℕ) : ℕ :=
  rank

/-- The supernatural modulus is trivial exactly when the stored modulus vanishes. -/
def modulusTrivial (modulus : ℕ) : Prop :=
  modulus = 0

/-- The register side matches the visible rank except in the trivial-modulus collapse. -/
def registerLedger (rank modulus : ℕ) : ℕ :=
  if modulus = 0 then 0 else rank

/-- Paper label: `prop:unit-circle-complete-phase-standard-ledger`. -/
theorem paper_unit_circle_complete_phase_standard_ledger (rank modulus : ℕ) :
    visibleLedger rank = rank ∧ (¬ modulusTrivial modulus → registerLedger rank modulus = rank) ∧
      (modulusTrivial modulus → registerLedger rank modulus = 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    unfold modulusTrivial at h
    simp [registerLedger, h]
  · intro h
    unfold modulusTrivial at h
    simp [registerLedger, h]

end Omega.UnitCirclePhaseArithmetic
