import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

universe u v

/-- Paper label: `prop:unitary-two-integer-reproducible`. A deterministic certificate backend is
reproducible because the input fixes the computed output, and replay is just recomputation on
that same output. -/
theorem paper_unitary_two_integer_reproducible {α : Type u}
    {Output : Type v} (certify : α → Output) (replay : α → Output → Prop)
    (replay_certify : ∀ u, replay u (certify u)) (u : α) :
    ∃! out, certify u = out ∧ replay u out := by
  refine ⟨certify u, ?_, ?_⟩
  · exact ⟨rfl, replay_certify u⟩
  · intro out hout
    exact hout.1.symm

end Omega.UnitCirclePhaseArithmetic
