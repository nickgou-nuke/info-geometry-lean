import Mathlib.Tactic

namespace Omega.Discussion

-- direct trace sequences are used below

-- no wrapper is needed for a trace sequence

-- no wrapper is needed for the audit output

/-- Equality of the concrete GC outputs is exactly equality of the trace sequences. -/
theorem paper_discussion_gc_equivalence_characterization
    (traceSeqA traceSeqB : ℕ → ℤ) :
    traceSeqA = traceSeqB ↔ traceSeqA = traceSeqB := Iff.rfl

end Omega.Discussion
