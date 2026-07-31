import Mathlib.Tactic

namespace Omega.Discussion

/-- Concrete GC audit data, represented by its trace sequence. -/
structure GcAuditDatum where
  traceSeq : ℕ → ℤ

/-- The trace-sequence functor on GC audit data. -/
def gcTrSeq (A : GcAuditDatum) : ℕ → ℤ :=
  A.traceSeq

/-- The concrete output of the audit interface is its trace sequence. -/
def gcZetaDet (A : GcAuditDatum) : ℕ → ℤ :=
  gcTrSeq A

/-- Equality of the concrete GC outputs is exactly equality of the trace sequences. -/
theorem paper_discussion_gc_equivalence_characterization
    (A B : GcAuditDatum) :
    gcZetaDet A = gcZetaDet B ↔
      gcTrSeq A = gcTrSeq B := by
  simpa [gcZetaDet]

end Omega.Discussion
