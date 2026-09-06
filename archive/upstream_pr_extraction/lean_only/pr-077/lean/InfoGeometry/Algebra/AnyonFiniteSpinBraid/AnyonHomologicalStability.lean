import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSUSYBlocks

noncomputable section

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

open InfoGeometry.Algebra.FiniteSUSY

/-- The finite Witten-index trace used by the braid-stability gate. -/
def witten_index_trace : ℂ :=
  finiteWittenTrace 1 1

/-- Kernel-checked vanishing of the finite Witten-index trace. -/
theorem witten_index_trace_vanishes : witten_index_trace = 0 := by
  simpa [witten_index_trace] using finiteWittenTrace_eq_zero_of_equal 1

/--
A minimal stability gate: the unpaired leakage scalar is represented by the
same finite Witten-index trace.  This is an algebraic isolation valve, not a
spectral or model-completeness theorem.
-/
abbrev HomologicalBraidStability := ℂ

namespace HomologicalBraidStability

/-- Compatibility accessor for the native complex leakage scalar. -/
abbrev unpairedLeak (stable : HomologicalBraidStability) : ℂ := stable

end HomologicalBraidStability

namespace HomologicalBraidStability

variable (stable : HomologicalBraidStability)

/-- Vanishing Witten index is part of the recorded stability gate. -/
theorem witten_zero : witten_index_trace = 0 :=
  witten_index_trace_vanishes

/-- The recorded unpaired-leak scalar vanishes through the finite Witten gate. -/
theorem no_unpaired_leak
    (h_unpaired_eq_witten : stable.unpairedLeak = witten_index_trace) :
    stable.unpairedLeak = 0 := by
  rw [h_unpaired_eq_witten, witten_index_trace_vanishes]

end HomologicalBraidStability

/-- Canonical finite stability gate for the two-state SUSY block. -/
def canonicalHomologicalBraidStability : HomologicalBraidStability :=
  witten_index_trace

/-- The canonical finite braid-stability gate has no unpaired leakage. -/
theorem canonical_no_unpaired_leak : canonicalHomologicalBraidStability.unpairedLeak = 0 :=
  canonicalHomologicalBraidStability.no_unpaired_leak rfl

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
