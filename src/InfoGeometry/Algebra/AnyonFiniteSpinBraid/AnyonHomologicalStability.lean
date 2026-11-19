/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.FiniteSUSYBlocks

noncomputable section

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

open InfoGeometry.Algebra.FiniteSUSY

/-- The finite Witten-index trace for equal two-state occupancies. -/
def witten_index_trace : ℂ :=
  finiteWittenTrace 1 1

/-- Kernel-checked vanishing of the finite Witten-index trace. -/
theorem witten_index_trace_vanishes : witten_index_trace = 0 := by
  simpa [witten_index_trace] using finiteWittenTrace_eq_zero_of_equal 1

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
