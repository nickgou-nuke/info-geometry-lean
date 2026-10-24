/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MetriplecticMetricRadical

namespace InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem

example : ∀ B : Cl11Matrix ℤ, metricBracket ⟨0, 1, 1, 0⟩ B = 0 := by
  exact (metricBracket_radical_iff _).2 ⟨rfl, rfl, rfl⟩

example : metricBracket (⟨1, 0, 0, -1⟩ : Cl11Matrix ℝ) ⟨1, 0, 0, -1⟩ = 2 := by
  norm_num [metricBracket]

example : metricBracket (⟨1, 0, 0, 1⟩ : Cl11Matrix ℝ) ⟨1, 0, 0, 1⟩ = -2 := by
  norm_num [metricBracket]

#print axioms metricBracket_radical_iff
#print axioms metricBracket_of_trace_zero
#print axioms metricBracket_self_of_trace_zero
#print axioms metricBracket_nonneg_of_trace_zero
#print axioms metricBracket_self_zero_iff_radical
#print axioms metricBracket_not_positiveSemidefinite

end InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem
