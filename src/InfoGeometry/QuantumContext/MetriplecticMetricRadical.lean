/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MetriplecticChiralCl11

/-! # Radical and trace-zero restriction of the coordinate symmetric form

The form from `MetriplecticChiralCl11` is indefinite on its full carrier.
Its trace-zero real restriction is nonnegative, with exactly the same radical.
These statements concern that existing coordinate form, not a Clifford action
or a construction of metriplectic dynamics.
-/

namespace InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem

/-- The radical is the symmetric off-diagonal line, over any commutative ring. -/
theorem metricBracket_radical_iff {R : Type*} [CommRing R] (A : Cl11Matrix R) :
    (∀ B, metricBracket A B = 0) ↔
      A.m11 = 0 ∧ A.m22 = 0 ∧ A.m12 = A.m21 := by
  constructor
  · intro h
    have h11 := h ⟨0, 0, 0, 1⟩
    have h22 := h ⟨1, 0, 0, 0⟩
    have h12 := h ⟨0, 1, 0, 0⟩
    simpa [metricBracket, sub_eq_zero] using And.intro h11 (And.intro h22 h12)
  · rintro ⟨h11, h22, h12⟩ B
    simp [metricBracket, h11, h22, h12]

/-- On trace-zero inputs the form is a weighted dot product in two coordinates. -/
theorem metricBracket_of_trace_zero {R : Type*} [CommRing R]
    (A B : Cl11Matrix R) (hA : Cl11Matrix.trace A = 0)
    (hB : Cl11Matrix.trace B = 0) :
    metricBracket A B =
      (A.m12 - A.m21) * (B.m12 - B.m21) + 2 * A.m11 * B.m11 := by
  have ha : A.m22 = -A.m11 := eq_neg_of_add_eq_zero_right hA
  have hb : B.m22 = -B.m11 := eq_neg_of_add_eq_zero_right hB
  simp only [metricBracket, ha, hb]
  ring

/-- Exact sum of squares on the trace-zero real restriction. -/
theorem metricBracket_self_of_trace_zero (A : Cl11Matrix ℝ)
    (hA : Cl11Matrix.trace A = 0) :
    metricBracket A A = (A.m12 - A.m21) ^ 2 + 2 * A.m11 ^ 2 := by
  rw [metricBracket_of_trace_zero A A hA hA]
  ring

/-- The trace-zero restriction is positive semidefinite. -/
theorem metricBracket_nonneg_of_trace_zero (A : Cl11Matrix ℝ)
    (hA : Cl11Matrix.trace A = 0) : 0 ≤ metricBracket A A := by
  rw [metricBracket_self_of_trace_zero A hA]
  positivity

/-- On the trace-zero real restriction, self-nullity is exactly radical membership. -/
theorem metricBracket_self_zero_iff_radical (A : Cl11Matrix ℝ)
    (hA : Cl11Matrix.trace A = 0) :
    metricBracket A A = 0 ↔ ∀ B, metricBracket A B = 0 := by
  constructor
  · intro h
    rw [metricBracket_self_of_trace_zero A hA] at h
    have h11 : A.m11 = 0 := by nlinarith [sq_nonneg (A.m12 - A.m21)]
    have h12 : A.m12 = A.m21 := by nlinarith [sq_nonneg A.m11]
    apply (metricBracket_radical_iff A).2
    exact ⟨h11, by simpa [Cl11Matrix.trace, h11] using hA, h12⟩
  · intro h
    exact h A

end InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem
