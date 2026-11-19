/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCoupledCorners
import Mathlib.Data.Matrix.Basis
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Nonzero Peirce round trips with only zero in their spectrum

The full real `4 × 4` matrix algebra contains opposite Peirce corners whose
two ordered products are nonzero, square-zero, and different. Their sum and
commutator are also nonzero and square-zero. Consequently, nonzero coupling
does not imply a nonempty nonzero spectrum.

The spectrum calculation uses native algebraic spectrum and polynomial
spectral mapping. It requires neither a diagonal reduction nor an assumption
that the input operators commute. The separately maintained
`PeirceSpine.PeirceOverlapCounterexamples` owner supplies the other boundary:
two nonzero opposite corners can have both ordered products equal to zero.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceRoundTripCounterexamples

open InfoGeometry.Core.PeirceDecomposition

/-- Every nilpotent element of a nontrivial algebra over a field has exactly
the singleton zero as its algebraic spectrum. No finite-dimensional or
commutative-algebra hypothesis is needed. -/
theorem spectrum_eq_singleton_zero_of_nilpotent
    {K A : Type*} [Field K] [Ring A] [Algebra K A] [Nontrivial A]
    {a : A} (ha : IsNilpotent a) : spectrum K a = {0} := by
  apply Set.Subset.antisymm
  · intro r hr
    obtain ⟨n, hn⟩ := ha
    have hpow := spectrum.pow_mem_pow a n hr
    rw [hn, spectrum.zero_eq] at hpow
    exact Set.mem_singleton_iff.mpr
      (eq_zero_of_pow_eq_zero (Set.mem_singleton_iff.mp hpow))
  · intro r hr
    have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
    rw [hr0]
    exact (spectrum.zero_mem_iff K).mpr ha.not_isUnit

private def e (i j : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.single i j 1

private theorem e_mul (i j k l : Fin 4) :
    e i j * e k l = if j = k then e i l else 0 := by
  by_cases h : j = k
  · subst k
    simp [e]
  · rw [ite_eq_right h]
    simpa [e] using Matrix.single_mul_single_of_ne (1 : ℝ) i j k h (1 : ℝ)

/-- Projection onto the first two coordinates. -/
def nilpotentCut : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.single 0 0 1 + Matrix.single 1 1 1

/-- The identity map from the lower two-dimensional sector to the upper one. -/
def nilpotentUpper : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.single 0 2 1 + Matrix.single 1 3 1

/-- The lower corner carries a nonzero square-zero two-dimensional map. -/
def nilpotentLower : Matrix (Fin 4) (Fin 4) ℝ := Matrix.single 2 1 1

theorem nilpotentCut_idempotent : IsIdempotentElem nilpotentCut := by
  change (e 0 0 + e 1 1) * (e 0 0 + e 1 1) = e 0 0 + e 1 1
  simp [mul_add, add_mul, e_mul]

theorem nilpotentUpper_mem : nilpotentUpper ∈ peirce10 nilpotentCut := by
  refine ⟨nilpotentUpper, ?_⟩
  change e 0 2 + e 1 3 =
    (e 0 0 + e 1 1) * (e 0 2 + e 1 3) * (1 - (e 0 0 + e 1 1))
  simp [mul_sub, mul_add, add_mul, e_mul]

theorem nilpotentLower_mem : nilpotentLower ∈ peirce01 nilpotentCut := by
  refine ⟨nilpotentLower, ?_⟩
  change e 2 1 = (1 - (e 0 0 + e 1 1)) * e 2 1 * (e 0 0 + e 1 1)
  simp [sub_mul, mul_add, add_mul, e_mul]

theorem nilpotentUpper_mul_lower :
    nilpotentUpper * nilpotentLower = Matrix.single 0 1 (1 : ℝ) := by
  change (e 0 2 + e 1 3) * e 2 1 = e 0 1
  simp [add_mul, e_mul]

theorem nilpotentLower_mul_upper :
    nilpotentLower * nilpotentUpper = Matrix.single 2 3 (1 : ℝ) := by
  change e 2 1 * (e 0 2 + e 1 3) = e 2 3
  simp [mul_add, e_mul]

theorem nilpotentUpper_mul_lower_ne_zero : nilpotentUpper * nilpotentLower ≠ 0 := by
  rw [nilpotentUpper_mul_lower]
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
  norm_num [Matrix.single] at hentry

theorem nilpotentLower_mul_upper_ne_zero : nilpotentLower * nilpotentUpper ≠ 0 := by
  rw [nilpotentLower_mul_upper]
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 3) h
  norm_num [Matrix.single] at hentry

theorem nilpotentUpper_ne_zero : nilpotentUpper ≠ 0 := by
  intro h
  exact nilpotentUpper_mul_lower_ne_zero (by rw [h, zero_mul])

theorem nilpotentLower_ne_zero : nilpotentLower ≠ 0 := by
  intro h
  exact nilpotentUpper_mul_lower_ne_zero (by rw [h, mul_zero])

theorem nilpotentUpper_lower_not_commute : ¬ Commute nilpotentUpper nilpotentLower := by
  intro h
  have heq := h.eq
  rw [nilpotentUpper_mul_lower, nilpotentLower_mul_upper] at heq
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) heq
  norm_num [Matrix.single] at hentry

theorem nilpotentUpper_mul_lower_sq : (nilpotentUpper * nilpotentLower) ^ 2 = 0 := by
  rw [nilpotentUpper_mul_lower, pow_two]
  change e 0 1 * e 0 1 = 0
  simp [e_mul]

theorem nilpotentLower_mul_upper_sq : (nilpotentLower * nilpotentUpper) ^ 2 = 0 := by
  rw [nilpotentLower_mul_upper, pow_two]
  change e 2 3 * e 2 3 = 0
  simp [e_mul]

theorem nilpotent_jordan_ne_zero :
    nilpotentUpper * nilpotentLower + nilpotentLower * nilpotentUpper ≠ 0 := by
  rw [nilpotentUpper_mul_lower, nilpotentLower_mul_upper]
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
  norm_num [Matrix.single] at hentry

theorem nilpotent_commutator_ne_zero :
    nilpotentUpper * nilpotentLower - nilpotentLower * nilpotentUpper ≠ 0 := by
  intro h
  exact nilpotentUpper_lower_not_commute (sub_eq_zero.mp h)

theorem nilpotent_jordan_sq :
    (nilpotentUpper * nilpotentLower + nilpotentLower * nilpotentUpper) ^ 2 = 0 := by
  rw [nilpotentUpper_mul_lower, nilpotentLower_mul_upper, pow_two]
  change (e 0 1 + e 2 3) * (e 0 1 + e 2 3) = 0
  simp [mul_add, add_mul, e_mul]

theorem nilpotent_commutator_sq :
    (nilpotentUpper * nilpotentLower - nilpotentLower * nilpotentUpper) ^ 2 = 0 := by
  rw [nilpotentUpper_mul_lower, nilpotentLower_mul_upper, pow_two]
  change (e 0 1 - e 2 3) * (e 0 1 - e 2 3) = 0
  simp [mul_sub, sub_mul, e_mul]

theorem nilpotentUpper_mul_lower_spectrum :
    spectrum ℝ (nilpotentUpper * nilpotentLower) = {0} :=
  spectrum_eq_singleton_zero_of_nilpotent ⟨2, nilpotentUpper_mul_lower_sq⟩

theorem nilpotentLower_mul_upper_spectrum :
    spectrum ℝ (nilpotentLower * nilpotentUpper) = {0} :=
  spectrum_eq_singleton_zero_of_nilpotent ⟨2, nilpotentLower_mul_upper_sq⟩

theorem nilpotent_jordan_spectrum :
    spectrum ℝ (nilpotentUpper * nilpotentLower + nilpotentLower * nilpotentUpper) = {0} :=
  spectrum_eq_singleton_zero_of_nilpotent ⟨2, nilpotent_jordan_sq⟩

theorem nilpotent_commutator_spectrum :
    spectrum ℝ (nilpotentUpper * nilpotentLower - nilpotentLower * nilpotentUpper) = {0} :=
  spectrum_eq_singleton_zero_of_nilpotent ⟨2, nilpotent_commutator_sq⟩

end InfoGeometry.OperatorAlgebra.PeirceRoundTripCounterexamples
