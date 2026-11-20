/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import InfoGeometry.Arithmetic.RiemannZetaFiniteFacts

/-!
# An explicit conditional reduction to the Riemann hypothesis

This module uses the existing zeta-facts owner and native Mathlib analysis.
The half-plane nonvanishing premise remains explicit; the external claimed
RH proof is not imported.

The functional equation makes RH equivalent to nonvanishing strictly to the
right of the critical line. Nonvanishing for all Dirichlet L-functions implies
this zeta premise by specializing to the character modulo one.
-/

namespace InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction

/-- Zeta has no zero strictly right of the critical line, away from its pole. -/
def ZetaRightHalfPlaneNonvanishing : Prop :=
  ∀ s : ℂ, (1 : ℝ) / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0

/-- The explicit Dirichlet nonvanishing assertion used as a premise below. -/
def DirichletRightHalfPlaneNonvanishing : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    (1 : ℝ) / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0

/-- A nontrivial zeta zero reflects under `s ↦ 1 - s`. -/
theorem nontrivial_zero_reflect {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (hs1 : s ≠ 1) :
    riemannZeta (1 - s) = 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact RiemannZetaFiniteFacts.riemannZeta_zero_not_on_critical_line.1 hz
  have hgamma : Complex.Gammaℝ s ≠ 0 := by
    intro hg
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
    cases n with
    | zero => exact hs0 (by simpa using hn)
    | succ n =>
        apply htriv
        refine ⟨n, ?_⟩
        simpa only [Nat.cast_add, Nat.cast_one, neg_mul] using hn
  have hcompleted : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hgamma
  have hreflection : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [riemannZeta_def_of_ne_zero hreflection, completedRiemannZeta_one_sub,
    hcompleted, zero_div]

/-- The zero-free half-plane is supplied explicitly; Mathlib supplies the functional equation. -/
theorem riemannHypothesis_of_rightHalfPlane
    (hnv : ZetaRightHalfPlaneNonvanishing) : _root_.RiemannHypothesis := by
  intro s hz htriv hs1
  rcases lt_trichotomy s.re ((1 : ℝ) / 2) with hleft | hline | hright
  · have hs0 : s ≠ 0 := by
      rintro rfl
      exact RiemannZetaFiniteFacts.riemannZeta_zero_not_on_critical_line.1 hz
    have hreflection : (1 : ℂ) - s ≠ 1 := by
      intro h
      exact hs0 (sub_eq_self.mp h)
    have hright' : (1 : ℝ) / 2 < ((1 : ℂ) - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact False.elim
      (hnv (1 - s) hright' hreflection (nontrivial_zero_reflect hz htriv hs1))
  · exact hline
  · exact False.elim (hnv s hright hs1 hz)

/-- RH excludes every zero in the indicated open half-plane. -/
theorem rightHalfPlane_of_riemannHypothesis
    (hRH : _root_.RiemannHypothesis) : ZetaRightHalfPlaneNonvanishing := by
  intro s hright hs1 hz
  have htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hsn⟩
    have hre : s.re = -2 * ((n : ℝ) + 1) := by
      rw [hsn]
      exact RiemannZetaFiniteFacts.trivialZero_real_part n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hline := hRH s hz htriv hs1
  linarith

/-- The right-half-plane assertion is equivalent to RH; it is not an easier assumption. -/
theorem riemannHypothesis_iff_rightHalfPlane :
    _root_.RiemannHypothesis ↔ ZetaRightHalfPlaneNonvanishing :=
  ⟨rightHalfPlane_of_riemannHypothesis, riemannHypothesis_of_rightHalfPlane⟩

/-- The character modulo one identifies the Dirichlet premise with a zeta instance. -/
theorem zetaRightHalfPlane_of_dirichletRightHalfPlane
    (hL : DirichletRightHalfPlaneNonvanishing) : ZetaRightHalfPlaneNonvanishing := by
  intro s hright hs1
  simpa only [DirichletCharacter.LFunction_modOne_eq] using
    hL 1 (1 : DirichletCharacter ℂ 1) s hright (Or.inr hs1)

/-- A conditional implication. No proof of the Dirichlet premise is asserted. -/
theorem riemannHypothesis_of_dirichletRightHalfPlane
    (hL : DirichletRightHalfPlaneNonvanishing) : _root_.RiemannHypothesis :=
  riemannHypothesis_of_rightHalfPlane (zetaRightHalfPlane_of_dirichletRightHalfPlane hL)

/-- The elementary exponent choice in a half-plane limiting argument.

This does not supply an analytic estimate or a zero-free region: it only chooses
a sufficiently small positive parameter once `σ > 1 / 2` is given.
-/
theorem exists_small_exponent (C σ ε₀ : ℝ) (hσ : (1 : ℝ) / 2 < σ)
    (hε₀ : 0 < ε₀) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧ (1 : ℝ) / 2 + C * ε < σ := by
  let ε := min (ε₀ / 2) ((σ - 1 / 2) / (2 * (|C| + 1)))
  have hden : 0 < 2 * (|C| + 1) := by nlinarith [abs_nonneg C]
  have hpos : 0 < ε := lt_min (half_pos hε₀) (div_pos (sub_pos.mpr hσ) hden)
  have hsmall : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₀)
  have hscaled : ε * (2 * (|C| + 1)) ≤ σ - 1 / 2 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hmul : C * ε ≤ |C| * ε := mul_le_mul_of_nonneg_right (le_abs_self C) hpos.le
  exact ⟨ε, hpos, hsmall, by nlinarith⟩

end InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction
