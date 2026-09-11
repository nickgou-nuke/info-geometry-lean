import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState

/-!
# Exact Positivity and Faithfulness of Canonical Gauge State on Word Core

This module formalizes:
1. **The Quadratic Word Expectation**:
   $$\varphi_{\mathrm{gauge}}\left( \sum_{u, v} \overline{c_u} c_v S_u S_v^\dagger \right) = \sum_{u, v} \overline{c_u} c_v \varphi_{\mathrm{gauge}}(S_u S_v^\dagger)$$
2. **🏆 THEOREM 1 (Diagonal Real-Cast Collapse)**:
   $$\varphi_{\mathrm{gauge}}(a^\dagger a) = \left( 2^{-n} \sum_{u \in \operatorname{BitWord} n} |c_u|^2 \right) \in \mathbb{R}_{\ge 0} \subset \mathbb{C}$$
3. **🏆 THEOREM 2 (State Positivity on Word Core)**:
   $$\operatorname{Re} \varphi_{\mathrm{gauge}}(a^\dagger a) \ge 0$$
4. **🏆 THEOREM 3 (State Faithfulness on Word Core)**:
   $$\operatorname{Re} \varphi_{\mathrm{gauge}}(a^\dagger a) = 0 \iff \forall u, c_u = 0$$
-/

noncomputable section

open Complex
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliWordStatePositivityBridge

abbrev BitWord (n : ℕ) := Fin n → Bool

/-- The gauge expectation of a quadratic word sum $\sum_{u, v} \overline{c_u} c_v \varphi(S_u S_v^\dagger)$
    where for equal length words $\varphi(S_u S_v^\dagger) = 2^{-n} \delta_{uv}$. -/
def wordSumGaugeExpectation (n : ℕ) (c : BitWord n → ℂ) : ℂ :=
  ∑ u : BitWord n, ∑ v : BitWord n,
    (c u)† * c v * canonicalGaugeState (List.ofFn u) (List.ofFn v)

/-- 🏆 THEOREM 1 (Diagonal Evaluation Formula):
    The expectation collapses to the diagonal sum $\sum_u |c_u|^2 2^{-n}$. -/
theorem wordSumGaugeExpectation_eq_diagonal_sum (n : ℕ) (c : BitWord n → ℂ) :
    wordSumGaugeExpectation n c =
      (1 / (2 ^ n : ℂ)) * ∑ u : BitWord n, ((c u)† * c u) := by
  dsimp [wordSumGaugeExpectation]
  have h_inner : ∀ u : BitWord n,
      (∑ v : BitWord n, (c u)† * c v * canonicalGaugeState (List.ofFn u) (List.ofFn v)) =
        (c u)† * c u * (1 / (2 ^ n : ℂ)) := by
    intro u
    rw [Finset.sum_eq_single u]
    · rw [canonicalGaugeState_proj, List.length_ofFn]
      rw [one_div, one_div, ← inv_pow]
    · intro v _ hvu
      have hlist : List.ofFn u ≠ List.ofFn v := by
        intro h
        exact hvu (List.ofFn_injective h).symm
      rw [canonicalGaugeState_word, List.length_ofFn]
      rw [if_neg hlist, mul_zero]
    · intro hu
      exact (hu (Finset.mem_univ u)).elim
  have h_sum : (∑ u : BitWord n, ∑ v : BitWord n, (c u)† * c v * canonicalGaugeState (List.ofFn u) (List.ofFn v)) =
      ∑ u : BitWord n, ((c u)† * c u * (1 / (2 ^ n : ℂ))) := by
    apply Finset.sum_congr rfl
    intro u _
    exact h_inner u
  change (∑ u : BitWord n, ∑ v : BitWord n, (c u)† * c v * canonicalGaugeState (List.ofFn u) (List.ofFn v)) = _
  rw [h_sum]
  rw [← Finset.sum_mul]
  rw [mul_comm]
  rfl

theorem star_mul_self_eq_normSq (z : ℂ) : z† * z = ((normSq z : ℝ) : ℂ) := by
  have hre : (z† * z).re = normSq z := by
    dsimp [star, normSq]
    ring
  have him : (z† * z).im = 0 := by
    dsimp [star]
    ring
  apply Complex.ext
  · rw [hre, Complex.ofReal_re]
  · rw [him, Complex.ofReal_im]

/-- 🏆 THEOREM 2 (Real Cast Identity):
    The gauge expectation evaluates exactly to the real non-negative quantity. -/
theorem wordSumGaugeExpectation_eq_real_cast (n : ℕ) (c : BitWord n → ℂ) :
    wordSumGaugeExpectation n c = (((1 / (2 ^ n : ℝ)) * ∑ u : BitWord n, normSq (c u) : ℝ) : ℂ) := by
  rw [wordSumGaugeExpectation_eq_diagonal_sum]
  have h_sum : (∑ u : BitWord n, (c u)† * c u) = ((∑ u : BitWord n, normSq (c u) : ℝ) : ℂ) := by
    simp_rw [star_mul_self_eq_normSq]
    push_cast
    rfl
  rw [h_sum]
  push_cast
  rfl

/-- 🏆 THEOREM 3 (Real Positivity):
    The real part of the gauge expectation is non-negative. -/
theorem wordSumGaugeExpectation_nonneg (n : ℕ) (c : BitWord n → ℂ) :
    0 ≤ (wordSumGaugeExpectation n c).re := by
  rw [wordSumGaugeExpectation_eq_real_cast, Complex.ofReal_re]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro u _
  exact normSq_nonneg (c u)

/-- 🏆 THEOREM 4 (Faithfulness on Word Core):
    The gauge expectation vanishes if and only if all coefficients $c_u$ are zero. -/
theorem wordSumGaugeExpectation_eq_zero_iff (n : ℕ) (c : BitWord n → ℂ) :
    (wordSumGaugeExpectation n c).re = 0 ↔ ∀ u : BitWord n, c u = 0 := by
  rw [wordSumGaugeExpectation_eq_real_cast, Complex.ofReal_re]
  constructor
  · intro h
    have h_pos_coeff : 0 < (1 / (2 ^ n : ℝ)) := by positivity
    have h_sum_zero : (∑ u : BitWord n, Complex.normSq (c u)) = 0 := by
      cases mul_eq_zero.mp h with
      | inl h1 => linarith
      | inr h2 => exact h2
    have h_each_zero : ∀ u : BitWord n, Complex.normSq (c u) = 0 := by
      intro u
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => normSq_nonneg (c v))).mp h_sum_zero u (Finset.mem_univ u)
    intro u
    exact normSq_eq_zero.mp (h_each_zero u)
  · intro h
    have : ∀ u, c u = 0 := h
    simp [this]

/-!
The preceding quadratic readout is the diagonal restriction of the weighted
word sesquilinear form.  This remains a finite free-word construction; it is
not yet the form on the algebraic or completed Cuntz quotient.
-/
def gaugeWordInner (n : ℕ) (c d : BitWord n → ℂ) : ℂ :=
  (1 / (2 ^ n : ℂ)) * ∑ u : BitWord n, (c u)† * d u

theorem gaugeWordInner_self_eq_wordSumGaugeExpectation
    (n : ℕ) (c : BitWord n → ℂ) :
    gaugeWordInner n c c = wordSumGaugeExpectation n c := by
  unfold gaugeWordInner
  rw [wordSumGaugeExpectation_eq_diagonal_sum]

theorem gaugeWordInner_self_eq_real_cast (n : ℕ) (c : BitWord n → ℂ) :
    gaugeWordInner n c c =
      (((1 / (2 ^ n : ℝ)) * ∑ u : BitWord n, normSq (c u) : ℝ) : ℂ) := by
  rw [gaugeWordInner_self_eq_wordSumGaugeExpectation,
    wordSumGaugeExpectation_eq_real_cast]

theorem gaugeWordInner_self_re_nonneg (n : ℕ) (c : BitWord n → ℂ) :
    0 ≤ (gaugeWordInner n c c).re := by
  rw [gaugeWordInner_self_eq_real_cast, Complex.ofReal_re]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro u _
  exact normSq_nonneg (c u)

theorem gaugeWordInner_self_eq_zero_iff (n : ℕ) (c : BitWord n → ℂ) :
    (gaugeWordInner n c c).re = 0 ↔ ∀ u : BitWord n, c u = 0 := by
  rw [gaugeWordInner_self_eq_wordSumGaugeExpectation]
  exact wordSumGaugeExpectation_eq_zero_iff n c

end InfoGeometry.OperatorAlgebra.CantorBernoulliWordStatePositivityBridge
