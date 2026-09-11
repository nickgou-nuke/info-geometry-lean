import Mathlib.Analysis.Fourier.ZMod
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

namespace InfoGeometry.LLM

/-! Native Mathlib finite Fourier bridge for cyclic positions. -/

noncomputable def zmodFourierKernel {n : ℕ} [NeZero n]
    (χ : AddChar (ZMod n) ℂ) (t s : ZMod n) : ℂ :=
  χ (t - s)

theorem zmodFourierKernel_translation_invariant {n : ℕ} [NeZero n]
    (χ : AddChar (ZMod n) ℂ) (t s a : ZMod n) :
    zmodFourierKernel χ (t + a) (s + a) = zmodFourierKernel χ t s := by
  simp [zmodFourierKernel, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

theorem zmodFourierKernel_zero {n : ℕ} [NeZero n]
    (χ : AddChar (ZMod n) ℂ) (t : ZMod n) :
    zmodFourierKernel χ t t = 1 := by
  simp [zmodFourierKernel]

theorem zmodDft_apply_as_character_sum {n : ℕ} [NeZero n]
    (Φ : ZMod n → ℂ) (k : ZMod n) :
    ZMod.dft Φ k = ∑ j : ZMod n, ZMod.stdAddChar (-(j * k)) • Φ j := by
  exact ZMod.dft_apply Φ k

theorem zmodDft_inverse_left {n : ℕ} [NeZero n]
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (Φ : ZMod n → E) :
    ZMod.dft.symm (ZMod.dft Φ) = Φ := by
  exact ZMod.dft.left_inv Φ

theorem zmodDft_inverse_right {n : ℕ} [NeZero n]
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (Ψ : ZMod n → E) :
    ZMod.dft (ZMod.dft.symm Ψ) = Ψ := by
  exact ZMod.dft.right_inv Ψ

end InfoGeometry.LLM
