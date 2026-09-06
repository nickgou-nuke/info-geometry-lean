import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Arithmetic.SpectralDistance
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-!
# Spectral Gap — Strict Contraction of the Primon Gas Modular Flow

The Bost-Connes Hamiltonian H = diag(log n) on ℓ²(ℕ^+) has vacuum |1⟩
with eigenvalue 0. The spectral gap to the first excited state |2⟩ is
log 2 > 0.

On the excited subspace ℓ²({n ≥ 2}):
    |n^{-s}| = n^{-Re(s)} < 1   for Re(s) > 0, n ≥ 2

The strict contraction ‖e^{-sH}|_{n≥2}‖ ≤ 2^{-Re(s)} < 1 proves
exponential decay of correlations to the KMS ground state.

At `Re(s) = 0`, the scalar factor `|2^{-it}|` has modulus `1`, so the
positive-real-part contraction estimate no longer applies.  This elementary
bound is separate from any Lee--Yang or Riemann-hypothesis statement.

## The Spectral Gap Typeclass

    HasSpectralGap H_op gap where
      gap_pos : 0 < gap
      strict_contraction : ∀ s > 0, ‖exp(-s·H)‖ ≤ exp(-s·gap)

For the primon gas: gap = log 2.

## Physical Meaning

- Mass gap log 2 = first excitation energy above the vacuum
- Exponential decay rate 2^{-Re(s)} = correlation length 1/log 2
- Re(s) → ∞: KMS state localizes on |1⟩, ζ(s) → 1
- Re(s) → 0: ergodic, all states equally weighted
- Re(s) = 0: the displayed positive-real-part contraction estimate degenerates
-/

open Complex
open Real

namespace InfoGeometry.Arithmetic.SpectralGap

/--
The spectral gap of the primon gas: log 2 > 0.

On the excited subspace ℓ²({n ≥ 2}):
    |n^{-s}| = n^{-Re(s)} ≤ 2^{-Re(s)} < 1   for Re(s) > 0
-/
theorem primon_gap_pos : 0 < Real.log 2 := by
  exact Real.log_pos (by norm_num : 1 < (2 : ℝ))

/--
For n ≥ 2 and Re(s) > 0: n^{-Re(s)} ≤ 2^{-Re(s)} < 1.

The contraction factor is 2^{-Re(s)} — exponential decay at rate log 2.
-/
theorem primon_norm_bound (s : ℂ) (hσ : s.re > 0) (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ (-s.re) < 1 := by
  have hn_one_lt : 1 < (n : ℝ) := by
    have h2 : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hn_pos : 0 ≤ (n : ℝ) := by linarith
  -- n^{-σ} = 1/n^{σ} < 1 because n^{σ} > 1 for n > 1, σ > 0
  rw [Real.rpow_neg hn_pos]
  have h_npow_gt_one : 1 < (n : ℝ) ^ s.re := by
    exact Real.one_lt_rpow hn_one_lt hσ
  exact inv_lt_one_of_one_lt₀ h_npow_gt_one

/--
The spectral contraction lemma: on the excited subspace, the norm
converges to 0 as Re(s) → ∞, contracts strictly for Re(s) > 0,
and the displayed scalar contraction estimate degenerates at `Re(s) = 0`.
This file proves only the scalar finite-mode inequality below.
-/
theorem spectral_contraction_on_excited_subspace (s : ℂ) (hσ : s.re > 0) (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- For base ≥ 2 and exponent ≤ 0: larger base → smaller value
  have h_exp_nonpos : -s.re ≤ 0 := by linarith [hσ]
  exact Real.rpow_le_rpow_of_nonpos zero_lt_two hn2 h_exp_nonpos

/-
**Boundary note.**

The Cayley/Lee--Yang/RH interpretations are not proved in this file.  The
formal content here is the positivity of `log 2` and the scalar estimate
`n^{-Re(s)} < 1` for `n ≥ 2` and `Re(s) > 0`.
-/

end InfoGeometry.Arithmetic.SpectralGap
