/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Convergent kernels for the even and odd powers of an exponential

For every element of a complete real normed algebra, the two factorial series
`evenExpKernel Z` and `oddExpKernel Z` converge. Their values at `Z = H ^ 2`
give the exponential of `H` without choosing a square root or dividing by `H`.

The parity refers to powers of `H`. It does not assert that either summand
has a particular parity for a separately chosen algebra grading.
-/

noncomputable section

namespace InfoGeometry.Analysis.EvenOddExponential

open scoped BigOperators

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The everywhere convergent kernel with coefficients `1 / (2 k)!`. -/
def evenExpKernel (Z : A) : A :=
  ∑' k : ℕ, (Nat.factorial (2 * k) : ℝ)⁻¹ • Z ^ k

/-- The everywhere convergent kernel with coefficients `1 / (2 k + 1)!`.
Its value at zero is one, so no inverse or removable singularity is required. -/
def oddExpKernel (Z : A) : A :=
  ∑' k : ℕ, (Nat.factorial (2 * k + 1) : ℝ)⁻¹ • Z ^ k

private theorem norm_factorial_term_le (Z : A) (k m : ℕ) (hkm : k ≤ m) :
    ‖(Nat.factorial m : ℝ)⁻¹ • Z ^ k‖ ≤
      ‖(Nat.factorial k : ℝ)⁻¹ • Z ^ k‖ := by
  have hfac : (Nat.factorial k : ℝ) ≤ (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.factorial_le hkm
  rw [norm_smul, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (Nat.factorial m : ℝ)⁻¹),
    Real.norm_of_nonneg (by positivity : 0 ≤ (Nat.factorial k : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) hfac) (norm_nonneg _)

/-- Absolute convergence follows by comparison with the ordinary exponential
series at the same algebra element. -/
theorem summable_norm_evenExpKernel (Z : A) :
    Summable (fun k : ℕ => ‖(Nat.factorial (2 * k) : ℝ)⁻¹ • Z ^ k‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) Z)
  exact norm_factorial_term_le Z k (2 * k) (by omega)

/-- Absolute convergence of the odd-power coefficient kernel, including at
singular or nilpotent algebra elements. -/
theorem summable_norm_oddExpKernel (Z : A) :
    Summable (fun k : ℕ => ‖(Nat.factorial (2 * k + 1) : ℝ)⁻¹ • Z ^ k‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) Z)
  exact norm_factorial_term_le Z k (2 * k + 1) (by omega)

@[simp] theorem evenExpKernel_zero : evenExpKernel (0 : A) = 1 := by
  rw [evenExpKernel, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

@[simp] theorem oddExpKernel_zero : oddExpKernel (0 : A) = 1 := by
  rw [oddExpKernel, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

/-- A commuting element also commutes with the entire even-power kernel. -/
theorem commute_evenExpKernel {W Z : A} (h : Commute W Z) :
    Commute W (evenExpKernel Z) := by
  exact Commute.tsum_right W fun k => (h.pow_right k).smul_right _

/-- A commuting element also commutes with the entire odd-power kernel. -/
theorem commute_oddExpKernel {W Z : A} (h : Commute W Z) :
    Commute W (oddExpKernel Z) := by
  exact Commute.tsum_right W fun k => (h.pow_right k).smul_right _

variable [CompleteSpace A]

theorem summable_evenExpKernel (Z : A) :
    Summable (fun k : ℕ => (Nat.factorial (2 * k) : ℝ)⁻¹ • Z ^ k) :=
  (summable_norm_evenExpKernel Z).of_norm

theorem summable_oddExpKernel (Z : A) :
    Summable (fun k : ℕ => (Nat.factorial (2 * k + 1) : ℝ)⁻¹ • Z ^ k) :=
  (summable_norm_oddExpKernel Z).of_norm

/-- The genuine norm-convergent exponential splits by the parity of its powers.
The algebra need not be commutative, and `H` need not be invertible. -/
theorem exp_eq_evenExpKernel_add_mul_oddExpKernel (H : A) :
    NormedSpace.exp H = evenExpKernel (H ^ 2) + H * oddExpKernel (H ^ 2) := by
  have he : HasSum
      (fun k : ℕ => (Nat.factorial (2 * k) : ℝ)⁻¹ • H ^ (2 * k))
      (evenExpKernel (H ^ 2)) := by
    simpa only [evenExpKernel, pow_mul] using
      (summable_evenExpKernel (H ^ 2)).hasSum
  have ho : HasSum
      (fun k : ℕ => (Nat.factorial (2 * k + 1) : ℝ)⁻¹ • H ^ (2 * k + 1))
      (H * oddExpKernel (H ^ 2)) := by
    convert (summable_oddExpKernel (H ^ 2)).hasSum.mul_left H using 1
    · ext k
      rw [mul_smul_comm, ← pow_mul, ← pow_succ']
    · rfl
  exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) H).unique
    (he.even_add_odd ho)

/-- The negative exponential uses the same kernels and reverses only the
odd-power summand. -/
theorem exp_neg_eq_evenExpKernel_sub_mul_oddExpKernel (H : A) :
    NormedSpace.exp (-H) = evenExpKernel (H ^ 2) - H * oddExpKernel (H ^ 2) := by
  simpa only [neg_sq, neg_mul, sub_eq_add_neg] using
    exp_eq_evenExpKernel_add_mul_oddExpKernel (-H)

end InfoGeometry.Analysis.EvenOddExponential
