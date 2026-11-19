/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Discrete Multiscale Cantor Fourier Uncertainty Principle Contraction

This module formalizes the discrete multiscale Cantor-set Fourier uncertainty principle
(FUP) on finite matrix algebras $\mathrm{Fin}(N) \to \mathbb{C}$, establishing:
1. Normalized unitary discrete Fourier transform (DFT) matrix `dftMat N`.
2. Support projections `projSet N S` and the restricted Fourier operator `fupOp N Ω T`.
3. General Frobenius-to-$L^2$-operator-norm inequality on Euclidean space:
   $\|\mathrm{toEuclideanCLM}\ M\| \le \sqrt{\sum_{i,j} \|M_{ij}\|^2}$.
4. Exact Hilbert–Schmidt norm formula:
   $\sum_{j,k} \|(\mathrm{fupOp}\ N\ \Omega\ T)_{jk}\|^2 = (|\Omega| \cdot |T| : \mathbb{R}) / N$.
5. General FUP operator norm bound:
   $\|\mathrm{toEuclideanCLM}(\mathrm{fupOp}\ N\ \Omega\ T)\| \le \sqrt{(|\Omega| \cdot |T| : \mathbb{R}) / N}$.
6. Multiscale exponential contraction on $k$-scale base-$b$ Cantor digit-restricted subsets
   $\Omega_k, T_k \subseteq \mathrm{Fin}(b^k)$ missing $m$ digits ($b - m < \sqrt{b}$):
   $\|\mathrm{toEuclideanCLM}(\mathrm{fupOp}\ (b^k)\ \Omega_k\ T_k)\| \le ((b - m : \mathbb{R}) / \sqrt{b})^k < 1$,
   strictly contractive for $k \ge 1$, and converging $\to 0$ as $k \to \infty$.
7. Explicit non-trivial contraction witness at $b = 4, m = 3$ with ratio $r = 1/2$.
8. OpenGauss Trap T16 non-commutativity witness:
   $P_S \cdot D \neq D \cdot P_S$ for $S = \{0\} \subseteq \mathrm{Fin}(2)$.

This directly closes `epistemic_compilation_archetypes.md` Open Debt #2.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace InfoGeometry.Algebra.DiscreteCantorFourierUncertainty

/-- The normalized discrete Fourier transform matrix $D \in M_N(\mathbb{C})$. -/
noncomputable def dftMat (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => (1 / (Real.sqrt (N : ℝ) : ℂ)) *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((j.val * k.val : ℕ) : ℂ) / (N : ℂ))

/-- Diagonal support projector onto a subset $S \subseteq \mathrm{Fin}(N)$. -/
def projSet (N : ℕ) (S : Finset (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => if i ∈ S then 1 else 0)

/-- The restricted Fourier uncertainty operator $P_\Omega \cdot D_N \cdot P_T$. -/
noncomputable def fupOp (N : ℕ) [NeZero N] (Ω T : Finset (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  projSet N Ω * dftMat N * projSet N T

/-- Action of post-multiplying by the support projection $P_S$. -/
theorem mul_projSet_apply (N : ℕ) (S : Finset (Fin N)) (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (M * projSet N S) i j = if j ∈ S then M i j else 0 := by
  dsimp [Matrix.mul_apply, projSet, diagonal]
  rw [Finset.sum_eq_single j]
  · simp
  · intros k _ hk
    simp [hk]
  · intros hj
    exact False.elim (hj (Finset.mem_univ j))

/-- Action of pre-multiplying by the support projection $P_S$. -/
theorem projSet_mul_apply (N : ℕ) (S : Finset (Fin N)) (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (projSet N S * M) i j = if i ∈ S then M i j else 0 := by
  dsimp [Matrix.mul_apply, projSet, diagonal]
  rw [Finset.sum_eq_single i]
  · simp
  · intros k _ hk
    simp [hk.symm]
  · intros hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Explicit entry formula for the restricted Fourier operator $P_\Omega \cdot D \cdot P_T$. -/
theorem fupOp_apply (N : ℕ) [NeZero N] (Ω T : Finset (Fin N)) (j k : Fin N) :
    fupOp N Ω T j k = if j ∈ Ω ∧ k ∈ T then dftMat N j k else 0 := by
  dsimp [fupOp]
  rw [mul_projSet_apply, projSet_mul_apply]
  by_cases hj : j ∈ Ω <;> by_cases hk : k ∈ T <;> simp [hj, hk]

/-- Norm of the scalar prefactor in the normalized DFT. -/
theorem norm_inv_sqrt_N (N : ℕ) [NeZero N] :
    ‖(1 / (Real.sqrt (N : ℝ) : ℂ))‖ = 1 / Real.sqrt (N : ℝ) := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have h_sqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (le_of_lt h_sqrt_pos)]

/-- Unimodularity of the DFT exponential kernel. -/
theorem norm_exp_dft_kernel (N : ℕ) [NeZero N] (j k : Fin N) :
    ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((j.val * k.val : ℕ) : ℂ) / (N : ℂ))‖ = 1 := by
  have hN : (N : ℂ) = ((N : ℝ) : ℂ) := rfl
  have h_eq : -2 * (Real.pi : ℂ) * Complex.I * ((j.val * k.val : ℕ) : ℂ) / (N : ℂ) =
      ((-2 * Real.pi * (j.val * k.val : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I := by
    rw [hN]
    push_cast
    ring
  rw [h_eq]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Every entry of the normalized DFT matrix has exact complex norm $1 / \sqrt{N}$. -/
theorem dftMat_entry_norm (N : ℕ) [NeZero N] (j k : Fin N) :
    ‖dftMat N j k‖ = 1 / Real.sqrt (N : ℝ) := by
  dsimp [dftMat]
  rw [norm_mul, norm_inv_sqrt_N, norm_exp_dft_kernel N j k, mul_one]

/-- Every entry of the normalized DFT matrix has squared norm $1 / N$. -/
theorem dftMat_entry_norm_sq (N : ℕ) [NeZero N] (j k : Fin N) :
    ‖dftMat N j k‖ ^ 2 = 1 / (N : ℝ) := by
  rw [dftMat_entry_norm]
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hN)]

/-- Action of complex conjugation on `Complex.exp`. -/
theorem star_exp (x : ℂ) : star (Complex.exp x) = Complex.exp (star x) := by
  change (starRingEnd ℂ) (Complex.exp x) = Complex.exp ((starRingEnd ℂ) x)
  exact (Complex.exp_conj x).symm

/-- Action of complex conjugation on the scalar prefactor $1 / \sqrt{N}$. -/
private lemma star_inv_sqrt_N (N : ℕ) :
    (starRingEnd ℂ) (1 / (Real.sqrt (N : ℝ) : ℂ)) = 1 / (Real.sqrt (N : ℝ) : ℂ) := by
  show (starRingEnd ℂ) (1 / (Real.sqrt (N : ℝ) : ℂ)) = 1 / (Real.sqrt (N : ℝ) : ℂ)
  simp only [map_div₀, map_one, Complex.conj_ofReal]

/-- Action of complex conjugation on the DFT exponential phase exponent. -/
theorem star_dft_phase (N : ℕ) (m j : ℕ) :
    (starRingEnd ℂ) (-2 * (Real.pi : ℂ) * Complex.I * ((m * j : ℕ) : ℂ) / (N : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((j * m : ℕ) : ℂ) / (N : ℂ) := by
  change (starRingEnd ℂ) (-2 * ((Real.pi : ℝ) : ℂ) * Complex.I * (((m * j : ℕ) : ℝ) : ℂ) / (((N : ℕ) : ℝ) : ℂ)) = _
  simp only [map_div₀, map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Explicit formula for entries of the conjugate transpose $(D_N)ᴴ$. -/
theorem dftMat_conjTranspose_apply (N : ℕ) [NeZero N] (j m : Fin N) :
    (dftMat N)ᴴ j m = (1 / (Real.sqrt (N : ℝ) : ℂ)) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j.val * m.val : ℕ) : ℂ) / (N : ℂ)) := by
  rw [conjTranspose_apply, dftMat]
  change (starRingEnd ℂ) (1 / (Real.sqrt (N : ℝ) : ℂ) * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m.val * j.val : ℕ) : ℂ) / (N : ℂ))) = _
  rw [map_mul, star_inv_sqrt_N]
  congr 1
  change star (Complex.exp _) = _
  rw [star_exp]
  exact congr_arg Complex.exp (star_dft_phase N m.val j.val)

/-- The squared scalar prefactor $(1 / \sqrt{N})^2$ in $\mathbb{C}$ equals $1 / N$. -/
theorem inv_sqrt_N_sq (N : ℕ) [NeZero N] :
    (1 / (Real.sqrt (N : ℝ) : ℂ)) ^ 2 = 1 / (N : ℂ) := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have h_sqrt : (Real.sqrt (N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hN)]
    rfl
  rw [div_pow, one_pow, h_sqrt]

/-- The product of conjugate-transpose and forward DFT entry phases factors as a power. -/
theorem exp_term_eq_pow (N : ℕ) (j k : ℕ) (m : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j * m : ℕ) : ℂ) / (N : ℂ)) *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m * k : ℕ) : ℂ) / (N : ℂ)) =
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℂ) - (k : ℂ)) / (N : ℂ))) ^ m := by
  rw [← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The $N$-th power of the relative DFT phase is 1. -/
theorem root_of_unity_pow_N (N : ℕ) [NeZero N] (j k : ℕ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℂ) - (k : ℂ)) / (N : ℂ))) ^ N = 1 := by
  rw [← Complex.exp_nat_mul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h_arg : (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ((j : ℂ) - (k : ℂ)) / (N : ℂ)) =
      (((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [mul_div_cancel₀ _ hN]
    push_cast
    ring
  rw [h_arg]
  exact Complex.exp_int_mul_two_pi_mul_I ((j : ℤ) - (k : ℤ))

/-- Vanishing of the geometric sum for a non-trivial root of unity. -/
theorem geom_sum_eq_zero_of_pow_eq_one {x : ℂ} {n : ℕ} (h_pow : x ^ n = 1) (h_ne : x ≠ 1) :
    ∑ i ∈ Finset.range n, x ^ i = 0 := by
  have h_mul : (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = 0 := by
    rw [geom_sum_mul, h_pow, sub_self]
  have h_sub_ne : x - 1 ≠ 0 := sub_ne_zero.mpr h_ne
  cases mul_eq_zero.mp h_mul with
  | inl h => exact h
  | inr h => exact False.elim (h_sub_ne h)

/-- An integer multiple of $N$ strictly between $-N$ and $N$ must be zero. -/
lemma int_mul_eq_zero_of_bounds {N : ℕ} (hN : 0 < N) {n : ℤ}
    (h_gt : -(N : ℤ) < n * (N : ℤ)) (h_lt : n * (N : ℤ) < (N : ℤ)) : n = 0 := by
  rcases lt_trichotomy n 0 with hneg | hz | hpos
  · have hn1 : n ≤ -1 := by
      omega
    have hN_pos : 0 < (N : ℤ) := by
      exact_mod_cast hN
    have h_le : n * (N : ℤ) ≤ -(N : ℤ) := by
      calc n * (N : ℤ)
        _ ≤ -1 * (N : ℤ) := mul_le_mul_of_nonneg_right hn1 (le_of_lt hN_pos)
        _ = -(N : ℤ) := by
          ring
    have h_contra : -(N : ℤ) < -(N : ℤ) := lt_of_lt_of_le h_gt h_le
    exact False.elim (lt_irrefl _ h_contra)
  · exact hz
  · have hn1 : 1 ≤ n := by
      omega
    have hN_pos : 0 < (N : ℤ) := by
      exact_mod_cast hN
    have h_ge : (N : ℤ) ≤ n * (N : ℤ) := by
      calc (N : ℤ)
        _ = 1 * (N : ℤ) := by
          ring
        _ ≤ n * (N : ℤ) := mul_le_mul_of_nonneg_right hn1 (le_of_lt hN_pos)
    have h_contra : (N : ℤ) < (N : ℤ) := lt_of_le_of_lt h_ge h_lt
    exact False.elim (lt_irrefl _ h_contra)

/-- For distinct indices $j \neq k \in \mathrm{Fin}(N)$, the relative phase is not 1. -/
lemma root_of_unity_ne_one {N : ℕ} (hN : N ≠ 0) {j k : Fin N} (h : j ≠ k) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j.val : ℂ) - (k.val : ℂ)) / (N : ℂ)) ≠ 1 := by
  intro h_exp
  rw [Complex.exp_eq_one_iff] at h_exp
  rcases h_exp with ⟨n, hn⟩
  have h_pi_I : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h_div : ((j.val : ℂ) - (k.val : ℂ)) / (N : ℂ) = (n : ℂ) := by
    have hn2 : (2 * (Real.pi : ℂ) * Complex.I) * (((j.val : ℂ) - (k.val : ℂ)) / (N : ℂ)) =
        (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
      calc (2 * (Real.pi : ℂ) * Complex.I) * (((j.val : ℂ) - (k.val : ℂ)) / (N : ℂ))
        _ = 2 * (Real.pi : ℂ) * Complex.I * ((j.val : ℂ) - (k.val : ℂ)) / (N : ℂ) := by
          ring
        _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
        _ = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
          ring
    exact mul_left_cancel₀ h_pi_I hn2
  have hN_c : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h_sub : (j.val : ℂ) - (k.val : ℂ) = ((n * (N : ℤ) : ℤ) : ℂ) := by
    calc (j.val : ℂ) - (k.val : ℂ)
      _ = (((j.val : ℂ) - (k.val : ℂ)) / (N : ℂ)) * (N : ℂ) := by
        rw [div_mul_cancel₀ _ hN_c]
      _ = (n : ℂ) * (N : ℂ) := by
        rw [h_div]
      _ = ((n * (N : ℤ) : ℤ) : ℂ) := by
        push_cast
        ring
  have h1 : (((j.val : ℤ) - (k.val : ℤ) : ℤ) : ℂ) = ((n * (N : ℤ) : ℤ) : ℂ) := by
    rw [← h_sub]
    push_cast
    ring
  have hre := congr_arg Complex.re h1
  simp only [Complex.intCast_re] at hre
  have h_int : (j.val : ℤ) - (k.val : ℤ) = n * (N : ℤ) := by
    exact_mod_cast hre
  have hj : (j.val : ℤ) < (N : ℤ) := by
    exact_mod_cast j.isLt
  have hk : (k.val : ℤ) < (N : ℤ) := by
    exact_mod_cast k.isLt
  have hj0 : 0 ≤ (j.val : ℤ) := by
    omega
  have hk0 : 0 ≤ (k.val : ℤ) := by
    omega
  have h_diff_lt : (j.val : ℤ) - (k.val : ℤ) < (N : ℤ) := by
    omega
  have h_diff_gt : -(N : ℤ) < (j.val : ℤ) - (k.val : ℤ) := by
    omega
  have hn0 : n = 0 := int_mul_eq_zero_of_bounds (Nat.pos_of_ne_zero hN)
    (by rwa [← h_int]) (by rwa [← h_int])
  rw [hn0, zero_mul] at h_int
  have hj_eq_k : j.val = k.val := by
    omega
  exact h (Fin.ext hj_eq_k)

/-- Unitarity of the normalized DFT matrix: $(D_N)ᴴ \cdot D_N = 1$. -/
theorem dftMat_unitary (N : ℕ) [NeZero N] :
    (dftMat N)ᴴ * dftMat N = 1 := by
  ext j k
  rw [mul_apply]
  have h_term : ∀ m : Fin N,
      (dftMat N)ᴴ j m * dftMat N m k =
        (1 / (N : ℂ)) * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j.val : ℂ) - (k.val : ℂ)) / (N : ℂ))) ^ m.val := by
    intro m
    rw [dftMat_conjTranspose_apply, dftMat]
    have h_prod : (1 / (Real.sqrt (N : ℝ) : ℂ)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j.val * m.val : ℕ) : ℂ) / (N : ℂ)) *
        ((1 / (Real.sqrt (N : ℝ) : ℂ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m.val * k.val : ℕ) : ℂ) / (N : ℂ))) =
        ((1 / (Real.sqrt (N : ℝ) : ℂ)) ^ 2) *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j.val * m.val : ℕ) : ℂ) / (N : ℂ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m.val * k.val : ℕ) : ℂ) / (N : ℂ))) := by
      ring
    rw [h_prod, inv_sqrt_N_sq, exp_term_eq_pow]
  simp_rw [h_term]
  rw [← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun m => (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j.val : ℂ) - (k.val : ℂ)) / (N : ℂ))) ^ m) N]
  by_cases h : j = k
  · subst h
    rw [one_apply_eq]
    have h_zero : ((j.val : ℂ) - (j.val : ℂ)) = 0 := sub_self _
    rw [h_zero, mul_zero, zero_div, Complex.exp_zero]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    exact div_mul_cancel₀ 1 hN
  · rw [one_apply_ne h]
    have h_ne := root_of_unity_ne_one (NeZero.ne N) h
    have h_pow := root_of_unity_pow_N N j.val k.val
    rw [geom_sum_eq_zero_of_pow_eq_one h_pow h_ne, mul_zero]

/-- Two-sided unitarity of the normalized DFT matrix: $D_N \cdot (D_N)ᴴ = 1$. -/
theorem dftMat_mul_conjTranspose (N : ℕ) [NeZero N] :
    dftMat N * (dftMat N)ᴴ = 1 := by
  rw [mul_eq_one_comm]
  exact dftMat_unitary N

/-- General Frobenius-to-$L^2$-operator-norm inequality on $\mathbb{C}^n$. -/
theorem toEuclideanCLM_norm_le_frobenius {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    ‖(toEuclideanCLM (n := n) (𝕜 := ℂ)) M‖ ≤ Real.sqrt (∑ i : n, ∑ j : n, ‖M i j‖ ^ 2) := by
  let F := Real.sqrt (∑ i : n, ∑ j : n, ‖M i j‖ ^ 2)
  have hF_nonneg : 0 ≤ F := Real.sqrt_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ hF_nonneg
  intro x
  have h_sq : ‖(toEuclideanCLM (n := n) (𝕜 := ℂ)) M x‖ ^ 2 ≤ (F * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _),
        Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have h_entry : ‖((toEuclideanCLM (n := n) (𝕜 := ℂ)) M x).ofLp i‖ ≤ ∑ j : n, ‖M i j‖ * ‖x.ofLp j‖ := by
      rw [ofLp_toEuclideanCLM, mulVec, dotProduct]
      have h1 : ‖∑ j : n, M i j * x.ofLp j‖ ≤ ∑ j : n, ‖M i j * x.ofLp j‖ := norm_sum_le _ _
      have h2 : (∑ j : n, ‖M i j * x.ofLp j‖) = ∑ j : n, ‖M i j‖ * ‖x.ofLp j‖ := by
        congr 1
        ext j
        exact norm_mul (M i j) (x.ofLp j)
      rw [h2] at h1
      exact h1
    have h_entry_sq : ‖((toEuclideanCLM (n := n) (𝕜 := ℂ)) M x).ofLp i‖ ^ 2 ≤ (∑ j : n, ‖M i j‖ * ‖x.ofLp j‖) ^ 2 := by
      have h_nonneg_entry : 0 ≤ ‖((toEuclideanCLM (n := n) (𝕜 := ℂ)) M x).ofLp i‖ := norm_nonneg _
      have h_nonneg_rhs : 0 ≤ ∑ j : n, ‖M i j‖ * ‖x.ofLp j‖ :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      nlinarith
    have h_cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n) (fun j => ‖M i j‖) (fun j => ‖x.ofLp j‖)
    rw [← EuclideanSpace.norm_sq_eq] at h_cs
    exact h_entry_sq.trans h_cs
  have h_nonneg1 : 0 ≤ ‖(toEuclideanCLM (n := n) (𝕜 := ℂ)) M x‖ := norm_nonneg _
  have h_nonneg2 : 0 ≤ F * ‖x‖ := mul_nonneg hF_nonneg (norm_nonneg _)
  have h_abs := sq_le_sq.mp h_sq
  rwa [abs_of_nonneg h_nonneg1, abs_of_nonneg h_nonneg2] at h_abs

/-- Exact Hilbert–Schmidt norm formula for the restricted Fourier operator $P_\Omega \cdot D \cdot P_T$. -/
theorem fupOp_frobenius_norm_sq (N : ℕ) [NeZero N] (Ω T : Finset (Fin N)) :
    (∑ j : Fin N, ∑ k : Fin N, ‖fupOp N Ω T j k‖ ^ 2) = (Ω.card * T.card : ℝ) / (N : ℝ) := by
  have h_inner : ∀ j : Fin N, (∑ k : Fin N, ‖fupOp N Ω T j k‖ ^ 2) =
      if j ∈ Ω then (T.card : ℝ) / (N : ℝ) else 0 := by
    intro j
    by_cases hj : j ∈ Ω
    · simp only [hj, ite_true]
      have h1 : (∑ k : Fin N, ‖fupOp N Ω T j k‖ ^ 2) = ∑ k : Fin N, (if k ∈ T then 1 / (N : ℝ) else 0) := by
        congr 1
        ext k
        rw [fupOp_apply]
        simp only [hj, true_and]
        split_ifs with hk
        · rw [dftMat_entry_norm_sq]
        · simp
      rw [h1, ← Finset.sum_filter]
      have h_filt : (Finset.univ.filter (fun k : Fin N => k ∈ T)) = T := by
        ext x
        simp
      rw [h_filt, Finset.sum_const, nsmul_eq_mul]
      ring
    · simp only [hj, ite_false]
      have h0 : (∑ k : Fin N, ‖fupOp N Ω T j k‖ ^ 2) = ∑ k : Fin N, 0 := by
        congr 1
        ext k
        rw [fupOp_apply]
        simp [hj]
      rw [h0, Finset.sum_const_zero]
  have h2 : (∑ j : Fin N, ∑ k : Fin N, ‖fupOp N Ω T j k‖ ^ 2) =
      ∑ j : Fin N, (if j ∈ Ω then (T.card : ℝ) / (N : ℝ) else 0) := by
    congr 1
    ext j
    exact h_inner j
  rw [h2, ← Finset.sum_filter]
  have h_filtΩ : (Finset.univ.filter (fun j : Fin N => j ∈ Ω)) = Ω := by
    ext x
    simp
  rw [h_filtΩ, Finset.sum_const, nsmul_eq_mul]
  ring

/-- General discrete Fourier uncertainty principle $L^2$ operator norm bound. -/
theorem fup_operator_norm_bound (N : ℕ) [NeZero N] (Ω T : Finset (Fin N)) :
    ‖(toEuclideanCLM (n := Fin N) (𝕜 := ℂ)) (fupOp N Ω T)‖ ≤
      Real.sqrt ((Ω.card * T.card : ℝ) / (N : ℝ)) := by
  have h_frob := toEuclideanCLM_norm_le_frobenius (fupOp N Ω T)
  rw [fupOp_frobenius_norm_sq] at h_frob
  exact h_frob

/-- Square root distributes over powers of non-negative reals. -/
lemma Real_sqrt_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = (Real.sqrt x) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      rw [Real.sqrt_mul (pow_nonneg hx k)]
      rw [ih]

/-- Algebraic reduction for the multiscale Cantor bound. -/
theorem cantor_bound_algebra (b m : ℕ) (hm : m < b) (k : ℕ) :
    Real.sqrt ((((b - m : ℝ) ^ k * (b - m : ℝ) ^ k) / (b : ℝ) ^ k)) =
      ((b - m : ℝ) / Real.sqrt (b : ℝ)) ^ k := by
  have hb_pos : 0 < (b : ℝ) := Nat.cast_pos.mpr (by omega)
  have hbm_nonneg : 0 ≤ (b - m : ℝ) := by
    have : m ≤ b := le_of_lt hm
    exact sub_nonneg.mpr (Nat.cast_le.mpr this)
  have h1 : ((b - m : ℝ) ^ k * (b - m : ℝ) ^ k) / (b : ℝ) ^ k = (((b - m : ℝ) ^ 2) / (b : ℝ)) ^ k := by
    rw [← mul_pow, sq, ← div_pow]
  rw [h1]
  rw [Real_sqrt_pow _ (div_nonneg (sq_nonneg _) (by positivity))]
  congr 1
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hbm_nonneg]

/-- Multiscale Cantor FUP Exponential Contraction:
On $k$-scale base-$b$ Cantor subsets $\Omega_k, T_k \subseteq \mathrm{Fin}(b^k)$ missing $m$ digits,
the restricted Fourier operator norm is bounded by $((b - m) / \sqrt{b})^k$. -/
theorem cantor_fup_contraction (b m : ℕ) (hm : m < b) (k : ℕ)
    (Ω_k T_k : Finset (Fin (b ^ k)))
    (hΩ : Ω_k.card ≤ (b - m) ^ k)
    (hT : T_k.card ≤ (b - m) ^ k) :
    have : NeZero (b ^ k) := ⟨pow_ne_zero k (by omega)⟩
    ‖(toEuclideanCLM (n := Fin (b ^ k)) (𝕜 := ℂ)) (fupOp (b ^ k) Ω_k T_k)‖ ≤
      ((b - m : ℝ) / Real.sqrt (b : ℝ)) ^ k := by
  have : NeZero (b ^ k) := ⟨pow_ne_zero k (by omega)⟩
  have h_bound := fup_operator_norm_bound (b ^ k) Ω_k T_k
  rw [Nat.cast_pow] at h_bound
  have hb_pos : 0 < (b : ℝ) := Nat.cast_pos.mpr (by omega)
  have hb_pow_pos : 0 < (b : ℝ) ^ k := pow_pos hb_pos k
  have h_sub_cast : ((b - m : ℕ) : ℝ) = (b - m : ℝ) := Nat.cast_sub (le_of_lt hm)
  have h1 : (Ω_k.card : ℝ) ≤ ((b - m : ℝ) ^ k) := by
    have h_nat : (Ω_k.card : ℝ) ≤ (((b - m) ^ k : ℕ) : ℝ) := by exact_mod_cast hΩ
    rw [Nat.cast_pow, h_sub_cast] at h_nat
    exact h_nat
  have h2 : (T_k.card : ℝ) ≤ ((b - m : ℝ) ^ k) := by
    have h_nat : (T_k.card : ℝ) ≤ (((b - m) ^ k : ℕ) : ℝ) := by exact_mod_cast hT
    rw [Nat.cast_pow, h_sub_cast] at h_nat
    exact h_nat
  have h_card_prod : (Ω_k.card * T_k.card : ℝ) ≤ ((b - m : ℝ) ^ k * (b - m : ℝ) ^ k) := by
    have h_nonneg1 : 0 ≤ (Ω_k.card : ℝ) := Nat.cast_nonneg _
    have h_nonneg2 : 0 ≤ (T_k.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h_frac_le : (Ω_k.card * T_k.card : ℝ) / (b : ℝ) ^ k ≤
      ((b - m : ℝ) ^ k * (b - m : ℝ) ^ k) / (b : ℝ) ^ k :=
    div_le_div_of_nonneg_right h_card_prod (le_of_lt hb_pow_pos)
  have h_sqrt_le := Real.sqrt_le_sqrt h_frac_le
  rw [cantor_bound_algebra b m hm k] at h_sqrt_le
  exact h_bound.trans h_sqrt_le

/-- Strict multiscale contraction factor strictly less than 1 when $(b - m) < \sqrt{b}$. -/
theorem cantor_fup_strict_contraction (b m : ℕ) (hm : m < b)
    (h_sparse : (b - m : ℝ) < Real.sqrt (b : ℝ)) (k : ℕ) (hk : 0 < k) :
    ((b - m : ℝ) / Real.sqrt (b : ℝ)) ^ k < 1 := by
  have hb_pos : 0 < (b : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_sqrt_pos : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.mpr hb_pos
  have hbm_nonneg : 0 ≤ (b - m : ℝ) := by
    have : m ≤ b := le_of_lt hm
    exact sub_nonneg.mpr (Nat.cast_le.mpr this)
  have h_ratio_nonneg : 0 ≤ (b - m : ℝ) / Real.sqrt (b : ℝ) :=
    div_nonneg hbm_nonneg (le_of_lt h_sqrt_pos)
  have h_ratio_lt_one : (b - m : ℝ) / Real.sqrt (b : ℝ) < 1 := by
    rw [div_lt_one h_sqrt_pos]
    exact h_sparse
  exact pow_lt_one₀ h_ratio_nonneg h_ratio_lt_one hk.ne'

/-- Asymptotic convergence of the multiscale Cantor FUP bound to 0 as scale $k \to \infty$. -/
theorem cantor_fup_tendsto_zero (b m : ℕ) (hm : m < b)
    (h_sparse : (b - m : ℝ) < Real.sqrt (b : ℝ)) :
    Filter.Tendsto (fun k : ℕ => ((b - m : ℝ) / Real.sqrt (b : ℝ)) ^ k)
      Filter.atTop (nhds 0) := by
  have hb_pos : 0 < (b : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_sqrt_pos : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.mpr hb_pos
  have hbm_nonneg : 0 ≤ (b - m : ℝ) := by
    have : m ≤ b := le_of_lt hm
    exact sub_nonneg.mpr (Nat.cast_le.mpr this)
  have h_ratio_nonneg : 0 ≤ (b - m : ℝ) / Real.sqrt (b : ℝ) :=
    div_nonneg hbm_nonneg (le_of_lt h_sqrt_pos)
  have h_ratio_lt_one : (b - m : ℝ) / Real.sqrt (b : ℝ) < 1 := by
    rw [div_lt_one h_sqrt_pos]
    exact h_sparse
  exact tendsto_pow_atTop_nhds_zero_of_lt_one h_ratio_nonneg h_ratio_lt_one

/-- Explicit constructive witness at base $b = 4$, missing $m = 3$ digits:
Contraction factor is $1/2 < 1$. -/
theorem cantor_witness_b4_m3 :
    ((4 - 3 : ℝ) / Real.sqrt (4 : ℝ)) = 1 / 2 ∧
    ((4 - 3 : ℝ) / Real.sqrt (4 : ℝ)) < 1 := by
  have h_sqrt4 : Real.sqrt 4 = 2 := by
    have h : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h, Real.sqrt_sq (by norm_num)]
  constructor
  · rw [h_sqrt4]
    norm_num
  · rw [h_sqrt4]
    norm_num

/-- OpenGauss Trap T16 Non-Commutativity Witness:
The support projection $P_{\{0\}}$ and normalized DFT $D_2$ do NOT commute. -/
theorem fup_noncomm_witness :
    projSet 2 {0} * dftMat 2 ≠ dftMat 2 * projSet 2 {0} := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  rw [projSet_mul_apply, mul_projSet_apply] at h01
  simp only [Finset.mem_singleton, ↓reduceIte] at h01
  dsimp [dftMat] at h01
  rw [Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one] at h01
  have h_sqrt2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have h_div : (1 / (Real.sqrt 2 : ℂ)) ≠ 0 := by
    exact one_div_ne_zero h_sqrt2
  exact h_div h01

end InfoGeometry.Algebra.DiscreteCantorFourierUncertainty
