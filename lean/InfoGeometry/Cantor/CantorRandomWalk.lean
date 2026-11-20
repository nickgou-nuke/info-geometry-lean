/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

noncomputable section

/-!
# CantorRandomWalk

Cantor configuration carrier and bit-flip action.

The Cantor carrier is the binary sequence space `ℕ → Bool`. Operator-valued
finite-mode steps are owned by `Cantor.CliffordMarkovOperators`, where they act
through the represented split Clifford algebra on the Fock carrier.
-/

namespace InfoGeometry.Cantor.CantorRandomWalk

/-- Cantor binary sequence space, read as infinitely many occupation bits. -/
abbrev CantorWord : Type :=
  ℕ → Bool

/-- Dirac-sea reference word with every mode unoccupied. -/
def diracSea : CantorWord :=
  fun _ => false

/-- Predicate saying two Cantor words differ at coordinate `n`. -/
def DifferAt (x y : CantorWord) (n : ℕ) : Prop :=
  x n ≠ y n

/-- A singleton bit flip at coordinate `i`. -/
def flipBit (i : ℕ) (x : CantorWord) : CantorWord :=
  fun j => if j = i then !(x j) else x j

/-- The flipped coordinate is negated. -/
@[simp] theorem flipBit_self (i : ℕ) (x : CantorWord) :
    flipBit i x i = !(x i) := by
  simp [flipBit]

/-- Other coordinates are unchanged by a singleton bit flip. -/
theorem flipBit_other {i j : ℕ} (hji : j ≠ i) (x : CantorWord) :
    flipBit i x j = x j := by
  simp [flipBit, hji]

/-- Flipping the same coordinate twice is the identity. -/
@[simp] theorem flipBit_involutive (i : ℕ) (x : CantorWord) :
    flipBit i (flipBit i x) = x := by
  ext j
  by_cases hji : j = i <;> simp [flipBit, hji]

/-- A singleton bit flip always changes the word. -/
theorem flipBit_ne_self (i : ℕ) (x : CantorWord) :
    flipBit i x ≠ x := by
  intro h
  have hi := congrFun h i
  simp [flipBit] at hi

/-- If two Cantor words are unequal, they differ at some coordinate. -/
theorem exists_differAt_of_ne {x y : CantorWord} (hxy : x ≠ y) :
    ∃ n : ℕ, DifferAt x y n := by
  by_contra hnone
  apply hxy
  funext n
  by_contra hd
  exact hnone ⟨n, hd⟩

/--
First coordinate at which two unequal Cantor words differ.

This is the discrete depth readout behind the usual Cantor ultrametric. The
file only uses the depth, not a metric-space instance.
-/
def firstDifference (x y : CantorWord) (hxy : x ≠ y) : ℕ :=
  by
    classical
    exact Nat.find (exists_differAt_of_ne hxy)

/-- The first-difference coordinate really differs. -/
theorem firstDifference_spec (x y : CantorWord) (hxy : x ≠ y) :
    DifferAt x y (firstDifference x y hxy) := by
  classical
  exact Nat.find_spec (exists_differAt_of_ne hxy)

/-- Before the first-difference depth, the two Cantor words agree. -/
theorem agree_before_firstDifference
    (x y : CantorWord) (hxy : x ≠ y) {k : ℕ}
    (hk : k < firstDifference x y hxy) :
    x k = y k := by
  classical
  by_contra hd
  have hle : firstDifference x y hxy ≤ k :=
    Nat.find_min' (exists_differAt_of_ne hxy) hd
  exact (not_le_of_gt hk) hle

/-! ## Random-walk Markov harmonicity and RG trajectory rescaling -/

section MarkovAndRG

open Filter Topology

/-- One-step uniform random-walk Markov averaging operator over the first `n`
bit-flip directions. -/
def cantorMarkovStep (n : ℕ) [NeZero n] (f : CantorWord → ℝ) (x : CantorWord) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, f (flipBit i x)

/-- Discrete Cantor Laplacian `Δ_n f = P_n f - f`. -/
def cantorLaplacian (n : ℕ) [NeZero n] (f : CantorWord → ℝ) (x : CantorWord) : ℝ :=
  cantorMarkovStep n f x - f x

/-- A function is Markov-harmonic on the `n`-mode Cantor walk when `P_n f = f`. -/
def IsCantorHarmonic (n : ℕ) [NeZero n] (f : CantorWord → ℝ) : Prop :=
  ∀ x : CantorWord, cantorMarkovStep n f x = f x

theorem isCantorHarmonic_iff_laplacian_zero (n : ℕ) [NeZero n]
    (f : CantorWord → ℝ) :
    IsCantorHarmonic n f ↔ ∀ x : CantorWord, cantorLaplacian n f x = 0 := by
  simp [IsCantorHarmonic, cantorLaplacian, sub_eq_zero]

theorem cantorMarkovStep_const (n : ℕ) [NeZero n] (c : ℝ) (x : CantorWord) :
    cantorMarkovStep n (fun _ => c) x = c := by
  unfold cantorMarkovStep
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem cantorMarkovStep_add (n : ℕ) [NeZero n] (f g : CantorWord → ℝ)
    (x : CantorWord) :
    cantorMarkovStep n (fun y => f y + g y) x =
      cantorMarkovStep n f x + cantorMarkovStep n g x := by
  unfold cantorMarkovStep
  rw [Finset.sum_add_distrib, mul_add]

theorem cantorMarkovStep_smul (n : ℕ) [NeZero n] (c : ℝ) (f : CantorWord → ℝ)
    (x : CantorWord) :
    cantorMarkovStep n (fun y => c * f y) x = c * cantorMarkovStep n f x := by
  unfold cantorMarkovStep
  rw [← Finset.mul_sum]
  ring

theorem cantorMarkovStep_iter_eq (n : ℕ) [NeZero n] {f : CantorWord → ℝ}
    (hf : IsCantorHarmonic n f) (k : ℕ) (x : CantorWord) :
    (cantorMarkovStep n)^[k] f x = f x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hfun : (cantorMarkovStep n)^[k] f = f := by
      ext y
      exact ih y
    rw [hfun]
    exact hf x

theorem cantorMarkovStep_abs_le (n : ℕ) [NeZero n] {f : CantorWord → ℝ}
    {M : ℝ} (hM : ∀ y, |f y| ≤ M) (x : CantorWord) :
    |cantorMarkovStep n f x| ≤ M := by
  unfold cantorMarkovStep
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  calc
    (n : ℝ)⁻¹ * |∑ i : Fin n, f (flipBit i x)|
        ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |f (flipBit i x)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, M := by
          gcongr with i _
          exact hM (flipBit i x)
    _ = M := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
          rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- Empirical trajectory mean over `N` steps. -/
def trajectoryMean (ξ : ℕ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, ξ k

/-- Kadanoff / statistical renormalization-group block decimation of block size `b`. -/
def rgBlockStep (b : ℕ) (ξ : ℕ → ℝ) (m : ℕ) : ℝ :=
  (b : ℝ)⁻¹ * ∑ j ∈ Finset.range b, ξ (b * m + j)

/-- Exact RG invariance of the empirical trajectory mean under block decimation
`ξ ↦ rgBlockStep b ξ`. -/
theorem trajectoryMean_rgBlockStep (b : ℕ) [NeZero b] (ξ : ℕ → ℝ) (M : ℕ) :
    trajectoryMean (rgBlockStep b ξ) M = trajectoryMean ξ (b * M) := by
  unfold trajectoryMean rgBlockStep
  rw [← Finset.mul_sum]
  have hsum :
      ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range b, ξ (b * m + j) =
        ∑ k ∈ Finset.range (b * M), ξ k := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]
  rw [hsum, Nat.cast_mul, mul_inv]
  ring

/-- Statistical RG convergence: if the empirical trajectory mean converges to `μ`,
then every block-decimated trajectory `rgBlockStep b ξ` converges to the same `μ`. -/
theorem tendsto_trajectoryMean_rgBlockStep {b : ℕ} [NeZero b] {ξ : ℕ → ℝ} {μ : ℝ}
    (hξ : Tendsto (trajectoryMean ξ) atTop (𝓝 μ)) :
    Tendsto (trajectoryMean (rgBlockStep b ξ)) atTop (𝓝 μ) := by
  have hEq : trajectoryMean (rgBlockStep b ξ) = fun M => trajectoryMean ξ (b * M) := by
    ext M
    exact trajectoryMean_rgBlockStep b ξ M
  rw [hEq]
  have hMul : Tendsto (fun M : ℕ => b * M) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, fun M hM => ?_⟩
    exact le_trans hM (Nat.le_mul_of_pos_left M (Nat.pos_of_ne_zero (NeZero.ne b)))
  exact hξ.comp hMul

/-- Diffusive variance rescaling `N⁻¹ * σ_N²`: exact fixed-point invariance
under `N ↦ √N` diffusive normalization. -/
theorem diffusive_rescaling_fixed_point {N : ℕ} (hN : N ≠ 0) (σsq : ℝ) :
    ((Real.sqrt N)⁻¹) ^ 2 * ((N : ℝ) * σsq) = σsq := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [inv_pow, Real.sq_sqrt hNpos.le, ← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]

end MarkovAndRG

end InfoGeometry.Cantor.CantorRandomWalk
