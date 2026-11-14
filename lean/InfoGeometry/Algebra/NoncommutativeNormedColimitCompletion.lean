/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.NoncommutativeColimitAndSpectralGapSynthesis

/-!
# Analytic & Normed Colimit Completion of the Inductive Bott–Clifford Tower

This module lifts the algebraic directed inductive system `(ClTower n A, cantorEmbed n)`
from `NoncommutativeColimitAndSpectralGapSynthesis` to `[NormedRing A]` and
`UniformSpace.Completion A`:
1. Defines the recursive block-supremum norm `towerNorm n` on `ClTower n A` and proves
   nonnegativity, triangle inequality, and exact isometry under `cantorEmbed` and
   `cantorEmbedIter` (`towerNorm (n + k) (cantorEmbedIter n k X) = towerNorm n X`).
2. Proves the uniform-in-`k` trace and supertrace Lipschitz bounds
   `‖towerTrace (n + k) (cantorEmbedIter n k X)‖ ≤ 2 ^ n * towerNorm n X`.
3. Proves that any `towerNorm`-Cauchy sequence in `ClTower n A` induces a `CauchySeq` of
   traces and supertraces in `A`, converging to a common limit in `UniformSpace.Completion A`
   invariant across all `cantorEmbedIter n k` transitions.
4. Over `[NormedDivisionRing A] [CharZero A]` (or `ℝ`), proves exact sector norm scaling
   for the spectral mass gap Hamiltonian `massGapHamiltonian n μ lam`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeFutureHorizonsTower
open InfoGeometry.Algebra.NoncommutativeColimitAndSpectralGapSynthesis

namespace InfoGeometry.Algebra.NoncommutativeNormedColimitCompletion

universe u

section TowerNorm

variable {A : Type u} [SeminormedRing A]

/-- Recursive block-supremum norm on `ClTower n A`. -/
def towerNorm : ∀ n : ℕ, ClTower n A → ℝ
  | 0,     a => ‖a‖
  | n + 1, M => max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                    (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1)))

lemma towerNorm_nonneg : ∀ (n : ℕ) (X : ClTower n A), 0 ≤ towerNorm n X
  | 0,     a => norm_nonneg a
  | n + 1, M => le_trans (towerNorm_nonneg n (M 0 0)) (le_trans (le_max_left _ _) (le_max_left _ _))

lemma towerNorm_zero : ∀ (n : ℕ), towerNorm n (0 : ClTower n A) = 0
  | 0     => norm_zero
  | n + 1 => by
      dsimp [towerNorm]
      change max (max (towerNorm n (0 : ClTower n A)) (towerNorm n 0))
                 (max (towerNorm n 0) (towerNorm n 0)) = 0
      simp [towerNorm_zero n]

lemma towerNorm_neg : ∀ (n : ℕ) (X : ClTower n A), towerNorm n (-X) = towerNorm n X
  | 0,     a => norm_neg a
  | n + 1, M => by
      dsimp [towerNorm]
      change max (max (towerNorm n (-M 0 0)) (towerNorm n (-M 0 1)))
                 (max (towerNorm n (-M 1 0)) (towerNorm n (-M 1 1))) =
             max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                 (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1)))
      simp [towerNorm_neg n]

lemma towerNorm_add_le : ∀ (n : ℕ) (X Y : ClTower n A),
    towerNorm n (X + Y) ≤ towerNorm n X + towerNorm n Y
  | 0,     a, b => norm_add_le a b
  | n + 1, M, N => by
      dsimp [towerNorm]
      change max (max (towerNorm n (M 0 0 + N 0 0)) (towerNorm n (M 0 1 + N 0 1)))
                 (max (towerNorm n (M 1 0 + N 1 0)) (towerNorm n (M 1 1 + N 1 1))) ≤
             max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                 (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1))) +
             max (max (towerNorm n (N 0 0)) (towerNorm n (N 0 1)))
                 (max (towerNorm n (N 1 0)) (towerNorm n (N 1 1)))
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
      · exact le_trans (towerNorm_add_le n (M 0 0) (N 0 0))
          (add_le_add (le_trans (le_max_left _ _) (le_max_left _ _))
                      (le_trans (le_max_left _ _) (le_max_left _ _)))
      · exact le_trans (towerNorm_add_le n (M 0 1) (N 0 1))
          (add_le_add (le_trans (le_max_right _ _) (le_max_left _ _))
                      (le_trans (le_max_right _ _) (le_max_left _ _)))
      · exact le_trans (towerNorm_add_le n (M 1 0) (N 1 0))
          (add_le_add (le_trans (le_max_left _ _) (le_max_right _ _))
                      (le_trans (le_max_left _ _) (le_max_right _ _)))
      · exact le_trans (towerNorm_add_le n (M 1 1) (N 1 1))
          (add_le_add (le_trans (le_max_right _ _) (le_max_right _ _))
                      (le_trans (le_max_right _ _) (le_max_right _ _)))

/-- `cantorEmbed n` is an exact isometry with respect to `towerNorm`. -/
theorem towerNorm_cantorEmbed (n : ℕ) (X : ClTower n A) :
    towerNorm (n + 1) (cantorEmbed n X) = towerNorm n X := by
  dsimp [towerNorm, cantorEmbed, mat2]
  simp [towerNorm_zero n, max_eq_left (towerNorm_nonneg n X)]

/-- Multi-step transition `cantorEmbedIter n k` is an exact isometry across all scales `n, k : ℕ`. -/
theorem towerNorm_cantorEmbedIter (n k : ℕ) (X : ClTower n A) :
    towerNorm (n + k) (cantorEmbedIter n k X) = towerNorm n X := by
  induction' k with m ih
  · rfl
  · dsimp [cantorEmbedIter]
    change towerNorm (n + m + 1) (cantorEmbed (n + m) (cantorEmbedIter n m X)) = towerNorm n X
    rw [towerNorm_cantorEmbed (n + m), ih]

theorem towerTrace_norm_le : ∀ (n : ℕ) (X : ClTower n A),
    ‖towerTrace n X‖ ≤ (2 ^ n : ℝ) * towerNorm n X
  | 0,     a => by simp [towerTrace, towerNorm]
  | n + 1, M => by
      dsimp [towerTrace, rgTowerDecimate]
      have h00 : towerNorm n (M 0 0) ≤ towerNorm (n + 1) M :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have h11 : towerNorm n (M 1 1) ≤ towerNorm (n + 1) M :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have h_tr : ‖towerTrace n (M 0 0 + M 1 1)‖ ≤
          (2 ^ n : ℝ) * towerNorm n (M 0 0) + (2 ^ n : ℝ) * towerNorm n (M 1 1) := by
        rw [NoncommutativeFutureHorizonsTower.towerTrace_add]
        exact le_trans (norm_add_le _ _)
          (add_le_add (towerTrace_norm_le n (M 0 0)) (towerTrace_norm_le n (M 1 1)))
      have h_2n_nonneg : (0 : ℝ) ≤ (2 ^ n : ℝ) := by positivity
      calc ‖towerTrace n (M 0 0 + M 1 1)‖
        _ ≤ (2 ^ n : ℝ) * towerNorm n (M 0 0) + (2 ^ n : ℝ) * towerNorm n (M 1 1) := h_tr
        _ ≤ (2 ^ n : ℝ) * towerNorm (n + 1) M + (2 ^ n : ℝ) * towerNorm (n + 1) M :=
            add_le_add (mul_le_mul_of_nonneg_left h00 h_2n_nonneg)
                       (mul_le_mul_of_nonneg_left h11 h_2n_nonneg)
        _ = (2 ^ (n + 1) : ℝ) * towerNorm (n + 1) M := by
            rw [pow_succ]; ring

/-- Uniform-in-`k` trace bound along the directed colimit system `cantorEmbedIter n k`. -/
theorem towerTrace_cantorEmbedIter_norm_le (n k : ℕ) (X : ClTower n A) :
    ‖towerTrace (n + k) (cantorEmbedIter n k X)‖ ≤ (2 ^ n : ℝ) * towerNorm n X := by
  rw [(cantor_transition_trace_and_supertrace_compatibility n k X X).2.2.2.2.2.1]
  exact towerTrace_norm_le n X

/-- Uniform-in-`k` supertrace bound along the directed colimit system `cantorEmbedIter n k`. -/
theorem superTrace_cantorEmbedIter_norm_le (n k : ℕ) (X : ClTower n A) :
    ‖superTrace (cantorEmbedIter n k X)‖ ≤ (2 ^ n : ℝ) * towerNorm n X := by
  rw [(cantor_transition_trace_and_supertrace_compatibility n k X X).2.2.2.2.2.2]
  dsimp [superTrace]
  have h_gamma_norm : ∀ m : ℕ, (M : ClTower m A) → towerNorm m (gammaTowerOp m * M) = towerNorm m M := by
    intro m; induction' m with m ih
    · intro a; simp [gammaTowerOp, towerNorm]
    · intro M
      dsimp [towerNorm, gammaTowerOp]
      simp only [mul2_00, mul2_01, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
        zero_mul, add_zero, zero_add]
      have h10 : (-gammaTowerOp m : ClTower m A) * M 1 0 = -(gammaTowerOp m * M 1 0) := by noncomm_ring
      have h11 : (-gammaTowerOp m : ClTower m A) * M 1 1 = -(gammaTowerOp m * M 1 1) := by noncomm_ring
      rw [h10, h11, towerNorm_neg, towerNorm_neg, ih, ih, ih, ih]
  rw [← h_gamma_norm n X]
  exact towerTrace_norm_le n (gammaTowerOp n * X)

end TowerNorm

section CompletionCocone

variable {A : Type u} [NormedRing A]

/-- A `towerNorm`-Cauchy sequence in `ClTower n A`. -/
def IsTowerCauchy (n : ℕ) (f : ℕ → ClTower n A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → towerNorm n (f i - f j) < ε

/-- Any `towerNorm`-Cauchy sequence in `ClTower n A` maps under `towerTrace n` to a
`CauchySeq` in `A`, and hence converges in `UniformSpace.Completion A`, with identical
limits across all `cantorEmbedIter n k` transitions. -/
theorem towerCauchy_trace_completion_cocone (n k : ℕ) (f : ℕ → ClTower n A)
    (hf : IsTowerCauchy n f) :
    CauchySeq (fun m => towerTrace n (f m)) ∧
    CauchySeq (fun m => towerTrace (n + k) (cantorEmbedIter n k (f m))) ∧
    (fun m => ((towerTrace (n + k) (cantorEmbedIter n k (f m)) : A) : UniformSpace.Completion A)) =
      (fun m => ((towerTrace n (f m) : A) : UniformSpace.Completion A)) := by
  have h_eq : (fun m => towerTrace (n + k) (cantorEmbedIter n k (f m))) =
      (fun m => towerTrace n (f m)) := by
    ext m
    exact (cantor_transition_trace_and_supertrace_compatibility n k (f m) (f m)).2.2.2.2.2.1
  have h_cauchy : CauchySeq (fun m => towerTrace n (f m)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have h2n : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    rcases hf (ε / (2 ^ n : ℝ)) (div_pos hε h2n) with ⟨N, hN⟩
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm]
    have h_sub : towerTrace n (f i) - towerTrace n (f j) = towerTrace n (f i - f j) := by
      rw [sub_eq_add_neg, ← NoncommutativeFutureHorizonsTower.towerTrace_neg,
          ← NoncommutativeFutureHorizonsTower.towerTrace_add, sub_eq_add_neg]
    rw [h_sub]
    calc ‖towerTrace n (f i - f j)‖
      _ ≤ (2 ^ n : ℝ) * towerNorm n (f i - f j) := towerTrace_norm_le n (f i - f j)
      _ < (2 ^ n : ℝ) * (ε / (2 ^ n : ℝ)) := mul_lt_mul_of_pos_left (hN i j hi hj) h2n
      _ = ε := mul_div_cancel₀ ε (ne_of_gt h2n)
  refine ⟨h_cauchy, ?_, ?_⟩
  · rw [h_eq]; exact h_cauchy
  · ext m
    exact congrArg ((↑) : A → UniformSpace.Completion A) (congrFun h_eq m)

end CompletionCocone

section SpectralGapNormScaling

/-- Over `ℝ`, `massGapHamiltonian n μ lam` scales the `towerNorm` on the vacuum and
excited sectors by exact eigenvalues `μ` and `μ + lam`. -/
theorem real_massGapHamiltonian_sector_norm_scaling (n μ lam : ℕ) :
    let P_n := (cantorTowerProj n : ClTower n ℝ)
    let Q_n := 1 - P_n
    let H_n := massGapHamiltonian (A := ℝ) n μ lam
    towerNorm n (H_n * P_n) = (μ : ℝ) * towerNorm n P_n ∧
    towerNorm n (H_n * Q_n) = ((μ + lam : ℕ) : ℝ) * towerNorm n Q_n := by
  intro P_n Q_n H_n
  have h_alg := all_scales_mass_gap_hamiltonian_and_excited_pore_fup (A := ℝ) n μ lam
  have h_smul_norm : ∀ (m : ℕ) (c : ℕ) (X : ClTower m ℝ),
      towerNorm m (c • X) = (c : ℝ) * towerNorm m X := by
    intro m; induction' m with m ih
    · intro c x
      dsimp [towerNorm]
      rw [nsmul_eq_mul, abs_mul, Nat.abs_cast]
    · intro c M
      dsimp [towerNorm]
      change max (max (towerNorm m (c • M 0 0)) (towerNorm m (c • M 0 1)))
                 (max (towerNorm m (c • M 1 0)) (towerNorm m (c • M 1 1))) =
             (c : ℝ) * max (max (towerNorm m (M 0 0)) (towerNorm m (M 0 1)))
                           (max (towerNorm m (M 1 0)) (towerNorm m (M 1 1)))
      simp only [ih c]
      have hc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
      simp only [← mul_max_of_nonneg _ _ hc]
  refine ⟨?_, ?_⟩
  · rw [h_alg.1, h_smul_norm]
  · rw [h_alg.2.1, h_smul_norm]

end SpectralGapNormScaling

end InfoGeometry.Algebra.NoncommutativeNormedColimitCompletion
