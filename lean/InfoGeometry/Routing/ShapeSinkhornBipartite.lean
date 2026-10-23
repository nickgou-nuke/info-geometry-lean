/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.BipartiteLogCoupling
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Shape–Sinkhorn–detector factorization and bipartite reduction

The five factors are supplied. No claim of low-rank NMF existence, uniqueness,
or finite-iteration Sinkhorn convergence is made. Native `doublyStochastic`
and `Equiv.Perm.permMatrix` are reused. The final solver identity records its
solved-system hypotheses rather than assuming that a rank-one stationary
projector works for every doubly stochastic matrix.
-/
noncomputable section
namespace InfoGeometry.Routing.ShapeSinkhornBipartite
open scoped BigOperators
open InfoGeometry.Probability.BipartiteLogCoupling
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K]

def gainCore (a : K → ℝ) (B : Matrix K K ℝ) (b : K → ℝ) : Matrix K K ℝ :=
  Matrix.diagonal a * B * Matrix.diagonal b

def coincidence (U : Matrix I K ℝ) (a : K → ℝ) (B : Matrix K K ℝ)
    (b : K → ℝ) (V : Matrix J K ℝ) : Matrix I J ℝ :=
  U * gainCore a B b * V.transpose

theorem gain_absorption (U : Matrix I K ℝ) (a : K → ℝ) (B : Matrix K K ℝ)
    (b : K → ℝ) (V : Matrix J K ℝ) :
    coincidence U a B b V =
      (U * Matrix.diagonal a) * B * (V * Matrix.diagonal b).transpose := by
  simp [coincidence, gainCore, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Native Birkhoff existence, not a supplied mixture witness. -/
theorem exists_matching_expansion (U : Matrix I K ℝ) (a : K → ℝ)
    (B : Matrix K K ℝ) (b : K → ℝ) (V : Matrix J K ℝ)
    (hB : B ∈ doublyStochastic ℝ K) :
    ∃ w : Equiv.Perm K → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      coincidence U a B b V =
        ∑ σ, w σ • ((U * Matrix.diagonal a) * σ.permMatrix ℝ *
          (V * Matrix.diagonal b).transpose) := by
  obtain ⟨w, hw, hm, he⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hB
  refine ⟨w, hw, hm, ?_⟩
  rw [gain_absorption, ← he, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem total_coincidence_mass (U : Matrix I K ℝ) (a : K → ℝ)
    (B : Matrix K K ℝ) (b : K → ℝ) (V : Matrix J K ℝ)
    (hU : ∀ k, ∑ i, U i k = 1) (hV : ∀ k, ∑ j, V j k = 1) :
    (∑ i, ∑ j, coincidence U a B b V i j) = ∑ k, ∑ l, a k * B k l * b l := by
  rw [coincidence, triFactor_total_mass U (gainCore a B b) V hU hV]
  simp [gainCore, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Log reconstruction is independent of whether the iterations have converged. -/
theorem log_gain_reconstruction (s : Matrix K K ℝ) (u v : K → ℝ) (c : ℝ)
    (i j : K) :
    Real.exp (-u i + c) * Real.exp (s i j + u i + v j) * Real.exp (-v j - c) =
      Real.exp (s i j) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Gauge choice balances log gain sums. -/
theorem balanced_log_gauge [Nonempty K] (u v : K → ℝ) :
    let c := ((∑ i, u i) - ∑ i, v i) / (2 * (Fintype.card K : ℝ))
    (∑ i, (-u i + c)) = ∑ i, (-v i - c) := by
  have hn : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  dsimp only
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hn]
  <;> ring

def bipartite (B : Matrix K K ℝ) : Matrix (K ⊕ K) (K ⊕ K) ℝ :=
  Matrix.fromBlocks 0 B B.transpose 0

def laplacian (B : Matrix K K ℝ) : Matrix (K ⊕ K) (K ⊕ K) ℝ := 1 - bipartite B

theorem bipartite_symmetric (B : Matrix K K ℝ) :
    (bipartite B).transpose = bipartite B := by
  simp [bipartite, Matrix.fromBlocks_transpose]

theorem laplacian_symmetric (B : Matrix K K ℝ) :
    (laplacian B).transpose = laplacian B := by
  simp [laplacian, Matrix.transpose_sub, bipartite_symmetric]

theorem bipartite_square (B : Matrix K K ℝ) :
    bipartite B * bipartite B =
      Matrix.fromBlocks (B * B.transpose) 0 0 (B.transpose * B) := by
  ext i j
  cases i <;> cases j <;>
    simp [bipartite, Matrix.mul_apply]

theorem bipartite_doublyStochastic (B : Matrix K K ℝ)
    (hB : B ∈ doublyStochastic ℝ K) :
    bipartite B ∈ doublyStochastic ℝ (K ⊕ K) := by
  rw [mem_doublyStochastic_iff_sum] at hB ⊢
  have hr : ∀ i, ∑ j, bipartite B i j = 1 := by
    intro i
    cases i <;> simp [bipartite, Fintype.sum_sum_type, hB.2.1, hB.2.2]
  refine ⟨?_, hr, ?_⟩
  · intro i j
    cases i <;> cases j <;> simp [bipartite, hB.1]
  · intro j
    calc (∑ i, bipartite B i j) = ∑ i, (bipartite B).transpose j i := rfl
      _ = 1 := by rw [bipartite_symmetric]; exact hr j

theorem gramian_doublyStochastic (B : Matrix K K ℝ)
    (hB : B ∈ doublyStochastic ℝ K) :
    B * B.transpose ∈ doublyStochastic ℝ K ∧
      B.transpose * B ∈ doublyStochastic ℝ K := by
  have ht := transpose_mem_doublyStochastic_iff.mpr hB
  exact ⟨(doublyStochastic ℝ K).mul_mem hB ht,
    (doublyStochastic ℝ K).mul_mem ht hB⟩

/-- The eigenvalue -1 parity mode prevents ordinary bipartite power convergence. -/
theorem parity_eigenvector (B : Matrix K K ℝ)
    (hB : B ∈ doublyStochastic ℝ K) :
    (bipartite B).mulVec (Sum.elim (fun _ => (1 : ℝ)) (fun _ => -1)) =
      -(Sum.elim (fun _ => (1 : ℝ)) (fun _ => -1)) := by
  obtain ⟨_, hr, hc⟩ := mem_doublyStochastic_iff_sum.mp hB
  funext i
  cases i <;>
    simp [bipartite, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Finset.sum_neg_distrib, hr, hc]

/-- Algebraic factorization underlying the reduced solve. -/
theorem laplacian_factorization (B : Matrix K K ℝ) :
    laplacian B * (1 + bipartite B) =
      1 - Matrix.fromBlocks (B * B.transpose) 0 0 (B.transpose * B) := by
  rw [← bipartite_square]
  unfold laplacian
  noncomm_ring

/-- Reduced equations plus the parity correction imply the full block equations.
The means ms,md are supplied; the runtime computes them from its input signals.
No invertibility or connectedness conclusion is hidden in this identity. -/
theorem reduced_poisson_contract (B : Matrix K K ℝ)
    (hB : B ∈ doublyStochastic ℝ K)
    (zS zD bS bD : K → ℝ) (ms md : ℝ)
    (hS : zS - B.mulVec (B.transpose.mulVec zS) = bS - fun _ => ms)
    (hD : zD - B.transpose.mulVec (B.mulVec zD) = bD - fun _ => md) :
    let delta := (ms - md) / 2
    let xS := zS + B.mulVec zD + fun _ => delta / 2
    let xD := B.transpose.mulVec zS + zD - fun _ => delta / 2
    xS - B.mulVec xD = bS - (fun _ => (ms + md) / 2) ∧
    xD - B.transpose.mulVec xS = bD - (fun _ => (ms + md) / 2) := by
  have hc (c : ℝ) : B.mulVec (fun _ => c) = fun _ => c := by
    funext i
    simp [Matrix.mulVec, dotProduct, ← Finset.sum_mul,
      sum_row_of_mem_doublyStochastic hB]
  have htc (c : ℝ) : B.transpose.mulVec (fun _ => c) = fun _ => c := by
    funext i
    simp [Matrix.mulVec, dotProduct, ← Finset.sum_mul,
      sum_col_of_mem_doublyStochastic hB]
  dsimp only
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, hc, htc]
  constructor
  · funext i
    have h := congrFun hS i
    simp only [Pi.sub_apply] at h
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith
  · funext i
    have h := congrFun hD i
    simp only [Pi.sub_apply] at h
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith

end InfoGeometry.Routing.ShapeSinkhornBipartite
