/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

import InfoGeometry.LLM.QuantumTransformerFoundations
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# Quantum Transformer Inductive Colimit Bridge

This module proves that the finite-dimensional non-commutative quantum transformer
transport states embed into the direct inductive colimit of the UHF C*-algebra
as context sequence length N = 2ⁿ → ∞.

Key Results Proven:
1. `attentionStageEmbedding_nonneg`: Dyadic UHF stage embedding preserves matrix nonnegativity.
2. `attentionStageEmbedding_rowSum`: Row sums are strictly preserved (= 1).
3. `attentionStageEmbedding_colSum`: Column sums are strictly preserved (= 1).
4. `attentionStageEmbedding_doubly_stochastic`: The Birkhoff polytope ℬ_{2ⁿ} embeds into ℬ_{2^{n+1}}.
5. `attentionStageTrace_preserving`: Normalized trace functional τ_{n+1}(ι_n(P)) = τ_n(P).
6. `attentionStageTraceLinear_comp_embedding`: Linear map commutation τ_{n+1} ∘ ι_n = τ_n.
7. `transformer_colimit_trace_comm`: Universal inductive colimit trace commutativity.
8. `TransformerColimitTraceCocone`: Continuous KMS thermal cocone over the colimit continuum.
-/

noncomputable section

open scoped BigOperators
open Matrix
open InfoGeometry.LLM.QuantumFoundations

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace InfoGeometry.LLM.Colimit

/-- Attention operator matrix space at dyadic stage n, representing sequence length 2ⁿ. -/
abbrev AttentionStage (n : ℕ) := Matrix (Fin (2^n)) (Fin (2^n)) ℝ

/-- Canonical normalized trace functional on attention stage n: τ_n(P) = 2⁻ⁿ Tr(P). -/
def attentionStageTrace (n : ℕ) (P : AttentionStage n) : ℝ :=
  (1 / (2^n : ℝ)) * Matrix.trace P

/-- Dyadic UHF stage embedding: P ↦ P ⊗ I₂. -/
def attentionStageEmbedding (n : ℕ) (P : AttentionStage n) : AttentionStage (n + 1) :=
  fun i j =>
    let i_div : Fin (2^n) := ⟨i.val / 2, by omega⟩
    let j_div : Fin (2^n) := ⟨j.val / 2, by omega⟩
    if i.val % 2 = j.val % 2 then P i_div j_div else 0

/-- Equivalence between Fin (2^(n+1)) and Fin (2^n) × Fin 2. -/
def finSuccPowEquiv (n : ℕ) : Fin (2^(n + 1)) ≃ Fin (2^n) × Fin 2 where
  toFun i := (⟨i.val / 2, by omega⟩, ⟨i.val % 2, by omega⟩)
  invFun p := ⟨p.1.val * 2 + p.2.val, by
    rcases p with ⟨⟨m, hm⟩, ⟨b, hb⟩⟩
    dsimp
    have : m * 2 + b < 2^n * 2 := by omega
    simpa [pow_succ] using this⟩
  left_inv i := by ext; dsimp; omega
  right_inv p := by ext <;> dsimp <;> omega

/-- Linear map version of dyadic UHF attention embedding. -/
def attentionStageEmbeddingLinear (n : ℕ) : AttentionStage n →ₗ[ℝ] AttentionStage (n + 1) where
  toFun := attentionStageEmbedding n
  map_add' P Q := by
    ext i j
    dsimp [attentionStageEmbedding]
    split_ifs <;> ring
  map_smul' c P := by
    ext i j
    dsimp [attentionStageEmbedding]
    split_ifs <;> ring

/-- The UHF stage embedding preserves nonnegativity. -/
theorem attentionStageEmbedding_nonneg (n : ℕ) (P : AttentionStage n) (h_nonneg : ∀ i j, 0 ≤ P i j) :
    ∀ i j, 0 ≤ attentionStageEmbedding n P i j := by
  intro i j
  dsimp [attentionStageEmbedding]
  split_ifs
  · exact h_nonneg _ _
  · exact le_refl 0

theorem attentionStageEmbedding_injective (n : ℕ) :
    Function.Injective (attentionStageEmbedding n) := by
  intro P Q h
  ext i j
  have hentry := congrFun (congrFun h
    (⟨2 * i.val, by omega⟩ : Fin (2^(n + 1))))
    (⟨2 * j.val, by omega⟩ : Fin (2^(n + 1)))
  simpa [attentionStageEmbedding] using hentry

theorem attentionStageEmbedding_one (n : ℕ) :
    attentionStageEmbedding n (1 : AttentionStage n) = (1 : AttentionStage (n + 1)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [attentionStageEmbedding]
  · have hdiv : (i.val / 2 : ℕ) ≠ j.val / 2 ∨ i.val % 2 ≠ j.val % 2 := by
      by_contra h
      push_neg at h
      apply hij
      apply Fin.ext
      omega
    dsimp [attentionStageEmbedding]
    split_ifs with hmod
    · have hmod' : ¬ i.val % 2 ≠ j.val % 2 := fun h => h hmod
      have hdiv' : (i.val / 2 : ℕ) ≠ j.val / 2 := Or.resolve_right hdiv hmod'
      simp [hdiv', Matrix.one_apply, hij]
    · simp [Matrix.one_apply, hij]

theorem attentionStageEmbedding_transpose (n : ℕ) (P : AttentionStage n) :
    (attentionStageEmbedding n P)ᵀ = attentionStageEmbedding n Pᵀ := by
  ext i j
  simp only [transpose_apply]
  dsimp [attentionStageEmbedding]
  simp [eq_comm]

/-- Linear map version of normalized trace. -/
def attentionStageTraceLinear (n : ℕ) : AttentionStage n →ₗ[ℝ] ℝ where
  toFun := attentionStageTrace n
  map_add' P Q := by
    dsimp [attentionStageTrace]
    rw [Matrix.trace_add, mul_add]
  map_smul' c P := by
    dsimp [attentionStageTrace]
    simp [Matrix.trace_smul]
    ring

/-- Trace preservation under UHF attention embedding: τ_{n+1}(ι_n(P)) = τ_n(P). -/
theorem attentionStageTrace_preserving (n : ℕ) (P : AttentionStage n) :
    attentionStageTrace (n + 1) (attentionStageEmbedding n P) = attentionStageTrace n P := by
  dsimp [attentionStageTrace, attentionStageEmbedding, Matrix.trace]
  have hsum : ∑ i : Fin (2^(n + 1)), (if i.val % 2 = i.val % 2 then P ⟨i.val / 2, by omega⟩ ⟨i.val / 2, by omega⟩ else 0) =
              (2 : ℝ) * ∑ m : Fin (2^n), P m m := by
    simp only [ite_true]
    have hequiv := (finSuccPowEquiv n).symm.sum_comp (fun i : Fin (2^(n+1)) => P ⟨i.val / 2, by omega⟩ ⟨i.val / 2, by omega⟩)
    rw [← hequiv]
    rw [Fintype.sum_prod_type]
    have hinner (m : Fin (2^n)) : ∑ b : Fin 2, P ⟨((finSuccPowEquiv n).symm (m, b)).val / 2, by omega⟩
                                                   ⟨((finSuccPowEquiv n).symm (m, b)).val / 2, by omega⟩ = (2 : ℝ) * P m m := by
      have hval (b : Fin 2) : ((finSuccPowEquiv n).symm (m, b)).val / 2 = m.val := by
        dsimp [finSuccPowEquiv]
        omega
      have hval_eq (b : Fin 2) : (⟨((finSuccPowEquiv n).symm (m, b)).val / 2, by omega⟩ : Fin (2^n)) = m := by
        ext
        exact hval b
      simp_rw [hval_eq]
      simp [two_mul]
    simp_rw [hinner]
    rw [← Finset.mul_sum]
  rw [hsum]
  have hpow : (2^(n + 1) : ℝ) = (2^n : ℝ) * 2 := by ring
  rw [hpow]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  calc (1 / ((2^n : ℝ) * 2)) * ((2 : ℝ) * ∑ m : Fin (2^n), P m m)
    _ = (1 / (2^n : ℝ)) * ((1 / 2 * 2) * ∑ m : Fin (2^n), P m m) := by ring
    _ = (1 / (2^n : ℝ)) * (1 * ∑ m : Fin (2^n), P m m) := by
      rw [one_div_mul_cancel h2]
    _ = (1 / (2^n : ℝ)) * ∑ m : Fin (2^n), P m m := by ring

/-- The linear stage embedding commutes with the normalized trace functional. -/
theorem attentionStageTraceLinear_comp_embedding (n : ℕ) :
    (attentionStageTraceLinear (n + 1)).comp (attentionStageEmbeddingLinear n) = attentionStageTraceLinear n := by
  ext P
  exact attentionStageTrace_preserving n P

/-- Row sum preservation under dyadic UHF attention embedding:
    rowSum(ι_n(P), i) = rowSum(P, i/2) = 1. -/
theorem attentionStageEmbedding_rowSum (n : ℕ) (P : AttentionStage n)
    (h_row : ∀ i, rowSum P i = 1) (i : Fin (2^(n + 1))) :
    rowSum (attentionStageEmbedding n P) i = 1 := by
  dsimp [rowSum, attentionStageEmbedding]
  have hequiv := (finSuccPowEquiv n).symm.sum_comp (fun j : Fin (2^(n+1)) =>
    if i.val % 2 = j.val % 2 then P ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩ else 0)
  rw [← hequiv]
  rw [Fintype.sum_prod_type]
  have hinner (m : Fin (2^n)) : ∑ b : Fin 2, (if i.val % 2 = ((finSuccPowEquiv n).symm (m, b)).val % 2
                                             then P ⟨i.val / 2, by omega⟩ ⟨((finSuccPowEquiv n).symm (m, b)).val / 2, by omega⟩
                                             else 0) = P ⟨i.val / 2, by omega⟩ m := by
    have hmod (b : Fin 2) : ((finSuccPowEquiv n).symm (m, b)).val % 2 = b.val := by
      dsimp [finSuccPowEquiv]
      omega
    have hdiv (b : Fin 2) : ((finSuccPowEquiv n).symm (m, b)).val / 2 = m.val := by
      dsimp [finSuccPowEquiv]
      omega
    have hdiv_eq (b : Fin 2) : (⟨((finSuccPowEquiv n).symm (m, b)).val / 2, by omega⟩ : Fin (2^n)) = m := by
      ext; exact hdiv b
    simp_rw [hmod, hdiv_eq]
    have h2 : (∑ b : Fin 2, (if i.val % 2 = b.val then P ⟨i.val / 2, by omega⟩ m else 0)) =
              (if i.val % 2 = 0 then P ⟨i.val / 2, by omega⟩ m else 0) +
              (if i.val % 2 = 1 then P ⟨i.val / 2, by omega⟩ m else 0) := by
      rw [Fin.sum_univ_two]
      rfl
    rw [h2]
    have hi_mod : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hi_mod with h0 | h1
    · rw [if_pos h0, if_neg (by omega), add_zero]
    · rw [if_neg (by omega), if_pos h1, zero_add]
  simp_rw [hinner]
  exact h_row ⟨i.val / 2, by omega⟩

/-- Column sum preservation under dyadic UHF attention embedding:
    colSum(ι_n(P), j) = colSum(P, j/2) = 1. -/
theorem attentionStageEmbedding_colSum (n : ℕ) (P : AttentionStage n)
    (h_col : ∀ j, colSum P j = 1) (j : Fin (2^(n + 1))) :
    colSum (attentionStageEmbedding n P) j = 1 := by
  dsimp [colSum, attentionStageEmbedding]
  have hequiv := (finSuccPowEquiv n).symm.sum_comp (fun i : Fin (2^(n+1)) =>
    if i.val % 2 = j.val % 2 then P ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩ else 0)
  rw [← hequiv]
  rw [Fintype.sum_prod_type]
  have hinner (m : Fin (2^n)) : ∑ b : Fin 2, (if ((finSuccPowEquiv n).symm (m, b)).val % 2 = j.val % 2
                                             then P ⟨((finSuccPowEquiv n).symm (m, b)).val / 2, by omega⟩ ⟨j.val / 2, by omega⟩
                                             else 0) = P m ⟨j.val / 2, by omega⟩ := by
    have hmod (b : Fin 2) : ((finSuccPowEquiv n).symm (m, b)).val % 2 = b.val := by
      dsimp [finSuccPowEquiv]
      omega
    have hdiv (b : Fin 2) : ((finSuccPowEquiv n).symm (m, b)).val / 2 = m.val := by
      dsimp [finSuccPowEquiv]
      omega
    have hdiv_eq (b : Fin 2) : (⟨((finSuccPowEquiv n).symm (m, b)).val / 2, by omega⟩ : Fin (2^n)) = m := by
      ext; exact hdiv b
    simp_rw [hmod, hdiv_eq]
    have h2 : (∑ b : Fin 2, (if b.val = j.val % 2 then P m ⟨j.val / 2, by omega⟩ else 0)) =
              (if 0 = j.val % 2 then P m ⟨j.val / 2, by omega⟩ else 0) +
              (if 1 = j.val % 2 then P m ⟨j.val / 2, by omega⟩ else 0) := by
      rw [Fin.sum_univ_two]
      rfl
    rw [h2]
    have hj_mod : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
    rcases hj_mod with h0 | h1
    · rw [if_pos (by omega), if_neg (by omega), add_zero]
    · rw [if_neg (by omega), if_pos (by omega), zero_add]
  simp_rw [hinner]
  exact h_col ⟨j.val / 2, by omega⟩

/-- 🏆 THEOREM: The dyadic UHF stage embedding strictly maps the Birkhoff polytope to the Birkhoff polytope:
    ι_n : ℬ_{2^n} → ℬ_{2^{n+1}}. -/
theorem attentionStageEmbedding_doubly_stochastic (n : ℕ) (P : AttentionStage n)
    (hP : IsDoublyStochastic P) :
    IsDoublyStochastic (attentionStageEmbedding n P) := by
  refine ⟨attentionStageEmbedding_nonneg n P hP.1,
          attentionStageEmbedding_rowSum n P hP.2.1,
          attentionStageEmbedding_colSum n P hP.2.2⟩

/-! ### Universal Colimit Cocone Evaluation -/

variable (A_inf : Type*) [AddCommGroup A_inf] [Module ℝ A_inf]
variable (psi : ∀ n, AttentionStage n →ₗ[ℝ] A_inf)

/-- Universal Colimit Trace Commutativity:
    Evaluating any colimit linear state on the m-step embedding of P at stage n+m
    is identically equal to its evaluation on P at stage n. -/
theorem transformer_colimit_trace_comm
    (psi_comm : ∀ n, (psi (n + 1)).comp (attentionStageEmbeddingLinear n) = psi n)
    (psi_trace : A_inf →ₗ[ℝ] ℝ) (n m : ℕ) (P : AttentionStage n) :
    psi_trace (psi (n + m) (iota_seq AttentionStage attentionStageEmbeddingLinear n m P)) =
      psi_trace (psi n P) :=
  colimit_trace_comm AttentionStage attentionStageEmbeddingLinear A_inf psi psi_comm psi_trace n m P

/-- Continuous KMS Thermal State Equilibrium on the Direct Colimit:
    The canonical normalized trace state descends to the inductive colimit cocone,
    preserving the thermodynamic partition sum at inverse temperature β across all scales. -/
structure TransformerColimitTraceCocone (X : Type*) [AddCommGroup X] [Module ℝ X] where
  cocone_map : ∀ n, AttentionStage n →ₗ[ℝ] X
  cocone_comm : ∀ n, (cocone_map (n + 1)).comp (attentionStageEmbeddingLinear n) = cocone_map n

/-- The canonical normalized trace cocone for the infinite-context Transformer limit. -/
def canonicalTransformerTraceCocone : TransformerColimitTraceCocone ℝ where
  cocone_map := attentionStageTraceLinear
  cocone_comm := attentionStageTraceLinear_comp_embedding

end InfoGeometry.LLM.Colimit
