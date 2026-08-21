import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Complete Positivity (CP) and the Choi–Jamiołkowski Isomorphism

This module formalizes:
1. Standard matrix units `E_{xy} = |x⟩⟨y|`.
2. The Choi Matrix of a linear superoperator `ℰ : Mat →ₗ[ℂ] Mat`:
     (Λ_ℰ)_{(i, x), (j, y)} = (ℰ(E_{xy}))_{i, j}
3. The Kraus representation of quantum operations:
     ℰ_K(ρ) = ∑_k K_k * ρ * K_k†
4. THEOREM (Choi Positive Semi-Definiteness):
     For any Kraus channel ℰ_K and any state vector v:
       ⟪v, Λ_{ℰ_K} v⟫ = ∑_k |∑_{i, x} v(i, x)* (K_k)_{i, x}|² ≥ 0
5. Partial trace preservation condition: Tr₁(Λ_ℰ) = I.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open Matrix
open BigOperators
open Finset

namespace InfoGeometry.Modular.Choi

lemma matrix_sum_apply {α : Type*} {m n : Type*} (s : Finset α) (f : α → Matrix m n ℂ) (i : m) (j : n) :
    (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j := by
  have h1 : (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i := Finset.sum_apply i s f
  rw [h1]
  exact Finset.sum_apply j s (fun k => f k i)

lemma finset_sum_ofReal_re {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    (∑ x ∈ s, (f x : ℂ)).re = ∑ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha ih =>
    rw [Finset.sum_insert ha, Complex.add_re, ih, Finset.sum_insert ha, Complex.ofReal_re]

variable {ι : Type*} [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

local notation "Mat" => Matrix ι ι ℂ
local notation "ChoiMat" => Matrix (ι × ι) (ι × ι) ℂ

/-!
=============================================================================
PART 1: Standard Matrix Units and the Choi Matrix
=============================================================================
-/

/-- Standard Matrix Unit E_{xy} = |x⟩⟨y|: 1 at entry (x, y) and 0 elsewhere. -/
def stdBasis (x y : ι) : Mat :=
  fun i j => if i = x ∧ j = y then 1 else 0

@[simp]
theorem stdBasis_apply (x y i j : ι) :
    stdBasis x y i j = if i = x ∧ j = y then 1 else 0 := rfl

/-- 
  The Choi Matrix of a linear superoperator ℰ:
  (Λ_ℰ)_{(i, x), (j, y)} = (ℰ(E_{xy}))_{i, j}
-/
def choiMatrix (E : Mat →ₗ[ℂ] Mat) : ChoiMat :=
  fun ⟨i, x⟩ ⟨j, y⟩ => E (stdBasis x y) i j

@[simp]
theorem choiMatrix_apply (E : Mat →ₗ[ℂ] Mat) (i x j y : ι) :
    choiMatrix E (i, x) (j, y) = E (stdBasis x y) i j := rfl

/-!
=============================================================================
PART 2: Kraus Channels and their Explicit Choi Representation
=============================================================================
-/

variable [Fintype ι]

/-- Single Kraus jump channel term: K_k * ρ * K_k†. -/
def krausTerm (K_k : Mat) (ρ : Mat) : Mat :=
  K_k * ρ * star K_k

/-- Multichannel Kraus Quantum Channel: ℰ_K(ρ) = ∑_k K_k * ρ * K_k†. -/
def krausChannel (K : κ → Mat) : Mat →ₗ[ℂ] Mat where
  toFun ρ := ∑ k, krausTerm (K k) ρ
  map_add' A B := by
    dsimp [krausTerm]
    simp only [mul_add, add_mul]
    rw [← Finset.sum_add_distrib]
  map_smul' c A := by
    dsimp [krausTerm]
    simp only [mul_smul_comm, smul_mul_assoc]
    rw [Finset.smul_sum]

/-- 
  LEMMA 1: Evaluation of a Single Kraus Channel on the Matrix Basis:
  (K * E_{xy} * K†)_{i, j} = K_{i, x} * (K_{j, y})*
-/
theorem kraus_on_basis_apply (K_op : Mat) (x y i j : ι) :
    (krausTerm K_op (stdBasis x y)) i j = K_op i x * starRingEnd ℂ (K_op j y) := by
  dsimp [krausTerm, Matrix.mul_apply, Matrix.star_apply, stdBasis]
  have h_first (m : ι) : (∑ p, K_op i p * if p = x ∧ m = y then (1 : ℂ) else 0) =
      if m = y then K_op i x else 0 := by
    rw [Finset.sum_eq_single x]
    · by_cases hm : m = y
      · simp [hm]
      · simp [hm]
    · intro p _ hp
      have : (p = x ∧ m = y) = False := by simp [hp]
      simp [this]
    · intro h_not; exfalso; exact h_not (Finset.mem_univ x)
  calc
    (∑ m, (∑ p, K_op i p * if p = x ∧ m = y then (1 : ℂ) else 0) * starRingEnd ℂ (K_op j m))
      = ∑ m, (if m = y then K_op i x else 0) * starRingEnd ℂ (K_op j m) := by
        apply Finset.sum_congr rfl; intro m _; rw [h_first m]
    _ = K_op i x * starRingEnd ℂ (K_op j y) := by
        rw [Finset.sum_eq_single y]
        · simp
        · intro m _ hm; simp [hm]
        · intro h_not; exfalso; exact h_not (Finset.mem_univ y)

/-!
=============================================================================
PART 3: Proof of Choi Positive Semi-Definiteness (Complete Positivity)
=============================================================================
-/

/-- The Quadratic Form / Expectation of the Choi Matrix on a bipartite vector v: ι × ι → ℂ. -/
def choiQuadraticForm (M : ChoiMat) (v : ι × ι → ℂ) : ℂ :=
  ∑ a, ∑ b, starRingEnd ℂ (v a) * M a b * v b

/-- 
  MASTER THEOREM (Choi Complete Positivity Theorem):
  For ANY Kraus channel ℰ_K = ∑_k K_k • K_k†, the Choi matrix is strictly
  POSITIVE SEMI-DEFINITE:
    ⟪v, Λ_{ℰ_K} v⟫ = ∑_k |∑_{i, x} v(i, x)* K_{i, x}|² ≥ 0
-/
theorem choi_matrix_positive_semidefinite (K : κ → Mat) (v : ι × ι → ℂ) :
    0 ≤ (choiQuadraticForm (choiMatrix (krausChannel K)) v).re := by
  dsimp [choiQuadraticForm, choiMatrix, krausChannel]
  have h_basis (a b : ι × ι) :
      (∑ k, krausTerm (K k) (stdBasis a.2 b.2)) a.1 b.1 =
      ∑ k, K k a.1 a.2 * starRingEnd ℂ (K k b.1 b.2) := by
    rw [matrix_sum_apply]
    apply Finset.sum_congr rfl; intro k _
    exact kraus_on_basis_apply (K k) a.2 b.2 a.1 b.1
  simp_rw [h_basis, Finset.mul_sum, Finset.sum_mul]
  have h_prod (k : κ) :
      (∑ a : ι × ι, ∑ b : ι × ι, starRingEnd ℂ (v a) * (K k a.1 a.2 * starRingEnd ℂ (K k b.1 b.2)) * v b) =
      (∑ a : ι × ι, starRingEnd ℂ (v a) * K k a.1 a.2) * (∑ b : ι × ι, starRingEnd ℂ (K k b.1 b.2) * v b) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    ring
  have h_swap :
      (∑ a : ι × ι, ∑ b : ι × ι, ∑ k : κ, starRingEnd ℂ (v a) * (K k a.1 a.2 * starRingEnd ℂ (K k b.1 b.2)) * v b) =
      ∑ k : κ, (∑ a : ι × ι, starRingEnd ℂ (v a) * K k a.1 a.2) * (∑ b : ι × ι, starRingEnd ℂ (K k b.1 b.2) * v b) := by
    calc
      (∑ a, ∑ b, ∑ k, starRingEnd ℂ (v a) * (K k a.1 a.2 * starRingEnd ℂ (K k b.1 b.2)) * v b)
        = ∑ a, ∑ k, ∑ b, starRingEnd ℂ (v a) * (K k a.1 a.2 * starRingEnd ℂ (K k b.1 b.2)) * v b := by
          apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, starRingEnd ℂ (v a) * (K k a.1 a.2 * starRingEnd ℂ (K k b.1 b.2)) * v b := Finset.sum_comm
      _ = ∑ k, (∑ a, starRingEnd ℂ (v a) * K k a.1 a.2) * (∑ b, starRingEnd ℂ (K k b.1 b.2) * v b) := by
          apply Finset.sum_congr rfl; intro k _
          exact h_prod k
  rw [h_swap]
  have h_conj_factor (k : κ) :
      (∑ b : ι × ι, starRingEnd ℂ (K k b.1 b.2) * v b) =
      starRingEnd ℂ (∑ a : ι × ι, starRingEnd ℂ (v a) * (K k a.1 a.2)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl; intro a _
    simp only [map_mul, starRingEnd_apply, star_star]
    ring
  have h_normSq_sum :
      (∑ k, (∑ a : ι × ι, starRingEnd ℂ (v a) * (K k a.1 a.2)) *
            (∑ b : ι × ι, starRingEnd ℂ (K k b.1 b.2) * v b)) =
      ∑ k, (Complex.normSq (∑ a : ι × ι, starRingEnd ℂ (v a) * (K k a.1 a.2)) : ℂ) := by
    apply Finset.sum_congr rfl; intro k _
    rw [h_conj_factor k]
    exact Complex.mul_conj (∑ a : ι × ι, starRingEnd ℂ (v a) * K k a.1 a.2)
  rw [h_normSq_sum]
  rw [finset_sum_ofReal_re]
  apply Finset.sum_nonneg
  intro k _
  exact Complex.normSq_nonneg _

/-!
=============================================================================
PART 4: Trace Preservation via Partial Trace on the Choi Matrix
=============================================================================
-/

/-- Partial Trace over the output space (first index): Tr₁(M)_{x, y} = ∑_i M_{(i, x), (i, y)}. -/
def partialTraceFirst (M : ChoiMat) : Mat :=
  fun x y => ∑ i, M (i, x) (i, y)

/-- 
  THEOREM (Choi Matrix Trace Preservation Characterization):
  A linear channel ℰ is Trace-Preserving on all matrix units if and only if
  the partial trace of its Choi matrix is the Identity Matrix:
    Tr₁(Λ_ℰ) = I
-/
theorem choi_trace_preserving_iff (E : Mat →ₗ[ℂ] Mat) :
    partialTraceFirst (choiMatrix E) = 1 ↔ (∀ x y, Matrix.trace (E (stdBasis x y)) = if x = y then 1 else 0) := by
  constructor
  · intro h x y
    have h_entry := congr_fun (congr_fun h x) y
    dsimp [partialTraceFirst, choiMatrix, Matrix.trace] at h_entry ⊢
    rw [h_entry, Matrix.one_apply]
  · intro h
    ext x y
    dsimp [partialTraceFirst, choiMatrix]
    have h_tr := h x y
    dsimp [Matrix.trace] at h_tr
    rw [h_tr, Matrix.one_apply]

end InfoGeometry.Modular.Choi

end noncomputable section
