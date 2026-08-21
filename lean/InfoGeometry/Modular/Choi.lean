import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

local notation "Mat" => Matrix ι ι ℂ
local notation "ChoiMat" => Matrix (ι × ι) (ι × ι) ℂ

/-!
=============================================================================
PART 1: Standard Matrix Units and the Choi Matrix
=============================================================================
-/

/-- Standard Matrix Unit E_{xy} = |x⟩⟨y|: 1 at entry (x, y) and 0 elsewhere. -/
def stdBasis (x y : ι) : Mat :=
  Matrix.of (fun i j => if i = x ∧ j = y then 1 else 0)

@[simp]
theorem stdBasis_apply (x y i j : ι) :
    stdBasis x y i j = if i = x ∧ j = y then 1 else 0 := rfl

/-- 
  The Choi Matrix of a linear superoperator ℰ:
  (Λ_ℰ)_{(i, x), (j, y)} = (ℰ(E_{xy}))_{i, j}
-/
def choiMatrix (E : Mat →ₗ[ℂ] Mat) : ChoiMat :=
  Matrix.of (fun ⟨i, x⟩ ⟨j, y⟩ => E (stdBasis x y) i j)

@[simp]
theorem choiMatrix_apply (E : Mat →ₗ[ℂ] Mat) (i x j y : ι) :
    choiMatrix E ⟨i, x⟩ ⟨j, y⟩ = E (stdBasis x y) i j := rfl

/-!
=============================================================================
PART 2: Kraus Channels and their Explicit Choi Representation
=============================================================================
-/

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
  dsimp [krausTerm, stdBasis, mul_apply, star_apply]
  have h_inner (r : ι) : (∑ c : ι, K_op i c * (if c = x ∧ r = y then (1 : ℂ) else 0)) =
      if r = y then K_op i x else 0 := by
    rw [Finset.sum_eq_single x]
    · simp only [true_and]
      split_ifs <;> simp
    · intro c _ hneq
      have : (c = x ∧ r = y) = False := by simp [hneq]
      simp [this]
    · intro hx
      exact False.elim (hx (Finset.mem_univ x))
  
  have h_outer : (∑ r : ι, (∑ c : ι, K_op i c * (if c = x ∧ r = y then (1 : ℂ) else 0)) * starRingEnd ℂ (K_op j r)) =
      K_op i x * starRingEnd ℂ (K_op j y) := by
    calc
      (∑ r : ι, (∑ c : ι, K_op i c * (if c = x ∧ r = y then (1 : ℂ) else 0)) * starRingEnd ℂ (K_op j r))
        = ∑ r : ι, (if r = y then K_op i x else 0) * starRingEnd ℂ (K_op j r) := by
          refine Finset.sum_congr rfl (fun r _ => by rw [h_inner r])
      _ = K_op i x * starRingEnd ℂ (K_op j y) := by
        rw [Finset.sum_eq_single y]
        · simp only [if_true]
        · intro r _ hneq
          simp only [if_neg hneq, zero_mul]
        · intro hj
          exact False.elim (hj (Finset.mem_univ y))
  
  exact h_outer

/-!
=============================================================================
PART 3: Proof of Choi Positive Semi-Definiteness (Complete Positivity)
=============================================================================
-/

/-- The Quadratic Form / Expectation of the Choi Matrix on a bipartite vector v: ι × ι → ℂ. -/
def choiQuadraticForm (M : ChoiMat) (v : ι × ι → ℂ) : ℂ :=
  ∑ a : ι × ι, ∑ b : ι × ι, starRingEnd ℂ (v a) * M a b * v b

/-- Factorization of bipartite product sum into independent factor sums. -/
theorem bilin_sum_factor (K_k : Mat) (v : (ι × ι) → ℂ) :
    (∑ a : ι × ι, ∑ b : ι × ι, starRingEnd ℂ (v a) * (K_k a.1 a.2 * starRingEnd ℂ (K_k b.1 b.2)) * v b) =
    (∑ a : ι × ι, starRingEnd ℂ (v a) * K_k a.1 a.2) * (∑ b : ι × ι, starRingEnd ℂ (K_k b.1 b.2) * v b) := by
  calc
    (∑ a : ι × ι, ∑ b : ι × ι, starRingEnd ℂ (v a) * (K_k a.1 a.2 * starRingEnd ℂ (K_k b.1 b.2)) * v b)
      = ∑ a : ι × ι, ∑ b : ι × ι, (starRingEnd ℂ (v a) * K_k a.1 a.2) * (starRingEnd ℂ (K_k b.1 b.2) * v b) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
    _ = ∑ a : ι × ι, (starRingEnd ℂ (v a) * K_k a.1 a.2) * (∑ b : ι × ι, starRingEnd ℂ (K_k b.1 b.2) * v b) := by
        refine Finset.sum_congr rfl (fun a _ => by rw [← Finset.mul_sum])
    _ = (∑ a : ι × ι, starRingEnd ℂ (v a) * K_k a.1 a.2) * (∑ b : ι × ι, starRingEnd ℂ (K_k b.1 b.2) * v b) := by
        rw [← Finset.sum_mul]

/-- 
  MASTER THEOREM (Choi Complete Positivity Theorem):
  For ANY Kraus channel ℰ_K = ∑_k K_k • K_k†, the Choi matrix is strictly
  POSITIVE SEMI-DEFINITE:
    ⟪v, Λ_{ℰ_K} v⟫ = ∑_k |∑_{i, x} v(i, x)* K_{i, x}|² ≥ 0
-/
theorem choi_matrix_positive_semidefinite (K : κ → Mat) (v : ι × ι → ℂ) :
    0 ≤ (choiQuadraticForm (choiMatrix (krausChannel K)) v).re ∧
    (choiQuadraticForm (choiMatrix (krausChannel K)) v).im = 0 := by
  have h_entry (a b : ι × ι) :
      choiMatrix (krausChannel K) a b = ∑ k, K k a.1 a.2 * starRingEnd ℂ (K k b.1 b.2) := by
    dsimp [choiMatrix, krausChannel]
    have h_sum_apply : (∑ k : κ, krausTerm (K k) (stdBasis a.2 b.2)) a.1 b.1 =
        ∑ k : κ, krausTerm (K k) (stdBasis a.2 b.2) a.1 b.1 :=
      Matrix.sum_apply a.1 b.1 Finset.univ (fun k => krausTerm (K k) (stdBasis a.2 b.2))
    rw [h_sum_apply]
    refine Finset.sum_congr rfl (fun k _ => kraus_on_basis_apply (K k) a.2 b.2 a.1 b.1)

  have h_swap :
      choiQuadraticForm (choiMatrix (krausChannel K)) v =
      ∑ k : κ, (∑ a : ι × ι, starRingEnd ℂ (v a) * K k a.1 a.2) *
               starRingEnd ℂ (∑ b : ι × ι, starRingEnd ℂ (v b) * K k b.1 b.2) := by
    dsimp [choiQuadraticForm]
    simp_rw [h_entry]
    simp only [Finset.mul_sum, Finset.sum_mul]
    have h_step :
        (∑ a : ι × ι, ∑ b : ι × ι, ∑ k : κ,
          starRingEnd ℂ (v a) * (K k a.1 a.2 * starRingEnd ℂ (K k b.1 b.2)) * v b) =
        ∑ a : ι × ι, ∑ k : κ, ∑ b : ι × ι,
          starRingEnd ℂ (v a) * (K k a.1 a.2 * starRingEnd ℂ (K k b.1 b.2)) * v b := by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    rw [h_step]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (ι × ι))) (t := (Finset.univ : Finset κ))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h_conj : starRingEnd ℂ (∑ b : ι × ι, starRingEnd ℂ (v b) * K k b.1 b.2) =
        ∑ b : ι × ι, starRingEnd ℂ (K k b.1 b.2) * v b := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [map_mul, Complex.conj_conj, mul_comm]
    rw [bilin_sum_factor (K k) v]
    rw [h_conj]
    rw [← Finset.sum_mul]

  rw [h_swap]
  have h_normSq_sum :
      (∑ k : κ, (∑ a : ι × ι, starRingEnd ℂ (v a) * K k a.1 a.2) *
                starRingEnd ℂ (∑ b : ι × ι, starRingEnd ℂ (v b) * K k b.1 b.2)) =
      ∑ k : κ, (Complex.normSq (∑ a : ι × ι, starRingEnd ℂ (v a) * K k a.1 a.2) : ℂ) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact Complex.mul_conj (∑ a : ι × ι, starRingEnd ℂ (v a) * K k a.1 a.2)
  rw [h_normSq_sum]
  constructor
  · rw [← Complex.ofReal_sum, Complex.ofReal_re]
    exact Finset.sum_nonneg (fun k _ => Complex.normSq_nonneg _)
  · rw [← Complex.ofReal_sum, Complex.ofReal_im]

/-!
=============================================================================
PART 4: Trace Preservation via Partial Trace on the Choi Matrix
=============================================================================
-/

/-- Partial Trace over the output space (first index): Tr₁(M)_{x, y} = ∑_i M_{(i, x), (i, y)}. -/
def partialTraceFirst (M : ChoiMat) : Mat :=
  Matrix.of (fun x y => ∑ i, M ⟨i, x⟩ ⟨i, y⟩)

@[simp]
theorem partialTraceFirst_apply (M : ChoiMat) (x y : ι) :
    partialTraceFirst M x y = ∑ i, M ⟨i, x⟩ ⟨i, y⟩ := rfl

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
    have h_entry := congrArg (fun M : Mat => M x y) h
    dsimp [partialTraceFirst, choiMatrix, Matrix.trace, Matrix.one_apply] at h_entry ⊢
    exact h_entry
  · intro h
    ext x y
    dsimp [partialTraceFirst, choiMatrix, Matrix.one_apply]
    have h_tr := h x y
    dsimp [Matrix.trace] at h_tr
    exact h_tr

end InfoGeometry.Modular.Choi

end noncomputable section
