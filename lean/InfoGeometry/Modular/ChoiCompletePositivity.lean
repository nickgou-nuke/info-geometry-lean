import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Complete Positivity and the Choi–Jamiołkowski Isomorphism

This module formalizes:
1. The standard matrix units E_{ij} and the Choi matrix of a superoperator Φ:
     Λ_Φ = ∑_{i,j} Φ(E_{ij}) ⊗ E_{ij}
     (Λ_Φ)_{(a, i), (b, j)} = (Φ(E_{ij}))_{a, b}
2. The Choi matrix of a single Kraus channel Φ_V(X) = V X V† is a rank-1 outer product:
     (Λ_{Φ_V})_{(a, i), (b, j)} = V_{a, i} * conj(V_{b, j}) = |vec(V)⟩⟨vec(V)|
3. Quadratic form of the single Kraus Choi matrix:
     ⟨z, Λ_{Φ_V} z⟩ = |∑_{a,i} conj(z_{a,i}) * V_{a,i}|² ≥ 0
4. Complete Positivity of Multichannel Kraus Operations:
     For any channel ℰ(X) = ∑_k V_k X V_k†, its Choi matrix satisfies:
     ⟨z, Λ_ℰ z⟩ = ∑_k |⟨z, vec(V_k)⟩|² ≥ 0 (Positive Semi-Definite).

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open Matrix
open BigOperators
open Finset

namespace InfoGeometry.Modular.Choi

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

local notation "Mat" => Matrix n n ℂ
local notation "BipartiteMat" => Matrix (n × n) (n × n) ℂ
local notation "BipartiteVec" => (n × n) → ℂ

/-!
=============================================================================
PART 1: Standard Basis Matrices and the Choi Matrix Definition
=============================================================================
-/

/-- The standard matrix unit E_{ij}: 1 at entry (i, j) and 0 elsewhere. -/
def stdBasis (i j : n) : Mat :=
  Matrix.of (fun a b => if a = i ∧ b = j then 1 else 0)

@[simp]
theorem stdBasis_apply (i j a b : n) :
    stdBasis i j a b = if a = i ∧ b = j then 1 else 0 := rfl

/-- 
  The single Kraus superoperator:
  Φ_V(X) = V * X * star V
-/
def krausTerm (V_k : Mat) (X : Mat) : Mat :=
  V_k * X * star V_k

/-- The Choi matrix of an arbitrary finite matrix superoperator. -/
def choiMatrix (E : Mat →ₗ[ℂ] Mat) : BipartiteMat :=
  Matrix.of (fun ⟨a, i⟩ ⟨b, j⟩ => E (stdBasis i j) a b)

@[simp]
theorem choiMatrix_apply (E : Mat →ₗ[ℂ] Mat) (a i b j : n) :
    choiMatrix E ⟨a, i⟩ ⟨b, j⟩ = E (stdBasis i j) a b := rfl

/-- A finite Kraus channel, as a complex-linear matrix superoperator. -/
def krausChannel {ι : Type*} [Fintype ι] (V : ι → Mat) : Mat →ₗ[ℂ] Mat where
  toFun X := ∑ k, krausTerm (V k) X
  map_add' X Y := by
    simp [krausTerm, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp [krausTerm, smul_mul_assoc, mul_smul_comm, Finset.smul_sum]

/-- 
  The Choi matrix of a single Kraus channel:
  (Λ_{Φ_V})_{(a, i), (b, j)} = (Φ_V(E_{ij}))_{a, b} = V_{a, i} * conj(V_{b, j})
-/
def krausChoiMatrix (V_k : Mat) : BipartiteMat :=
  Matrix.of (fun ⟨a, i⟩ ⟨b, j⟩ => V_k a i * star (V_k b j))

@[simp]
theorem krausChoiMatrix_apply (V_k : Mat) (a i b j : n) :
    krausChoiMatrix V_k ⟨a, i⟩ ⟨b, j⟩ = V_k a i * star (V_k b j) := rfl

/-- 
  THEOREM 1: The Choi Matrix of a Single Kraus Channel Matches the Channel Action on E_{ij}.
  (V * E_{ij} * V†)_{a, b} = V_{a, i} * conj(V_{b, j})
-/
theorem kraus_on_stdBasis_eq_choi (V_k : Mat) (i j a b : n) :
    krausTerm V_k (stdBasis i j) a b = krausChoiMatrix V_k ⟨a, i⟩ ⟨b, j⟩ := by
  dsimp [krausTerm, stdBasis, krausChoiMatrix, Matrix.mul_apply, Matrix.star_apply]
  -- Expanding the double matrix product (V * E_{ij} * V†)_{a, b}
  have h_inner (r : n) : (∑ c : n, V_k a c * (if c = i ∧ r = j then (1 : ℂ) else 0)) =
      if r = j then V_k a i else 0 := by
    rw [Finset.sum_eq_single i]
    · simp only [true_and]
      split_ifs <;> simp
    · intro c _ hneq
      have : (c = i ∧ r = j) = False := by simp [hneq]
      simp [this]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  
  have h_outer : (∑ r : n, (∑ c : n, V_k a c * (if c = i ∧ r = j then (1 : ℂ) else 0)) * star (V_k b r)) =
      V_k a i * star (V_k b j) := by
    calc
      (∑ r : n, (∑ c : n, V_k a c * (if c = i ∧ r = j then (1 : ℂ) else 0)) * star (V_k b r))
        = ∑ r : n, (if r = j then V_k a i else 0) * star (V_k b r) := by
          refine Finset.sum_congr rfl (fun r _ => by rw [h_inner r])
      _ = V_k a i * star (V_k b j) := by
        rw [Finset.sum_eq_single j]
        · simp only [if_true]
        · intro r _ hneq
          simp only [if_neg hneq, zero_mul]
        · intro hj
          exact False.elim (hj (Finset.mem_univ j))
  
  exact h_outer

/-!
=============================================================================
PART 2: Complete Positivity (CP) / Positive Semi-Definiteness of Choi Matrix
=============================================================================
-/

/-- Vectorized inner product with Kraus generator: ⟨z, vec(V)⟩ = ∑_{a,i} conj(z_{a,i}) * V_{a,i}. -/
def vecInner (z : BipartiteVec) (V_k : Mat) : ℂ :=
  ∑ p : n × n, star (z p) * V_k p.1 p.2

/-- 
  The Quadratic Form of a Matrix M evaluated on vector z:
  ⟨z, M z⟩ = ∑_{p, q} conj(z_p) * M_{p, q} * z_q
-/
def quadraticForm (M : BipartiteMat) (z : BipartiteVec) : ℂ :=
  ∑ p : n × n, ∑ q : n × n, star (z p) * M p q * z q

/-- 
  THEOREM 2: The Quadratic Form of the Single Kraus Choi Matrix is Exactly the Modulus Squared:
  ⟨z, Λ_{Φ_V} z⟩ = |⟨z, vec(V)⟩|² = vecInner(z, V) * conj(vecInner(z, V))
-/
theorem kraus_choi_quadraticForm (V_k : Mat) (z : BipartiteVec) :
    quadraticForm (krausChoiMatrix V_k) z = vecInner z V_k * star (vecInner z V_k) := by
  dsimp [quadraticForm, vecInner, krausChoiMatrix]
  have h_star : star (∑ p : n × n, star (z p) * V_k p.1 p.2) =
      ∑ q : n × n, star (V_k q.1 q.2) * z q := by
    rw [star_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [StarMul.star_mul, star_star]
  change (∑ p : n × n, ∑ q : n × n, star (z p) * (V_k p.1 p.2 * star (V_k q.1 q.2)) * z q) =
    (∑ p : n × n, star (z p) * V_k p.1 p.2) * star (∑ p : n × n, star (z p) * V_k p.1 p.2)
  rw [h_star]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  ring

/-- 
  THEOREM 3 (Single-Channel Complete Positivity):
  The quadratic form of the single Kraus Choi matrix is purely real and non-negative:
  ⟨z, Λ_{Φ_V} z⟩ ≥ 0
-/
theorem kraus_choi_nonneg (V_k : Mat) (z : BipartiteVec) :
    0 ≤ (quadraticForm (krausChoiMatrix V_k) z).re ∧ (quadraticForm (krausChoiMatrix V_k) z).im = 0 := by
  rw [kraus_choi_quadraticForm V_k z]
  have h_mul_star : vecInner z V_k * star (vecInner z V_k) = (Complex.normSq (vecInner z V_k) : ℂ) := by
    exact Complex.mul_conj (vecInner z V_k)
  rw [h_mul_star]
  constructor
  · rw [Complex.ofReal_re]
    exact Complex.normSq_nonneg (vecInner z V_k)
  · rw [Complex.ofReal_im]

/-!
=============================================================================
PART 3: Multichannel Complete Positivity (Choi's Theorem)
=============================================================================
-/

/-- The Choi Matrix of a Multichannel Quantum Operation ℰ = ∑_k Φ_{V_k}. -/
def multichannelChoiMatrix (V : ι → Mat) : BipartiteMat :=
  ∑ k, krausChoiMatrix (V k)

theorem choiMatrix_krausChannel_eq_multichannel
    {ι : Type*} [Fintype ι] (V : ι → Mat) :
    choiMatrix (krausChannel V) = multichannelChoiMatrix V := by
  ext ⟨a, i⟩ ⟨b, j⟩
  dsimp [choiMatrix, krausChannel, multichannelChoiMatrix]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  exact kraus_on_stdBasis_eq_choi (V k) i j a b

/-- 
  MASTER THEOREM 4 (Choi Complete Positivity):
  For ANY multichannel Kraus operation ℰ(X) = ∑_k V_k X V_k†, its Choi matrix
  is manifestly positive semi-definite:
    ⟨z, Λ_ℰ z⟩ ≥ 0
-/
theorem multichannel_choi_nonneg (V : ι → Mat) (z : BipartiteVec) :
    0 ≤ (quadraticForm (multichannelChoiMatrix V) z).re ∧
    (quadraticForm (multichannelChoiMatrix V) z).im = 0 := by
  have h_swap : quadraticForm (multichannelChoiMatrix V) z =
      ∑ k : ι, quadraticForm (krausChoiMatrix (V k)) z := by
    dsimp [multichannelChoiMatrix, quadraticForm]
    have h_entry (p q : n × n) : (∑ k : ι, krausChoiMatrix (V k)) p q = ∑ k : ι, krausChoiMatrix (V k) p q :=
      Matrix.sum_apply p q Finset.univ (fun k => krausChoiMatrix (V k))
    simp_rw [h_entry]
    simp only [Finset.mul_sum, Finset.sum_mul]
    have h_step : (∑ p : n × n, ∑ q : n × n, ∑ k : ι, (star (z p) * krausChoiMatrix (V k) p q * z q)) =
        ∑ p : n × n, ∑ k : ι, ∑ q : n × n, (star (z p) * krausChoiMatrix (V k) p q * z q) := by
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
    change (∑ p : n × n, ∑ q : n × n, ∑ k : ι, star (z p) * krausChoiMatrix (V k) p q * z q) =
      ∑ k : ι, ∑ p : n × n, ∑ q : n × n, star (z p) * krausChoiMatrix (V k) p q * z q
    rw [h_step]
    exact Finset.sum_comm
  rw [h_swap]
  constructor
  · rw [Complex.re_sum]
    refine Finset.sum_nonneg (fun k _ => (kraus_choi_nonneg (V k) z).1)
  · rw [Complex.im_sum]
    have h_zeros : ∀ k ∈ (Finset.univ : Finset ι), (quadraticForm (krausChoiMatrix (V k)) z).im = 0 :=
      fun k _ => (kraus_choi_nonneg (V k) z).2
    rw [Finset.sum_congr rfl h_zeros, Finset.sum_const_zero]

end InfoGeometry.Modular.Choi

end noncomputable section
