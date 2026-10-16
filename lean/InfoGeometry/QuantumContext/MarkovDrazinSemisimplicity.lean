/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic
import InfoGeometry.Canonical.AttentionPolarizedSinkhornBridge

/-!
# Semisimplicity obstruction for finite stochastic attention

For a finite row-stochastic real matrix, `1 - P` has no nonzero length-two
generalized zero-vector chain. The proof is finite: stochastic powers preserve
coordinate bounds, while such a chain would force linear growth. This is a
prerequisite for a group-inverse bridge, equivalently the Drazin equations at
`k = 1` (Drazin index at most one); no Drazin inverse is constructed here.

The action convention is explicit: `P *ᵥ x` applies the row-stochastic matrix
to a column vector of observables. This file does not establish an evolution
law for row probability distributions. The sign convention in the companion
owner is `I - P`.
-/

open Matrix
open scoped BigOperators

namespace InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A stochastic row maps a uniformly bounded vector into the same interval. -/
lemma stochastic_mulVec_abs_bound (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (x : ι → ℝ) (B : ℝ)
    (hB : ∀ j, |x j| ≤ B) (i : ι) : |(P *ᵥ x) i| ≤ B := by
  have hrow := Matrix.sum_row_of_mem_rowStochastic hP i
  have hnonneg : ∀ j, 0 ≤ P i j := fun j => Matrix.nonneg_of_mem_rowStochastic hP
  have hlow : -B ≤ (P *ᵥ x) i := by
    rw [Matrix.mulVec, dotProduct]
    calc
      -B = ∑ j, P i j * (-B) := by rw [← Finset.sum_mul, hrow, one_mul]
      _ ≤ ∑ j, P i j * x j := by
        apply Finset.sum_le_sum
        intro j _
        have hx : -B ≤ x j := (abs_le.mp (hB j)).1
        exact mul_le_mul_of_nonneg_left hx (hnonneg j)
  have hhigh : (P *ᵥ x) i ≤ B := by
    rw [Matrix.mulVec, dotProduct]
    calc
      ∑ j, P i j * x j ≤ ∑ j, P i j * B := by
        apply Finset.sum_le_sum
        intro j _
        have hx : x j ≤ B := (abs_le.mp (hB j)).2
        exact mul_le_mul_of_nonneg_left hx (hnonneg j)
      _ = B := by rw [← Finset.sum_mul, hrow, one_mul]
  exact abs_le.mpr ⟨hlow, hhigh⟩

/-- The iterates of a row-stochastic matrix preserve a uniform coordinate bound. -/
lemma stochastic_pow_mulVec_abs_bound (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (x : ι → ℝ) (B : ℝ)
    (hB : ∀ j, |x j| ≤ B) (n : ℕ) (i : ι) : |((P ^ n) *ᵥ x) i| ≤ B := by
  exact stochastic_mulVec_abs_bound (P ^ n)
    ((Matrix.rowStochastic ℝ ι).pow_mem hP n) x B hB i

/-- There is no nonzero length-two generalized eigenvector at eigenvalue one. -/
theorem no_length_two_generalized_fixed_vector
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (x y : ι → ℝ)
    (hxy : (1 - P) *ᵥ x = y)
    (hyy : (1 - P) *ᵥ y = 0) : y = 0 := by
  have hPx : P *ᵥ x = x - y := by
    funext i
    have hi := congrFun hxy i
    have hi' : x i - (P *ᵥ x) i = y i := by
      simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hi
    change (P *ᵥ x) i = x i - y i
    linarith
  have hPy : P *ᵥ y = y := by
    funext i
    have hi := congrFun hyy i
    have hi' : y i - (P *ᵥ y) i = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hi
    change (P *ᵥ y) i = y i
    linarith
  have h_iter : ∀ n : ℕ, (P ^ n) *ᵥ x = fun i => x i - (n : ℝ) * y i := by
    intro n
    induction n with
    | zero =>
        funext i
        simp
    | succ n ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
        change P *ᵥ (x - (n : ℝ) • y) = fun i => x i - (↑(n + 1) : ℝ) * y i
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hPx, hPy]
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [Nat.cast_succ]
        ring
  let B : ℝ := ∑ j, |x j|
  have hB : ∀ j, |x j| ≤ B := by
    intro j
    dsimp [B]
    exact Finset.single_le_sum (fun k _ => abs_nonneg (x k)) (Finset.mem_univ j)
  funext i
  by_contra hne
  have hpos : 0 < |y i| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * B / |y i|)
  have hbound := stochastic_pow_mulVec_abs_bound P hP x B hB n i
  rw [h_iter n] at hbound
  have hxi : |x i| ≤ B := hB i
  have hny : |(n : ℝ) * y i| ≤ 2 * B := by
    have hrepr : (n : ℝ) * y i = x i - (x i - (n : ℝ) * y i) := by ring
    rw [hrepr]
    calc
      |x i - (x i - (n : ℝ) * y i)| ≤ |x i| + |x i - (n : ℝ) * y i| := abs_sub _ _
      _ ≤ B + B := add_le_add hxi hbound
      _ = 2 * B := by ring
  have hncast : (2 * B / |y i|) < (n : ℝ) := by exact_mod_cast hn
  have hlarge : 2 * B < |(n : ℝ) * y i| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    have := (div_lt_iff₀ hpos).mp hncast
    nlinarith
  exact (not_lt_of_ge hny) hlarge

namespace Attention

open InfoGeometry.Canonical.Attention

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance markovAttentionFinNonempty : Nonempty (Fin n) :=
  ⟨⟨0, Fact.out⟩⟩

/-- The polarized attention transition matrix has no length-two generalized
fixed-vector chain at eigenvalue one. -/
theorem polarizedAttention_no_length_two_chain
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (x y : Fin n → ℝ)
    (hxy : (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) *ᵥ x = y)
    (hyy : (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) *ᵥ y = 0) :
    y = 0 := by
  exact InfoGeometry.QuantumContext.MarkovDrazin.no_length_two_generalized_fixed_vector
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    x y hxy hyy

end Attention

end InfoGeometry.QuantumContext.MarkovDrazin
