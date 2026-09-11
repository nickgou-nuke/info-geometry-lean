import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Convex.Birkhoff

noncomputable section

namespace ImprovedLLMTheory

open scoped BigOperators
open Matrix

variable {N : Type*} [Fintype N]

/-- Row sums of a square matrix. -/
def rowSum (A : Matrix N N ℝ) (i : N) : ℝ :=
  ∑ j, A i j

/-- Column sums of a square matrix. -/
def colSum (A : Matrix N N ℝ) (j : N) : ℝ :=
  ∑ i, A i j

/-- A Birkhoff transport plan: nonnegative and doubly normalized. -/
def IsDoublyStochastic (A : Matrix N N ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ (∀ i, rowSum A i = 1) ∧ (∀ j, colSum A j = 1)

/-- A doubly stochastic matrix decomposes as a convex combination of permutation matrices. -/
theorem attention_has_birkhoff_decomposition
    {N : Type*} [Fintype N] [DecidableEq N] (A : Matrix N N ℝ) (hA : A ∈ doublyStochastic ℝ N) :
    ∃ w : Equiv.Perm N → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧ ∑ σ, w σ • σ.permMatrix ℝ = A := by
  exact exists_eq_sum_perm_of_mem_doublyStochastic hA

/-- A nonnegative low-rank factorization through `Fin r`. -/
structure NonnegativeFactorization (n r : ℕ) where
  W : Matrix (Fin n) (Fin r) ℝ
  H : Matrix (Fin n) (Fin r) ℝ
  hW : ∀ i j, 0 ≤ W i j
  hH : ∀ i j, 0 ≤ H i j

namespace NonnegativeFactorization

variable {n r : ℕ}

/-- The reconstructed graph is nonnegative. -/
theorem graph_nonnegative (F : NonnegativeFactorization n r) :
    ∀ i j, 0 ≤ (F.W * F.H.transpose) i j := by
  intro i j
  simp [Matrix.mul_apply, Matrix.transpose]
  exact Finset.sum_nonneg (by
    intro k hk
    exact mul_nonneg (F.hW i k) (F.hH j k))

end NonnegativeFactorization

/-- Q/K/V triality as a cyclic permutation of three operator channels. -/
structure QKVTriality (n : ℕ) where
  q : Matrix (Fin n) (Fin n) ℝ
  k : Matrix (Fin n) (Fin n) ℝ
  v : Matrix (Fin n) (Fin n) ℝ

namespace QKVTriality

variable {n : ℕ}

/-- One step of QKV triality. -/
def rotate (T : QKVTriality n) : QKVTriality n :=
  { q := T.k, k := T.v, v := T.q }

@[simp] theorem rotate_q (T : QKVTriality n) : (rotate T).q = T.k := rfl
@[simp] theorem rotate_k (T : QKVTriality n) : (rotate T).k = T.v := rfl
@[simp] theorem rotate_v (T : QKVTriality n) : (rotate T).v = T.q := rfl

/-- Triality has order three. -/
theorem rotate_order3 (T : QKVTriality n) : rotate (rotate (rotate T)) = T := by
  cases T
  rfl

/-- The total trace is invariant under triality rotation. -/
theorem trace_rotate (T : QKVTriality n) :
    Matrix.trace (rotate T).q + Matrix.trace (rotate T).k + Matrix.trace (rotate T).v =
      Matrix.trace T.q + Matrix.trace T.k + Matrix.trace T.v := by
  cases T
  simp [rotate]
  ring

end QKVTriality

/-- A complete transport/factorization/triality bundle. -/
structure ImprovedLLM (n r : ℕ) where
  transport : Matrix N N ℝ
  transport_ok : IsDoublyStochastic transport
  factorization : NonnegativeFactorization n r
  triality : QKVTriality n
  anomaly_free : Matrix.trace triality.q + Matrix.trace triality.k + Matrix.trace triality.v = 0

/-- Doubly stochastic rows conserve total mass. -/
theorem row_mass_eq_card (A : Matrix N N ℝ) (hrow : ∀ i, rowSum A i = 1) :
    ∑ i, rowSum A i = Fintype.card N := by
  calc
    ∑ i, rowSum A i = ∑ i, (1 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hrow i
    _ = Fintype.card N := by
      have hcard : ((Fintype.card N : ℕ) : ℝ) = ∑ _ : N, (1 : ℝ) := by
        exact_mod_cast (Fintype.card_eq_sum_ones (α := N))
      exact hcard.symm

/-- A doubly stochastic transport plan has total mass `card N`. -/
theorem transport_total_mass (A : Matrix N N ℝ) (hA : IsDoublyStochastic A) :
    ∑ i, rowSum A i = Fintype.card N := by
  exact row_mass_eq_card A hA.2.1

/-- The triality cycle preserves anomaly compensation. -/
theorem triality_preserves_anomaly {n : ℕ} (T : QKVTriality n)
    (h : Matrix.trace T.q + Matrix.trace T.k + Matrix.trace T.v = 0) :
    Matrix.trace (QKVTriality.rotate T).q + Matrix.trace (QKVTriality.rotate T).k +
        Matrix.trace (QKVTriality.rotate T).v = 0 := by
  cases T
  simp [QKVTriality.rotate] at h ⊢
  linarith

/-- The Stern-Brocot mediant of two rationals encoded by natural numerators/denominators. -/
def mediant (a b c d : ℕ) : ℚ :=
  ((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ)

/--
The Stern-Brocot mediant lies between the two input rationals, assuming positive
denominators and an initial ordering.
-/
theorem mediant_between
    {a b c d : ℕ}
    (hb : 0 < b) (hd : 0 < d)
    (hord : (a : ℚ) / (b : ℚ) ≤ (c : ℚ) / (d : ℚ)) :
    (a : ℚ) / (b : ℚ) ≤ mediant a b c d ∧ mediant a b c d ≤ (c : ℚ) / (d : ℚ) := by
  constructor
  · have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
    have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    have hsumq : (0 : ℚ) < ((b + d : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_pos_right b hd
    have hcross : (a : ℚ) * (d : ℚ) ≤ (c : ℚ) * (b : ℚ) := by
      exact (div_le_div_iff₀ hbq hdq).mp hord
    rw [mediant]
    refine (div_le_div_iff₀ hbq hsumq).2 ?_
    norm_num [mul_add, add_mul]
    linarith
  · have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
    have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    have hsumq : (0 : ℚ) < ((b + d : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_pos_right b hd
    have hcross : (a : ℚ) * (d : ℚ) ≤ (c : ℚ) * (b : ℚ) := by
      exact (div_le_div_iff₀ hbq hdq).mp hord
    rw [mediant]
    refine (div_le_div_iff₀ hsumq hdq).2 ?_
    norm_num [mul_add, add_mul]
    linarith

end ImprovedLLMTheory
