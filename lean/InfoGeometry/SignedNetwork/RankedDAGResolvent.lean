import Mathlib

/-!
# Exact finite causal resolvent for a ranked graph

Rows are destinations and columns are sources. A nonzero entry of `T` must
strictly increase a finite rank. Nilpotence is proved from that support law,
not supplied as a replacement for acyclicity. The coefficient ring may be
noncommutative, for example a ring of additive endomorphisms acting on a
nonassociative Zorn payload. This does not give the Zorn product associativity.

The resulting inverse is a Green operator for `1 - T`. No Dirac operator,
retarded quantum correlator, softmax normalization, or stochastic semantics is
inferred from the finite inverse alone.
-/

noncomputable section

namespace InfoGeometry.SignedNetwork.RankedDAGResolvent

open scoped Matrix

section FiniteGeometric

variable {R : Type*} [Ring R]

/-- Finite geometric sum in an arbitrary associative ring. -/
def finiteGreen (T : R) (N : ℕ) : R := ∑ k ∈ Finset.range N, T ^ k

@[simp] theorem finiteGreen_zero (T : R) : finiteGreen T 0 = 0 := by
  simp [finiteGreen]

theorem finiteGreen_succ (T : R) (N : ℕ) :
    finiteGreen T (N + 1) = finiteGreen T N + T ^ N := by
  exact Finset.sum_range_succ (fun k => T ^ k) N

/-- Left telescoping identity; the order of factors is retained. -/
theorem one_sub_mul_finiteGreen (T : R) (N : ℕ) :
    (1 - T) * finiteGreen T N = 1 - T ^ N := by
  induction N with
  | zero => simp [finiteGreen]
  | succ N ih =>
      rw [finiteGreen_succ, mul_add, ih, pow_succ']
      noncomm_ring

/-- Right telescoping identity; no commutative-ring instance is assumed. -/
theorem finiteGreen_mul_one_sub (T : R) (N : ℕ) :
    finiteGreen T N * (1 - T) = 1 - T ^ N := by
  induction N with
  | zero => simp [finiteGreen]
  | succ N ih =>
      rw [finiteGreen_succ, add_mul, ih, pow_succ]
      noncomm_ring

end FiniteGeometric

section Ranked

variable {V R : Type*} [Fintype V] [DecidableEq V] [Ring R]
variable {N : ℕ}

/-- A weighted finite graph with a supplied topological ranking. -/
structure RankedKernel (V R : Type*) [Fintype V] [DecidableEq V] [Ring R]
    (N : ℕ) where
  rank : V → Fin N
  weight : Matrix V V R
  strict_support : ∀ i j, (rank i).val ≤ (rank j).val → weight i j = 0

namespace RankedKernel

variable (K : RankedKernel V R N)

/-- A nonzero length-`k` contribution requires at least `k` rank increases. -/
theorem pow_entry_eq_zero (k : ℕ) (i j : V)
    (h : (K.rank i).val < (K.rank j).val + k) :
    (K.weight ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
      have hij : i ≠ j := by
        intro heq
        subst j
        omega
      simp [hij]
  | succ k ih =>
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _hl
      by_cases hil : (K.rank i).val ≤ (K.rank l).val
      · rw [K.strict_support i l hil, zero_mul]
      · have hlj : (K.rank l).val < (K.rank j).val + k := by omega
        rw [ih l j hlj, mul_zero]

/-- Nilpotence is a consequence of the finite ranking. -/
theorem weight_pow_rank_bound : K.weight ^ N = 0 := by
  ext i j
  apply K.pow_entry_eq_zero
  have hi := (K.rank i).isLt
  omega

/-- The causal Green operator of `1 - weight`. -/
def green : Matrix V V R := finiteGreen K.weight N

/-- The finite path sum is a left inverse of the causal recurrence operator. -/
theorem recurrence_mul_green : (1 - K.weight) * K.green = 1 := by
  rw [green, one_sub_mul_finiteGreen, K.weight_pow_rank_bound, sub_zero]

/-- The same path sum is also a right inverse. -/
theorem green_mul_recurrence : K.green * (1 - K.weight) = 1 := by
  rw [green, finiteGreen_mul_one_sub, K.weight_pow_rank_bound, sub_zero]

/-- The Green operator contains no response to a source of strictly later rank. -/
theorem green_entry_eq_zero_of_rank_lt (i j : V)
    (h : (K.rank i).val < (K.rank j).val) : K.green i j = 0 := by
  change (∑ k ∈ Finset.range N, K.weight ^ k) i j = 0
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro k _hk
  apply K.pow_entry_eq_zero
  omega

/-- The finite inverse solves the inhomogeneous equation exactly. -/
theorem solve (J : Matrix V V R) : (1 - K.weight) * (K.green * J) = J := by
  rw [← mul_assoc, K.recurrence_mul_green, one_mul]

/-- Uniqueness is derived from the proved two-sided inverse. -/
theorem solution_unique (J X : Matrix V V R)
    (hX : (1 - K.weight) * X = J) : X = K.green * J := by
  calc
    X = (K.green * (1 - K.weight)) * X := by
      rw [K.green_mul_recurrence, one_mul]
    _ = K.green * ((1 - K.weight) * X) := mul_assoc _ _ _
    _ = K.green * J := by rw [hX]

end RankedKernel
end Ranked

/-- A two-vertex causal recurrence need not have row-normalized response. -/
def twoVertexTransfer : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 2, 0]

def twoVertexGreen : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 2, 1]

theorem twoVertex_inverse :
    (1 - twoVertexTransfer) * twoVertexGreen = 1 ∧
      twoVertexGreen * (1 - twoVertexTransfer) = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [twoVertexTransfer, twoVertexGreen, Matrix.mul_apply, Fin.sum_univ_two]

theorem twoVertex_not_row_normalized : (∑ j, twoVertexGreen 1 j) ≠ 1 := by
  norm_num [twoVertexGreen, Fin.sum_univ_two]

end InfoGeometry.SignedNetwork.RankedDAGResolvent
