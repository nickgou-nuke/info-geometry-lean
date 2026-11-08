import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Matrix
open scoped Matrix
open scoped BigOperators

namespace MetaplecticWeil

variable {n : ℕ} [NeZero n]
variable {R : Type*} [CommRing R]

/-! ### 1. Triangular Numbers and Modular Boundary Arithmetic -/

/-- Triangular numbers tri(m) = m * (m - 1) / 2 defined recursively in ℕ. -/
def tri : ℕ → ℕ
  | 0 => 0
  | m + 1 => tri m + m

lemma tri_add_two (m : ℕ) : tri (m + 2) = tri m + m + (m + 1) := rfl

/-- For an odd integer n = 2k + 1, the n-th triangular number is a multiple of n: tri(n) = n * k. -/
lemma tri_two_mul_add_one (k : ℕ) : tri (2 * k + 1) = (2 * k + 1) * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hstep : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [hstep]
    have hdef : tri ((2 * k + 1) + 2) = tri (2 * k + 1) + (2 * k + 1) + ((2 * k + 1) + 1) := rfl
    rw [hdef, ih]
    ring

lemma tri_pred_add_pred (n : ℕ) (hn : 0 < n) : tri (n - 1) + (n - 1) = tri n := by
  cases n with
  | zero => contradiction
  | succ m => rfl

/-- Value analysis of (j + 1) in ZMod n: either interior advance or cyclic wrap-around. -/
lemma zmod_val_add_one_cases (j : ZMod n) :
    ((j + 1).val = j.val + 1) ∨ ((j + 1).val = 0 ∧ j.val + 1 = n) := by
  have hj : j.val < n := ZMod.val_lt j
  have hval : (j + 1).val = (j.val + 1) % n := by
    have h : ((j.val + 1 : ℕ) : ZMod n) = j + 1 := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    rw [← h, ZMod.val_natCast]
  by_cases hlt : j.val + 1 < n
  · left
    rw [hval, Nat.mod_eq_of_lt hlt]
  · right
    have heq : j.val + 1 = n := by omega
    refine ⟨?_, heq⟩
    rw [hval, heq, Nat.mod_self]

/-- Key Phase Identity: The quadratic chirp phase under cyclic shift j ↦ j + 1. -/
lemma omega_pow_mul_tri_succ (ω : R) (hn : ω ^ n = 1) (k : ℕ) (hn_odd : n = 2 * k + 1)
    (κ : ℕ) (j : ZMod n) :
    ω ^ (κ * tri (j + 1).val) = ω ^ (κ * (tri j.val + j.val)) := by
  have hn_pos : 0 < n := by subst hn_odd; omega
  rcases zmod_val_add_one_cases j with h1 | ⟨h0, h_sum⟩
  · -- Interior step: (j + 1).val = j.val + 1
    rw [h1]
    rfl
  · -- Boundary wrap-around: (j + 1).val = 0 and j.val + 1 = n
    have hj_val : j.val = n - 1 := by omega
    rw [h0]
    have h_lhs : ω ^ (κ * tri 0) = 1 := by
      change ω ^ (κ * 0) = 1
      rw [mul_zero, pow_zero]
    have h_tri : tri j.val + j.val = n * k := by
      rw [hj_val, tri_pred_add_pred n hn_pos, hn_odd, tri_two_mul_add_one k]
    have h_rhs : ω ^ (κ * (tri j.val + j.val)) = 1 := by
      rw [h_tri]
      have h_exp : κ * (n * k) = n * (κ * k) := by ring
      rw [h_exp, pow_mul, hn, one_pow]
    rw [h_lhs, h_rhs]

/-! ### 2. Sylvester Operators & Quadratic Chirp -/

/-- Sylvester Clock operator C: diagonal with entries ω ^ i.val. -/
def clockMatrix (ω : R) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j then ω ^ i.val else 0

/-- Powers of the Clock operator C^κ: diagonal with entries ω ^ (κ * i.val). -/
def clockMatrixPow (ω : R) (κ : ℕ) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j then ω ^ (κ * i.val) else 0

/-- Sylvester Shift operator S: cyclic forward permutation S e_j = e_{j+1}. -/
def shiftMatrix : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j + 1 then 1 else 0

/-- The Quadratic Chirp operator U_κ: diagonal matrix with Fresnel phases ω ^ (κ * tri i.val). -/
def chirpMatrix (ω : R) (κ : ℕ) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j then ω ^ (κ * tri i.val) else 0

/-- Inverse Quadratic Chirp operator U_κ⁻¹ parameterized by the inverse root ω_inv. -/
def chirpMatrixInv (ω_inv : R) (κ : ℕ) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j then ω_inv ^ (κ * tri i.val) else 0

/-! ### 3. Diagonal Sum Evaluation Helpers -/

lemma mul_diagonal_left (d : ZMod n → R) (M : Matrix (ZMod n) (ZMod n) R) (i j : ZMod n) :
    (∑ k : ZMod n, (if i = k then d i else 0) * M k j) = d i * M i j := by
  have hsum : (∑ k : ZMod n, (if i = k then d i else 0) * M k j) =
      (if i = i then d i else 0) * M i j := by
    apply Finset.sum_eq_single i
    · intro k _ hk
      have : ¬(i = k) := hk.symm
      rw [if_neg this, zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [hsum, if_pos rfl]

lemma mul_diagonal_right (M : Matrix (ZMod n) (ZMod n) R) (d : ZMod n → R) (i j : ZMod n) :
    (∑ k : ZMod n, M i k * (if k = j then d j else 0)) = M i j * d j := by
  have hsum : (∑ k : ZMod n, M i k * (if k = j then d j else 0)) =
      M i j * (if j = j then d j else 0) := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  rw [hsum, if_pos rfl]

/-! ### 4. Commutation and Shear Relations -/

/-- Commutation: The quadratic chirp operator commutes with the Clock operator: U_κ * C = C * U_κ. -/
theorem chirpMatrix_mul_clockMatrix (ω : R) (κ : ℕ) :
    chirpMatrix (n := n) ω κ * clockMatrix (n := n) ω =
      clockMatrix (n := n) ω * chirpMatrix (n := n) ω κ := by
  ext i j
  dsimp [chirpMatrix, clockMatrix, Matrix.mul_apply, Matrix.of_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs with h
  · subst h; rw [mul_comm]
  · rfl

/-- Parabolic Shear: The quadratic chirp shears the Shift operator: U_κ * S = S * C^κ * U_κ. -/
theorem chirpMatrix_mul_shiftMatrix (ω : R) (hn : ω ^ n = 1) (k : ℕ) (hn_odd : n = 2 * k + 1)
    (κ : ℕ) :
    chirpMatrix (n := n) ω κ * shiftMatrix (n := n) =
      (shiftMatrix (n := n) * clockMatrixPow (n := n) ω κ) * chirpMatrix (n := n) ω κ := by
  ext i j
  dsimp [chirpMatrix, shiftMatrix, clockMatrixPow, Matrix.mul_apply, Matrix.of_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, one_mul]
  split_ifs with h
  · subst h
    rw [← pow_add]
    rw [omega_pow_mul_tri_succ ω hn k hn_odd κ j]
    congr 1
    ring
  · rfl

/-! ### 5. Invertibility of the Chirp Operator -/

/-- Left and right inverse: U_κ * U_κ⁻¹ = 1. -/
theorem chirpMatrix_mul_inv (ω ω_inv : R) (h_inv : ω * ω_inv = 1) (κ : ℕ) :
    chirpMatrix (n := n) ω κ * chirpMatrixInv (n := n) ω_inv κ = 1 := by
  ext i j
  dsimp [chirpMatrix, chirpMatrixInv, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs with h
  · subst h
    rw [← mul_pow, h_inv, one_pow]
  · rfl

/-- Right inverse: the inverse-root chirp also multiplies back to the identity.

Together with `chirpMatrix_mul_inv`, this records a two-sided algebraic
inverse. It does not by itself assert unitarity, which requires a star
structure and a compatibility condition between `ω_inv` and `star ω`. -/
theorem chirpMatrixInv_mul (ω ω_inv : R) (h_inv : ω * ω_inv = 1) (κ : ℕ) :
    chirpMatrixInv (n := n) ω_inv κ * chirpMatrix (n := n) ω κ = 1 := by
  have h_inv' : ω_inv * ω = 1 := by rw [mul_comm, h_inv]
  ext i j
  dsimp [chirpMatrix, chirpMatrixInv, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs with h
  · subst h
    rw [← mul_pow, h_inv', one_pow]
  · rfl

/-! ### 6. Metaplectic Covariance Theorems -/

/-- The Metaplectic Adjoint Action Ad_U(M) = U * M * U_inv. -/
def adjointAct (U U_inv M : Matrix (ZMod n) (ZMod n) R) : Matrix (ZMod n) (ZMod n) R :=
  U * M * U_inv

/-- Metaplectic covariance on the Clock operator: Ad_{U_κ}(C) = C. -/
theorem metaplectic_covariance_clock (ω ω_inv : R) (h_inv : ω * ω_inv = 1) (κ : ℕ) :
    adjointAct (chirpMatrix (n := n) ω κ) (chirpMatrixInv (n := n) ω_inv κ)
               (clockMatrix (n := n) ω) = clockMatrix (n := n) ω := by
  dsimp [adjointAct]
  rw [chirpMatrix_mul_clockMatrix, Matrix.mul_assoc, chirpMatrix_mul_inv (n := n) ω ω_inv h_inv κ,
      Matrix.mul_one]

/-- Metaplectic covariance on the Shift operator: Ad_{U_κ}(S) = S * C^κ. -/
theorem metaplectic_covariance_shift (ω ω_inv : R) (hn : ω ^ n = 1)
    (h_inv : ω * ω_inv = 1) (k : ℕ) (hn_odd : n = 2 * k + 1) (κ : ℕ) :
    adjointAct (chirpMatrix (n := n) ω κ) (chirpMatrixInv (n := n) ω_inv κ)
               (shiftMatrix (n := n)) = shiftMatrix (n := n) * clockMatrixPow (n := n) ω κ := by
  dsimp [adjointAct]
  rw [chirpMatrix_mul_shiftMatrix (n := n) ω hn k hn_odd κ, Matrix.mul_assoc,
      chirpMatrix_mul_inv (n := n) ω ω_inv h_inv κ, Matrix.mul_one]

end MetaplecticWeil
