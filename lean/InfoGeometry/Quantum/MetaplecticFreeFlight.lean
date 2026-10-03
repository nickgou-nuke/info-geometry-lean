import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Matrix
open scoped Matrix
open scoped BigOperators

namespace MetaplecticFreeFlight

variable {n : ℕ} [NeZero n]
variable {R : Type*} [CommRing R]

/-! ### 1. Triangular Numbers & Modular Arithmetic Helpers -/

/-- Triangular numbers tri(m) = m * (m - 1) / 2 in ℕ. -/
def tri : ℕ → ℕ
  | 0 => 0
  | m + 1 => tri m + m

/-- Exact reduction lemma: Since ω ^ n = 1, scaling modulo n preserves the phase. -/
lemma pow_mul_mod (ω : R) (hn : ω ^ n = 1) (a b : ℕ) :
    ω ^ (a * (b % n)) = ω ^ (a * b) := by
  have h : a * b = n * (a * (b / n)) + a * (b % n) := by
    calc a * b = a * (n * (b / n) + b % n) := by rw [Nat.div_add_mod]
    _ = n * (a * (b / n)) + a * (b % n) := by ring
  have h1 : ω ^ (n * (a * (b / n))) = 1 := by
    rw [pow_mul, hn, one_pow]
  rw [h, pow_add, h1, one_mul]

/-! ### 2. Sylvester Operators & Quadratic Chirp -/

/-- Sylvester Clock operator C: diagonal with entries ω ^ i.val. -/
def clockMatrix (ω : R) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j then ω ^ i.val else 0

/-- Sylvester Shift operator S: cyclic forward permutation S e_j = e_{j+1}. -/
def shiftMatrix : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j + 1 then 1 else 0

/-- Sylvester Adjoint Shift S*: cyclic backward permutation S* e_{j+1} = e_j. -/
def shiftMatrixAdj : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i + 1 = j then 1 else 0

/-- Quadratic Chirp operator U_chirp(κ): diagonal matrix with Fresnel phases ω ^ (κ * tri i.val). -/
def chirpMatrix (ω : R) (κ : ℕ) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j then ω ^ (κ * tri i.val) else 0

/-! ### 3. The Discrete Fourier Transform (DFT) Matrix -/

/-- The Discrete Fourier Transform matrix F on ZMod n: F_{j, k} = ω ^ (j.val * k.val). -/
def dftMatrix (ω : R) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun j k => ω ^ (j.val * k.val)

/-- The Adjoint / Inverse Phase DFT matrix F†: F†_{j, k} = ω_inv ^ (j.val * k.val). -/
def dftMatrixAdj (ω_inv : R) : Matrix (ZMod n) (ZMod n) R :=
  dftMatrix ω_inv

/-! ### 4. The Free-Flight Shear Operator -/

/-- The Free-Flight Shear Operator U_flight(τ) = F† * U_chirp(τ) * F. -/
def flightOperator (ω ω_inv : R) (τ : ℕ) : Matrix (ZMod n) (ZMod n) R :=
  dftMatrixAdj (n := n) ω_inv * chirpMatrix (n := n) ω τ * dftMatrix (n := n) ω

/-! ### 5. Fourier Intertwining Theorems (Duality of C and S) -/

lemma sum_mul_shiftMatrix (M : Matrix (ZMod n) (ZMod n) R) (i j : ZMod n) :
    (∑ k : ZMod n, M i k * shiftMatrix (n := n) k j) = M i (j + 1) := by
  have h : (∑ k : ZMod n, M i k * shiftMatrix (n := n) k j) =
      M i (j + 1) * shiftMatrix (n := n) (j + 1) j := by
    apply Finset.sum_eq_single (j + 1)
    · intro k _ hk
      simp only [shiftMatrix, Matrix.of_apply]
      rw [if_neg hk, mul_zero]
    · intro hj
      exact False.elim (hj (Finset.mem_univ (j + 1)))
  rw [h]
  simp only [shiftMatrix, Matrix.of_apply, if_pos rfl, mul_one]

lemma sum_clockMatrix_mul (d : ZMod n → R) (M : Matrix (ZMod n) (ZMod n) R) (i j : ZMod n) :
    (∑ k : ZMod n, (if i = k then d i else 0) * M k j) = d i * M i j := by
  have h : (∑ k : ZMod n, (if i = k then d i else 0) * M k j) =
      (if i = i then d i else 0) * M i j := by
    apply Finset.sum_eq_single i
    · intro k _ hk
      have : ¬(i = k) := hk.symm
      rw [if_neg this, zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [h, if_pos rfl]

lemma sum_shiftMatrixAdj_mul (M : Matrix (ZMod n) (ZMod n) R) (i j : ZMod n) :
    (∑ k : ZMod n, shiftMatrixAdj (n := n) i k * M k j) = M (i + 1) j := by
  have h : (∑ k : ZMod n, shiftMatrixAdj (n := n) i k * M k j) =
      shiftMatrixAdj (n := n) i (i + 1) * M (i + 1) j := by
    apply Finset.sum_eq_single (i + 1)
    · intro k _ hk
      simp only [shiftMatrixAdj, Matrix.of_apply]
      rw [if_neg hk.symm, zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ (i + 1)))
  rw [h]
  simp only [shiftMatrixAdj, Matrix.of_apply, if_pos rfl, one_mul]

lemma sum_mul_clockMatrix (M : Matrix (ZMod n) (ZMod n) R) (d : ZMod n → R) (i j : ZMod n) :
    (∑ k : ZMod n, M i k * (if k = j then d j else 0)) = M i j * d j := by
  have h : (∑ k : ZMod n, M i k * (if k = j then d j else 0)) =
      M i j * (if j = j then d j else 0) := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  rw [h, if_pos rfl]

/-- Fourier Duality 1: The DFT transforms the Shift operator into the Clock operator:
    F * S = C * F. -/
theorem dftMatrix_mul_shiftMatrix (ω : R) (hn : ω ^ n = 1) :
    dftMatrix (n := n) ω * shiftMatrix (n := n) =
      clockMatrix (n := n) ω * dftMatrix (n := n) ω := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [sum_mul_shiftMatrix]
  rw [sum_clockMatrix_mul (fun k => ω ^ k.val)]
  dsimp [dftMatrix, clockMatrix]
  have hval : (j + 1).val = (j.val + 1) % n := by
    have h : ((j.val + 1 : ℕ) : ZMod n) = j + 1 := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_val]
    rw [← h, ZMod.val_natCast]
  rw [hval]
  rw [pow_mul_mod ω hn i.val (j.val + 1)]
  have : i.val * (j.val + 1) = i.val + i.val * j.val := by ring
  rw [this, pow_add, mul_comm]

/-- Fourier Duality 2: The DFT transforms the Clock operator into the Adjoint Shift operator:
    S* * F = F * C. -/
theorem shiftMatrixAdj_mul_dftMatrix (ω : R) (hn : ω ^ n = 1) :
    shiftMatrixAdj (n := n) * dftMatrix (n := n) ω =
      dftMatrix (n := n) ω * clockMatrix (n := n) ω := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [sum_shiftMatrixAdj_mul]
  rw [sum_mul_clockMatrix _ (fun k => ω ^ k.val)]
  dsimp [dftMatrix, clockMatrix]
  have hval : (i + 1).val = (i.val + 1) % n := by
    have h : ((i.val + 1 : ℕ) : ZMod n) = i + 1 := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_val]
    rw [← h, ZMod.val_natCast]
  rw [hval]
  rw [mul_comm ((i.val + 1) % n) j.val]
  rw [pow_mul_mod ω hn j.val (i.val + 1)]
  have : j.val * (i.val + 1) = i.val * j.val + j.val := by ring
  rw [this, pow_add]

/-! ### 6. Algebraic Properties of Free Flight -/

/-- Chirp operator vanishes at flight time τ = 0 to the identity matrix. -/
theorem chirpMatrix_zero (ω : R) :
    chirpMatrix (n := n) ω 0 = 1 := by
  ext i j
  dsimp [chirpMatrix]
  rw [zero_mul, pow_zero]
  simp only [Matrix.one_apply]

/-- At zero flight time, the flight operator reduces to the bare DFT product F† * F. -/
theorem flightOperator_zero (ω ω_inv : R) :
    flightOperator (n := n) ω ω_inv 0 =
      dftMatrixAdj (n := n) ω_inv * dftMatrix (n := n) ω := by
  dsimp [flightOperator]
  rw [chirpMatrix_zero, Matrix.mul_one]

/-- The chirp matrix commutes with the Clock operator: U_chirp * C = C * U_chirp. -/
theorem chirpMatrix_mul_clockMatrix (ω : R) (κ : ℕ) :
    chirpMatrix (n := n) ω κ * clockMatrix (n := n) ω =
      clockMatrix (n := n) ω * chirpMatrix (n := n) ω κ := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [sum_clockMatrix_mul (fun k => ω ^ (κ * tri k.val))]
  rw [sum_clockMatrix_mul (fun k => ω ^ k.val)]
  simp only [clockMatrix, chirpMatrix, Matrix.of_apply]
  split_ifs with h
  · rw [mul_comm]
  · rw [mul_zero, mul_zero]

/-- Momentum Preservation in Fourier Space:
    Because U_chirp commutes with C, the free-flight kinetic energy commutes
    with the Fourier-transformed Shift operator (F * S = C * F). -/
theorem chirpMatrix_mul_fourier_shift (ω : R) (hn : ω ^ n = 1) (τ : ℕ) :
    chirpMatrix (n := n) ω τ * (dftMatrix (n := n) ω * shiftMatrix (n := n)) =
      (clockMatrix (n := n) ω * chirpMatrix (n := n) ω τ) * dftMatrix (n := n) ω := by
  rw [dftMatrix_mul_shiftMatrix ω hn]
  rw [← Matrix.mul_assoc]
  rw [chirpMatrix_mul_clockMatrix]
  rw [Matrix.mul_assoc]

end MetaplecticFreeFlight
