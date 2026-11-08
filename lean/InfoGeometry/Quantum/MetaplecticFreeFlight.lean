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

/-- Fourier Duality 1: The DFT transforms the Shift operator into the Clock operator:
    F * S = C * F. -/
theorem dftMatrix_mul_shiftMatrix (ω : R) (hn : ω ^ n = 1) :
    dftMatrix (n := n) ω * shiftMatrix (n := n) =
      clockMatrix (n := n) ω * dftMatrix (n := n) ω := by
  ext i j
  dsimp [Matrix.mul_apply, dftMatrix, shiftMatrix, clockMatrix, Matrix.of_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, one_mul]
  have hval : (j + 1).val = (j.val + 1) % n := by
    have h : ((j.val + 1 : ℕ) : ZMod n) = j + 1 := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    rw [← h, ZMod.val_natCast]
  rw [hval, pow_mul_mod ω hn i.val (j.val + 1)]
  have : i.val * (j.val + 1) = i.val + i.val * j.val := by ring
  rw [this, pow_add, mul_comm]

/-- Fourier Duality 2: The DFT transforms the Clock operator into the Adjoint Shift operator:
    S* * F = F * C. -/
theorem shiftMatrixAdj_mul_dftMatrix (ω : R) (hn : ω ^ n = 1) :
    shiftMatrixAdj (n := n) * dftMatrix (n := n) ω =
      dftMatrix (n := n) ω * clockMatrix (n := n) ω := by
  ext i j
  dsimp [Matrix.mul_apply, dftMatrix, shiftMatrixAdj, clockMatrix, Matrix.of_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, one_mul]
  have hval : (i + 1).val = (i.val + 1) % n := by
    have h : ((i.val + 1 : ℕ) : ZMod n) = i + 1 := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    rw [← h, ZMod.val_natCast]
  rw [hval, mul_comm ((i.val + 1) % n) j.val]
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
  dsimp [Matrix.mul_apply, clockMatrix, chirpMatrix, Matrix.of_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, one_mul]
  split_ifs with h
  · subst h; rw [mul_comm]
  · rfl

/-- Momentum Preservation in Fourier Space:
    Because U_chirp commutes with C, the free-flight kinetic energy commutes
    with the Fourier-transformed Shift operator (F * S = C * F). -/
theorem chirpMatrix_mul_fourier_shift (ω : R) (hn : ω ^ n = 1) (τ : ℕ) :
    chirpMatrix (n := n) ω τ * (dftMatrix (n := n) ω * shiftMatrix (n := n)) =
      (clockMatrix (n := n) ω * chirpMatrix (n := n) ω τ) * dftMatrix (n := n) ω := by
  rw [dftMatrix_mul_shiftMatrix ω hn]
  rw [← Matrix.mul_assoc]
  rw [chirpMatrix_mul_clockMatrix]
  

end MetaplecticFreeFlight
