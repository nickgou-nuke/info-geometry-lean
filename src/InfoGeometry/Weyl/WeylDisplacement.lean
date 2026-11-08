import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

open Matrix BigOperators

namespace InfoGeometry.Weyl

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-! ### 1. Inductive Braiding Lemmas -/

/-- Pushing a single Clock operator Z across c Shift operators:
    Z * X^c = ω^c • (X^c * Z) -/
theorem clock_mul_shift_pow (X Z : A) (ω : R)
    (hZX : Z * X = ω • (X * Z)) (c : ℕ) :
    Z * X ^ c = (ω ^ c) • (X ^ c * Z) := by
  induction c with
  | zero =>
    simp only [pow_zero, mul_one, one_mul, one_smul]
  | succ c ih =>
    rw [pow_succ' X c, ← mul_assoc, hZX]
    rw [smul_mul_assoc, mul_assoc, ih]
    rw [mul_smul_comm, smul_smul]
    rw [← pow_succ' ω c, ← mul_assoc, ← pow_succ' X c]

/-- Pushing b Clock operators across c Shift operators:
    Z^b * X^c = ω^(b * c) • (X^c * Z^b) -/
theorem clock_pow_mul_shift_pow (X Z : A) (ω : R)
    (hZX : Z * X = ω • (X * Z)) (b c : ℕ) :
    Z ^ b * X ^ c = (ω ^ (b * c)) • (X ^ c * Z ^ b) := by
  induction b with
  | zero =>
    simp only [pow_zero, one_mul, mul_one, zero_mul, one_smul]
  | succ b ih =>
    rw [pow_succ' Z b, mul_assoc, ih]
    rw [mul_smul_comm, ← mul_assoc, clock_mul_shift_pow X Z ω hZX c]
    rw [smul_mul_assoc, mul_assoc, smul_smul]
    rw [← pow_add, ← pow_succ' Z b]
    have h_exp : b * c + c = (b + 1) * c := by ring
    rw [h_exp]

/-! ### 2. Discrete Weyl Displacement Operators & Composition Law -/

/-- The discrete Weyl displacement operator D(a, b) = X^a * Z^b. -/
def weylD (X Z : A) (a b : ℕ) : A :=
  X ^ a * Z ^ b

/-- **Main Theorem (Projective Composition Law):**
    D(a, b) * D(c, d) = ω^(b * c) • D(a + c, b + d). -/
theorem weylD_mul (X Z : A) (ω : R)
    (hZX : Z * X = ω • (X * Z)) (a b c d : ℕ) :
    weylD X Z a b * weylD X Z c d = (ω ^ (b * c)) • weylD X Z (a + c) (b + d) := by
  dsimp [weylD]
  have h_mid : (X ^ a * Z ^ b) * (X ^ c * Z ^ d) =
      (ω ^ (b * c)) • (X ^ a * (X ^ c * Z ^ b) * Z ^ d) := by
    calc
      (X ^ a * Z ^ b) * (X ^ c * Z ^ d)
        = X ^ a * (Z ^ b * X ^ c) * Z ^ d := by simp only [mul_assoc]
      _ = X ^ a * ((ω ^ (b * c)) • (X ^ c * Z ^ b)) * Z ^ d := by
        rw [clock_pow_mul_shift_pow X Z ω hZX b c]
      _ = (ω ^ (b * c)) • (X ^ a * (X ^ c * Z ^ b) * Z ^ d) := by
        rw [mul_smul_comm, smul_mul_assoc]
  rw [h_mid]
  congr 1
  calc
    X ^ a * (X ^ c * Z ^ b) * Z ^ d
      = (X ^ a * X ^ c) * (Z ^ b * Z ^ d) := by simp only [mul_assoc]
    _ = X ^ (a + c) * Z ^ (b + d) := by rw [← pow_add, ← pow_add]

/-- **Heisenberg Group Commutation Relation:**
    The projective phase difference is governed by the symplectic form σ = a * d - b * c:
    ω^(a * d) • (D(a, b) * D(c, d)) = ω^(b * c) • (D(c, d) * D(a, b)). -/
theorem weylD_comm (X Z : A) (ω : R)
    (hZX : Z * X = ω • (X * Z)) (a b c d : ℕ) :
    (ω ^ (a * d)) • (weylD X Z a b * weylD X Z c d) =
    (ω ^ (b * c)) • (weylD X Z c d * weylD X Z a b) := by
  rw [weylD_mul X Z ω hZX a b c d]
  rw [weylD_mul X Z ω hZX c d a b]
  simp only [smul_smul]
  have h_add1 : a + c = c + a := add_comm a c
  have h_add2 : b + d = d + b := add_comm b d
  rw [h_add1, h_add2]
  congr 1
  rw [← pow_add, ← pow_add]
  congr 1
  ring

/-! ### 3. Specialization to Sylvester Clock and Shift Matrices -/

variable {n : ℕ} [NeZero n]

/-- Concrete Weyl displacement operators for Sylvester matrices. -/
def sylvesterD (shift clock : Matrix (ZMod n) (ZMod n) R) (a b : ℕ) :
    Matrix (ZMod n) (ZMod n) R :=
  weylD shift clock a b

/-- Specialization of the projective composition law to Sylvester matrices. -/
theorem sylvesterD_mul (shift clock : Matrix (ZMod n) (ZMod n) R) (ω : R)
    (h_braid : clock * shift = ω • (shift * clock)) (a b c d : ℕ) :
    sylvesterD shift clock a b * sylvesterD shift clock c d =
      (ω ^ (b * c)) • sylvesterD shift clock (a + c) (b + d) :=
  weylD_mul shift clock ω h_braid a b c d

end InfoGeometry.Weyl
