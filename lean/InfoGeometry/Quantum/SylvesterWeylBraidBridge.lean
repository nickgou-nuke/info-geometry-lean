import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Single-Sheet Weyl Braid Relation for Sylvester Matrices
-/

namespace SylvesterWeylBraid

variable (n : ℕ) [NeZero n]
variable {R : Type*} [CommRing R]

def clockMatrix (ω : R) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j then ω ^ i.val else 0

def shiftMatrix : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j + 1 then 1 else 0

lemma pow_eq_pow_mod (ω : R) (hn : ω ^ n = 1) (m : ℕ) :
    ω ^ m = ω ^ (m % n) := by
  have h : ω ^ m = ω ^ (n * (m / n) + m % n) := by rw [Nat.div_add_mod]
  rw [h, pow_add, pow_mul, hn, one_pow, one_mul]

lemma zmod_val_add_one (j : ZMod n) :
    (j + 1).val = (j.val + 1) % n := by
  have : (1 : ZMod n) = (1 : ℕ) := by simp
  rw [this, ZMod.val_add, ZMod.val_natCast]
  rw [Nat.add_mod, Nat.mod_mod, ←Nat.add_mod]

lemma pow_val_add_one (ω : R) (hn : ω ^ n = 1) (j : ZMod n) :
    ω ^ (j + 1).val = ω * ω ^ j.val := by
  rw [zmod_val_add_one n j]
  rw [← pow_eq_pow_mod n ω hn (j.val + 1)]
  rw [pow_succ, mul_comm]

theorem sylvester_weyl_braid_relation (ω : R) (hn : ω ^ n = 1) :
    clockMatrix n ω * shiftMatrix n = ω • (shiftMatrix n * clockMatrix n ω) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  have hLHS : (∑ k : ZMod n, clockMatrix n ω i k * shiftMatrix n k j) =
      if i = j + 1 then ω ^ i.val else 0 := by
    have hsum : (∑ k : ZMod n, clockMatrix n ω i k * shiftMatrix n k j) =
        clockMatrix n ω i i * shiftMatrix n i j := by
      apply Finset.sum_eq_single i
      · intro k _ hk
        simp only [clockMatrix, Matrix.of_apply]
        have hne : ¬(i = k) := hk.symm
        rw [if_neg hne, zero_mul]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    have hval : clockMatrix n ω i i * shiftMatrix n i j =
        if i = j + 1 then ω ^ i.val else 0 := by
      simp only [clockMatrix, shiftMatrix, Matrix.of_apply, if_true]
      split_ifs with h
      · rw [mul_one]
      · rw [mul_zero]
    rw [hsum, hval]
  have hRHS : (∑ k : ZMod n, shiftMatrix n i k * clockMatrix n ω k j) =
      if i = j + 1 then ω ^ j.val else 0 := by
    have hsum : (∑ k : ZMod n, shiftMatrix n i k * clockMatrix n ω k j) =
        shiftMatrix n i j * clockMatrix n ω j j := by
      apply Finset.sum_eq_single j
      · intro k _ hk
        simp only [clockMatrix, Matrix.of_apply]
        rw [if_neg hk, mul_zero]
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))
    have hval : shiftMatrix n i j * clockMatrix n ω j j =
        if i = j + 1 then ω ^ j.val else 0 := by
      simp only [clockMatrix, shiftMatrix, Matrix.of_apply, if_true]
      split_ifs with h
      · rw [one_mul]
      · rw [zero_mul]
    rw [hsum, hval]
  rw [hLHS, hRHS]
  split_ifs with h
  · rw [h]
    exact pow_val_add_one n ω hn j
  · rw [mul_zero]

end SylvesterWeylBraid

namespace InfoGeometry.Weyl

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Moving one clock factor across a power of the shift. -/
theorem clock_mul_shift_pow (X Z : A) (ω : R)
    (hZX : Z * X = ω • (X * Z)) (c : ℕ) :
    Z * X ^ c = (ω ^ c) • (X ^ c * Z) := by
  induction c with
  | zero => simp
  | succ c ih =>
      nth_rewrite 1 [pow_succ]
      calc
        Z * (X ^ c * X) = (Z * X ^ c) * X := by rw [mul_assoc]
        _ = ((ω ^ c) • (X ^ c * Z)) * X := by rw [ih]
        _ = (ω ^ c) • ((X ^ c * Z) * X) := by rw [smul_mul_assoc]
        _ = (ω ^ c) • (X ^ c * (Z * X)) := by rw [mul_assoc]
        _ = (ω ^ c) • (X ^ c * (ω • (X * Z))) := by rw [hZX]
        _ = (ω ^ (c + 1)) • (X ^ (c + 1) * Z) := by
          rw [Algebra.mul_smul_comm, smul_smul]
          calc
            (ω ^ c * ω) • (X ^ c * (X * Z)) =
                ω ^ (c + 1) • (X ^ c * (X * Z)) := by rw [pow_succ]
            _ = ω ^ (c + 1) • ((X ^ c * X) * Z) := by
                exact congrArg (fun y : A => ω ^ (c + 1) • y)
                  (mul_assoc (X ^ c) X Z).symm
            _ = ω ^ (c + 1) • (X ^ (c + 1) * Z) := by
                exact congrArg (fun y : A => ω ^ (c + 1) • (y * Z))
                  (pow_succ X c).symm

/-- Moving a power of the clock across a power of the shift. -/
theorem clock_pow_mul_shift_pow (X Z : A) (ω : R)
    (hZX : Z * X = ω • (X * Z)) (b c : ℕ) :
    Z ^ b * X ^ c = (ω ^ (b * c)) • (X ^ c * Z ^ b) := by
  induction b with
  | zero => simp
  | succ b ih =>
      nth_rewrite 1 [pow_succ]
      calc
        (Z ^ b * Z) * X ^ c = Z ^ b * (Z * X ^ c) := by rw [mul_assoc]
        _ = Z ^ b * ((ω ^ c) • (X ^ c * Z)) := by
          rw [clock_mul_shift_pow X Z ω hZX c]
        _ = (ω ^ c) • (Z ^ b * (X ^ c * Z)) := by rw [mul_smul_comm]
        _ = (ω ^ c) • ((Z ^ b * X ^ c) * Z) := by rw [mul_assoc]
        _ = (ω ^ c) • (((ω ^ (b * c)) • (X ^ c * Z ^ b)) * Z) := by rw [ih]
        _ = (ω ^ ((b + 1) * c)) • (X ^ c * Z ^ (b + 1)) := by
          rw [smul_mul_assoc, smul_smul]
          have hexp : c + b * c = (b + 1) * c := by
            simp [Nat.succ_mul, Nat.add_comm]
          calc
            (ω ^ c * ω ^ (b * c)) • ((X ^ c * Z ^ b) * Z) =
                ω ^ (c + b * c) • ((X ^ c * Z ^ b) * Z) := by rw [← pow_add]
            _ = ω ^ ((b + 1) * c) • ((X ^ c * Z ^ b) * Z) := by rw [hexp]
            _ = ω ^ ((b + 1) * c) • (X ^ c * (Z ^ b * Z)) := by rw [← mul_assoc]
            _ = ω ^ ((b + 1) * c) • (X ^ c * Z ^ (b + 1)) := by
                exact congrArg (fun y : A => ω ^ ((b + 1) * c) • (X ^ c * y))
                  (pow_succ Z b).symm

/-- The discrete Weyl displacement `D(a,b) = X^a Z^b`. -/
def weylD (X Z : A) (a b : ℕ) : A := X ^ a * Z ^ b

/-- The projective composition law for clock-shift displacement operators. -/
theorem weylD_mul (X Z : A) (ω : R)
    (hZX : Z * X = ω • (X * Z)) (a b c d : ℕ) :
    weylD X Z a b * weylD X Z c d =
      (ω ^ (b * c)) • weylD X Z (a + c) (b + d) := by
  dsimp [weylD]
  calc
    (X ^ a * Z ^ b) * (X ^ c * Z ^ d) =
        X ^ a * (Z ^ b * X ^ c) * Z ^ d := by simp only [mul_assoc]
    _ = X ^ a * ((ω ^ (b * c)) • (X ^ c * Z ^ b)) * Z ^ d := by
        rw [clock_pow_mul_shift_pow X Z ω hZX b c]
    _ = (ω ^ (b * c)) • (X ^ a * (X ^ c * Z ^ b) * Z ^ d) := by
        rw [mul_smul_comm, smul_mul_assoc]
    _ = (ω ^ (b * c)) • (X ^ (a + c) * Z ^ (b + d)) := by
        congr 1
        simp [pow_add, mul_assoc]

/-- Matrix specialization of the displacement composition law. -/
theorem sylvesterD_mul {n : ℕ} [NeZero n] {R : Type*} [CommRing R]
    (X Z : Matrix (ZMod n) (ZMod n) R) (ω : R)
    (hZX : Z * X = ω • (X * Z)) (a b c d : ℕ) :
    weylD X Z a b * weylD X Z c d =
      (ω ^ (b * c)) • weylD X Z (a + c) (b + d) :=
  weylD_mul X Z ω hZX a b c d

end InfoGeometry.Weyl
