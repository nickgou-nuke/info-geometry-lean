/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.SylvesterWeylBraidBridge
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Binary Weyl words

The existing Sylvester clock and shift matrices at dimension two give four
ordered words over any commutative coefficient ring. The binary labels live
in `ZMod 2`, while the matrices need not have characteristic two. Reduction
of the existing natural-exponent Weyl law retains the central sign.
-/

namespace InfoGeometry.Quantum.BinaryWeyl

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The dimension-two Sylvester shift matrix. -/
abbrev shift : Matrix (Fin 2) (Fin 2) R := SylvesterWeylBraid.shiftMatrix 2

/-- The dimension-two Sylvester clock matrix at parameter `-1`. -/
abbrev clock : Matrix (Fin 2) (Fin 2) R := SylvesterWeylBraid.clockMatrix 2 (-1)

/-- The sign character of the additive group `ZMod 2`. -/
def phase (t : ZMod 2) : R := (-1) ^ t.val

@[simp] theorem phase_zero : phase (R := R) 0 = 1 := by
  rw [phase, ZMod.val_zero, pow_zero]

@[simp] theorem phase_one : phase (R := R) 1 = -1 := by
  rw [phase, ZMod.val_one_eq_one_mod]
  norm_num

theorem phase_add (s t : ZMod 2) :
    phase (R := R) (s + t) = phase s * phase t := by
  rw [phase, ZMod.val_add,
    ← SylvesterWeylBraid.pow_eq_pow_mod 2 (-1 : R) (by simp), pow_add]
  rfl

@[simp] theorem phase_mul_self (t : ZMod 2) :
    phase (R := R) t * phase t = 1 := by
  fin_cases t <;> norm_num [phase, ZMod.val]

theorem phase_ne_zero [Nontrivial R] (t : ZMod 2) : phase (R := R) t ≠ 0 := by
  fin_cases t <;> simp [phase, ZMod.val]

theorem phase_injective [CharZero R] : Function.Injective (phase (R := R)) := by
  intro s t h
  fin_cases s <;> fin_cases t <;>
    norm_num [phase, ZMod.val, ZMod, Fin.ext_iff] at * <;> rfl

/-- The ordered binary Weyl word `X^a Z^b`, using the existing Sylvester matrices. -/
def word (a b : ZMod 2) : Matrix (ZMod 2) (ZMod 2) R :=
  Weyl.weylD shift clock a.val b.val

private theorem shift_eq :
    shift (R := R) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem clock_eq :
    clock (R := R) = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact pow_zero (-1 : R)
  · rfl
  · rfl
  · exact pow_one (-1 : R)

set_option backward.isDefEq.respectTransparency false in
private theorem shift_sq : (shift (R := R)) ^ 2 = 1 := by
  rw [shift_eq, pow_two, Matrix.mul_fin_two]
  simpa only [zero_mul, one_mul, zero_add, add_zero] using (Matrix.one_fin_two (α := R)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem clock_sq : (clock (R := R)) ^ 2 = 1 := by
  rw [clock_eq, pow_two, Matrix.mul_fin_two]
  simpa only [zero_mul, one_mul, mul_zero, mul_one, zero_add, add_zero, neg_mul_neg] using
    (Matrix.one_fin_two (α := R)).symm

@[simp] theorem word_zero_zero : word (R := R) 0 0 = 1 := by
  simp [word, Weyl.weylD]

/-- Binary addition of labels retains the Weyl multiplication phase. -/
theorem word_mul (a b c d : ZMod 2) :
    word (R := R) a b * word c d = phase (R := R) (b * c) • word (a + c) (b + d) := by
  unfold word
  rw [Weyl.weylD_mul _ _ (-1 : R)
    (SylvesterWeylBraid.sylvester_weyl_braid_relation 2 (-1) (by simp))]
  have hs : (SylvesterWeylBraid.shiftMatrix 2 (R := R)) ^ (a.val + c.val) =
      (SylvesterWeylBraid.shiftMatrix 2 (R := R)) ^ (a + c).val := by
    rw [ZMod.val_add]
    exact SylvesterWeylBraid.pow_eq_pow_mod 2 _ shift_sq _
  have hz : (SylvesterWeylBraid.clockMatrix 2 (-1 : R)) ^ (b.val + d.val) =
      (SylvesterWeylBraid.clockMatrix 2 (-1 : R)) ^ (b + d).val := by
    rw [ZMod.val_add]
    exact SylvesterWeylBraid.pow_eq_pow_mod 2 _ clock_sq _
  have hp : (-1 : R) ^ (b.val * c.val) = phase (b * c) := by
    rw [phase, ZMod.val_mul]
    exact SylvesterWeylBraid.pow_eq_pow_mod 2 _ (by simp) _
  simp only [Weyl.weylD, shift, clock, hs, hz, hp]

/-- Transpose reverses the order of the symmetric Sylvester generators. -/
theorem word_transpose_eq_reverse (a b : ZMod 2) :
    (word (R := R) a b)ᵀ = clock ^ b.val * shift ^ a.val := by
  have hx : (shift (R := R))ᵀ = shift := by
    rw [shift_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hz : (clock (R := R))ᵀ = clock := by
    rw [clock_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp only [word, Weyl.weylD, Matrix.transpose_mul, Matrix.transpose_pow]
  change clockᵀ ^ b.val * shiftᵀ ^ a.val = clock ^ b.val * shift ^ a.val
  rw [hz, hx]
  rfl

/-- An `XZ` factor is skew-symmetric; a real sign cannot alter this parity. -/
theorem word_transpose (a b : ZMod 2) :
    (word (R := R) a b)ᵀ = phase (R := R) (a * b) • word a b := by
  rw [word_transpose_eq_reverse]
  have hleft : word (R := R) 0 b * word a 0 = clock ^ b.val * shift ^ a.val := by
    simp [word, Weyl.weylD, shift, clock]
    rfl
  rw [← hleft, word_mul]
  simp only [zero_add, add_zero, mul_comm b a]

/-- The trace pairing of the four binary Weyl words is diagonal. -/
theorem word_trace_pair (u v : ZMod 2 × ZMod 2) :
    Matrix.trace ((word (R := R) u.1 u.2)ᵀ * word v.1 v.2) =
      if u = v then 2 else 0 := by
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, d⟩
  let X : Matrix (Fin 2) (Fin 2) R := shift
  let Z : Matrix (Fin 2) (Fin 2) R := clock
  have hx : X = !![0, 1; 1, 0] := shift_eq
  have hz : Z = !![1, 0; 0, -1] := clock_eq
  change Matrix.trace ((X ^ a.val * Z ^ b.val)ᵀ * (X ^ c.val * Z ^ d.val)) = _
  have binary (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide
  rcases binary a with rfl | rfl <;> rcases binary b with rfl | rfl <;>
    rcases binary c with rfl | rfl <;> rcases binary d with rfl | rfl <;>
    norm_num [ZMod.val_zero, ZMod.val_one_eq_one_mod,
      hx, hz, Matrix.one_fin_two, Matrix.mul_fin_two,
      Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, Prod.ext_iff]

/-- A noncommutativity witness on the actual two-by-two carrier. -/
theorem shift_clock_noncommute [CharZero R] :
    shift (R := R) * clock ≠ clock * shift := by
  intro h
  simp only [shift_eq, clock_eq, Matrix.mul_fin_two] at h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 0 1) h
  norm_num at he

end InfoGeometry.Quantum.BinaryWeyl
