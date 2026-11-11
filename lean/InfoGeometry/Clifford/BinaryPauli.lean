/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Algebra.Zorn.CochainTwistSeparation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Ordered real Pauli words and binary commutation

The local frame is the existing real Clifford frame `1, Eplus, J1, Eminus`.
The order is `Z^a X^b`, so the product exponent is `b * c`.
Two tensor factors give a genuine real four-dimensional matrix action and
four binary labels. The signed multiplication law retains information that
is lost by passing to projective incidence alone.

This is a finite real matrix construction. It does not identify the real Lie
algebra with either `su(4)` or `su*(4)`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.BinaryPauli

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Algebra.Zorn.Z2ThreeCochainBridge
open InfoGeometry.Algebra.Zorn.CochainTwistSeparation
open scoped Kronecker

/-- The two bits record the ordered local word `Z^a X^b`. -/
abbrev LocalLabel := ZMod 2 × ZMod 2

/-- The real Clifford frame, with phase bit first and shift bit second. -/
def localWord (x : LocalLabel) : Mat2 :=
  if x.1 = 0 then (if x.2 = 0 then 1 else J1)
  else (if x.2 = 0 then Eplus else Eminus)

private theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The ordered local product; the sign is not replaced by commutativity. -/
theorem localWord_mul (x y : LocalLabel) :
    localWord x * localWord y =
      (signUnit (x.2 * y.1) : ℝ) • localWord (x + y) := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
    rcases bit_cases c with rfl | rfl <;>
    rcases bit_cases d with rfl | rfl
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [localWord, signUnit, Eplus, Eminus, J1,
        Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

@[simp] theorem localWord_zero : localWord 0 = 1 := by
  simp [localWord]

@[simp] theorem localWord_phase : localWord (1, 0) = Eplus := by
  simp [localWord]

@[simp] theorem localWord_shift : localWord (0, 1) = J1 := by
  simp [localWord]

@[simp] theorem localWord_phase_shift : localWord (1, 1) = Eminus := by
  simp [localWord]

/-- Four binary labels, ordered by the two real Clifford tensor factors. -/
abbrev Label := LocalLabel × LocalLabel

/-- The product-index presentation of the full real `4 × 4` matrix algebra. -/
abbrev Mat := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

/-- An actual matrix tensor product, not a multiplication table supplied as data. -/
def word (v : Label) : Mat := localWord v.1 ⊗ₖ localWord v.2

/-- Moving each left shift past the corresponding right phase gives this exponent. -/
def exponent (v w : Label) : ZMod 2 :=
  v.1.2 * w.1.1 + v.2.2 * w.2.1

/-- The alternating form measures the change in sign on reversing the product. -/
def symplectic (v w : Label) : ZMod 2 := exponent v w + exponent w v

theorem exponent_add_left (u v w : Label) :
    exponent (u + v) w = exponent u w + exponent v w := by
  simp only [exponent, Prod.fst_add, Prod.snd_add]
  ring

theorem exponent_add_right (u v w : Label) :
    exponent u (v + w) = exponent u v + exponent u w := by
  simp only [exponent, Prod.fst_add, Prod.snd_add]
  ring

/-- The order-sensitive coefficient is a genuine associative two-cocycle. -/
theorem exponent_cocycle (u v w : Label) :
    exponent u v + exponent (u + v) w =
      exponent v w + exponent u (v + w) := by
  rw [exponent_add_left, exponent_add_right]
  abel

@[simp] theorem label_add_self (v : Label) : v + v = 0 := by
  ext <;> exact CharTwo.add_self_eq_zero _

@[simp] theorem symplectic_self (v : Label) : symplectic v v = 0 := by
  exact CharTwo.add_self_eq_zero _

theorem symplectic_comm (v w : Label) : symplectic v w = symplectic w v := by
  exact add_comm _ _

theorem symplectic_add_left (u v w : Label) :
    symplectic (u + v) w = symplectic u w + symplectic v w := by
  simp only [symplectic, exponent_add_left, exponent_add_right]
  abel

theorem symplectic_add_right (u v w : Label) :
    symplectic u (v + w) = symplectic u v + symplectic u w := by
  simp only [symplectic, exponent_add_left, exponent_add_right]
  abel

/-- All pairs of points on a binary line have the same commutation parity. -/
theorem symplectic_line (v w : Label) :
    symplectic v (v + w) = symplectic v w ∧
      symplectic w (v + w) = symplectic v w := by
  simp [symplectic_add_right, symplectic_comm]

/-- Four coordinate probes prove nondegeneracy of the alternating form. -/
theorem symplectic_nondegenerate (v : Label) :
    (∀ w, symplectic v w = 0) ↔ v = 0 := by
  constructor
  · intro h
    apply Prod.ext
    · apply Prod.ext
      · simpa [symplectic, exponent] using h ((0, 1), (0, 0))
      · simpa [symplectic, exponent] using h ((1, 0), (0, 0))
    · apply Prod.ext
      · simpa [symplectic, exponent] using h ((0, 0), (0, 1))
      · simpa [symplectic, exponent] using h ((0, 0), (1, 0))
  · rintro rfl w
    simp [symplectic, exponent]

@[simp] theorem word_zero : word 0 = 1 := by
  simp [word]

/-- The signed operator product follows from the two local products and native
Kronecker multiplication; no enumeration of the 256 matrix products is used. -/
theorem word_mul (v w : Label) :
    word v * word w = (signUnit (exponent v w) : ℝ) • word (v + w) := by
  unfold word
  rw [← Matrix.mul_kronecker_mul, localWord_mul, localWord_mul]
  simp only [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
    exponent, signUnit_add, Units.val_mul, Prod.fst_add, Prod.snd_add, mul_comm]

/-- Every word squares to a nonzero real scalar identity. -/
theorem word_sq (v : Label) :
    word v * word v = (signUnit (exponent v v) : ℝ) • (1 : Mat) := by
  rw [word_mul, label_add_self, word_zero]

theorem signUnit_val_mul_self (a : ZMod 2) :
    (signUnit a : ℝ) * (signUnit a : ℝ) = 1 := by
  have h := congrArg (fun u : ℝˣ => (u : ℝ)) (signUnit_add a a)
  simpa only [CharTwo.add_self_eq_zero, signUnit_zero, Units.val_one,
    Units.val_mul] using h.symm

/-- The inverse is constructed from the square law. -/
def wordUnit (v : Label) : Matˣ where
  val := word v
  inv := (signUnit (exponent v v) : ℝ) • word v
  val_inv := by
    rw [mul_smul_comm, word_sq, smul_smul, signUnit_val_mul_self, one_smul]
  inv_val := by
    rw [smul_mul_assoc, word_sq, smul_smul, signUnit_val_mul_self, one_smul]

theorem word_ne_zero (v : Label) : word v ≠ 0 := (wordUnit v).ne_zero

/-- Reversing operator order is controlled exactly by the binary symplectic form. -/
theorem word_mul_swap (v w : Label) :
    word v * word w = (signUnit (symplectic v w) : ℝ) • (word w * word v) := by
  rw [word_mul, word_mul, add_comm w v]
  simp only [symplectic, signUnit_add, Units.val_mul, smul_smul]
  rw [mul_assoc, signUnit_val_mul_self, mul_one]

/-- Scalar parity zero is equivalent to sign `+1`. -/
theorem signUnit_val_eq_one_iff (a : ZMod 2) :
    (signUnit a : ℝ) = 1 ↔ a = 0 := by
  rcases bit_cases a with rfl | rfl <;> norm_num [signUnit]

/-- This is the distinction between projective incidence and Lie commutation. -/
theorem word_commute_iff (v w : Label) :
    Commute (word v) (word w) ↔ symplectic v w = 0 := by
  constructor
  · intro h
    have hs : (signUnit (symplectic v w) : ℝ) • (word w * word v) =
        (1 : ℝ) • (word w * word v) := by
      rw [← word_mul_swap, one_smul]
      exact h.eq
    have hn : word w * word v ≠ 0 := ((wordUnit w) * (wordUnit v)).ne_zero
    exact (signUnit_val_eq_one_iff _).1 (smul_left_injective ℝ hn hs)
  · intro h
    change word v * word w = word w * word v
    simpa [h] using word_mul_swap v w

/-- The full commutator keeps both ordered coefficients. -/
theorem word_commutator (v w : Label) :
    word v * word w - word w * word v =
      ((signUnit (exponent v w) : ℝ) - (signUnit (exponent w v) : ℝ)) •
        word (v + w) := by
  rw [word_mul, word_mul, add_comm w v, sub_smul]

theorem word_commutator_eq_zero_iff (v w : Label) :
    word v * word w - word w * word v = 0 ↔ symplectic v w = 0 := by
  rw [sub_eq_zero]
  exact word_commute_iff v w

/-- On a nonisotropic pair the bracket is twice the ordered product. -/
theorem word_commutator_of_symplectic_one (v w : Label)
    (h : symplectic v w = 1) :
    word v * word w - word w * word v =
      (2 * (signUnit (exponent v w) : ℝ)) • word (v + w) := by
  have hs : word w * word v = -(word v * word w) := by
    simpa [symplectic_comm w v, h, signUnit] using word_mul_swap w v
  rw [hs, sub_neg_eq_add, ← two_smul ℝ (word v * word w), word_mul, smul_smul]

/-- A binary projective line has scalar ordered triple product, including its sign. -/
theorem word_line_product (v w : Label) :
    word v * word w * word (v + w) =
      (signUnit (exponent v w + exponent (v + w) (v + w)) : ℝ) • (1 : Mat) := by
  rw [word_mul, smul_mul_assoc, word_sq, smul_smul, signUnit_add, Units.val_mul]

/-- Both bracket outcomes occur in the concrete noncommutative matrix algebra. -/
theorem phase_shift_not_commute :
    ¬ Commute (word ((1, 0), (0, 0))) (word ((0, 1), (0, 0))) := by
  rw [word_commute_iff]
  norm_num [symplectic, exponent]

theorem different_factors_commute :
    Commute (word ((1, 0), (0, 0))) (word ((0, 0), (0, 1))) := by
  rw [word_commute_iff]
  norm_num [symplectic, exponent]

/-- Each nonidentity local word has zero trace. -/
theorem localWord_trace (v : LocalLabel) :
    Matrix.trace (localWord v) = if v = 0 then 2 else 0 := by
  rcases v with ⟨a, b⟩
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    norm_num [localWord, Eplus, Eminus, J1, Matrix.trace, Fin.sum_univ_two]

/-- The only word with nonzero trace is the identity word. -/
theorem word_trace (v : Label) :
    Matrix.trace (word v) = if v = 0 then 4 else 0 := by
  rcases v with ⟨a, b⟩
  simp only [word, Matrix.trace_kronecker, localWord_trace]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> norm_num [ha, hb]

/-- Real scalar multiplication cannot identify different binary operator labels. -/
theorem word_eq_smul_iff (v w : Label) (c : ℝ) :
    word v = c • word w ↔ v = w ∧ c = 1 := by
  constructor
  · intro h
    have hc : c ≠ 0 := by
      intro hc
      apply word_ne_zero v
      simpa [hc] using h
    have hvw : v = w := by
      by_contra hne
      have hsum : v + w ≠ 0 := by
        intro hz
        apply hne
        have h' := congrArg (fun x : Label => x + w) hz
        simpa only [add_assoc, label_add_self, add_zero, zero_add] using h'
      have ht := congrArg Matrix.trace (congrArg (fun A : Mat => A * word w) h)
      rw [word_mul, smul_mul_assoc, word_sq, Matrix.trace_smul,
        Matrix.trace_smul, Matrix.trace_smul, word_trace, ite_eq_right hsum,
        Matrix.trace_one] at ht
      have hs : (signUnit (exponent w w) : ℝ) ≠ 0 := (signUnit _).ne_zero
      norm_num [hc, hs] at ht
    refine ⟨hvw, ?_⟩
    subst v
    have he : (1 : ℝ) • word w = c • word w := by simpa using h
    exact (smul_left_injective ℝ (word_ne_zero w) he).symm
  · rintro ⟨rfl, rfl⟩
    simp

theorem word_injective : Function.Injective word := by
  intro v w h
  exact ((word_eq_smul_iff v w 1).1 (by simpa using h)).1

/-- A nonzero binary label never represents a scalar identity matrix. -/
theorem word_not_scalar_identity (v : Label) (hv : v ≠ 0) (c : ℝ) :
    word v ≠ c • (1 : Mat) := by
  intro h
  have h' : word v = c • word 0 := by simpa using h
  exact hv ((word_eq_smul_iff v 0 c).1 h').1

end InfoGeometry.Clifford.BinaryPauli
