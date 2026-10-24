/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Group.Units.Basic

/-!
# Opposite square-zero shears over arbitrary rings

The four explicit hypotheses are square-zero and reflexive inverse equations.
No star, scalar algebra, characteristic or nondegeneracy hypothesis is hidden.
Power equations are not assertions of exact orders. The common square/cube
commutes with the generators, but need not be central in the ambient ring.
-/
namespace InfoGeometry.Core.ParabolicShearRelations

variable {A : Type*} [Ring A]

/-- The elementary shear is an actual ambient unit. -/
def shearUnit (x : A) (hx : x * x = 0) : Aˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := by noncomm_ring [hx]
  inv_val := by noncomm_ring [hx]

/-- Natural powers of an elementary shear are linear in the parameter. -/
theorem shear_pow (x : A) (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, succ_nsmul]
    noncomm_ring [hx]

/-- The ordered double product. -/
def doubleShear (d b : A) : A := (1 + d) * (1 - b)

/-- Inverses reverse the order of the shear factors. -/
def doubleShearInv (d b : A) : A := (1 + b) * (1 - d)

/-- The ordered triple product; its value agrees with the existing Weyl owner. -/
def tripleShear (d b : A) : A := doubleShear d b * (1 + d)

/-- The common sign element acts by minus one on the active corner. -/
def supportSign (d b : A) : A := 1 - (d * b + b * d) - (d * b + b * d)

theorem double_inverse {d b : A} (hd : d * d = 0) (hb : b * b = 0) :
    doubleShear d b * doubleShearInv d b = 1 ∧
    doubleShearInv d b * doubleShear d b = 1 := by
  have dd (x : A) : d * (d * x) = 0 := by rw [← mul_assoc, hd, zero_mul]
  have bb (x : A) : b * (b * x) = 0 := by rw [← mul_assoc, hb, zero_mul]
  constructor <;> unfold doubleShear doubleShearInv <;> noncomm_ring [hd, hb, dd, bb]

/-- The inverse-sum is algebraic and needs no reflexive-pair assumptions. -/
theorem double_inverse_sum (d b : A) :
    doubleShear d b + doubleShearInv d b =
      2 • (1 - (d * b + b * d)) + (d * b + b * d) := by
  unfold doubleShear doubleShearInv
  noncomm_ring

/-- The triple is the harmonic completion of the skew arrow. -/
theorem triple_expansion {d b : A} (hd : d * d = 0) (hdb : d * b * d = d) :
    tripleShear d b = 1 - (d * b + b * d) + (d - b) := by
  unfold tripleShear doubleShear
  have hdb' : d * (b * d) = d := by simpa only [mul_assoc] using hdb
  noncomm_ring [hd, hdb']

/-- Both orders of the unipotent triple give the same element. -/
theorem shear_braid {d b : A} (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) :
    (1 + d) * (1 - b) * (1 + d) = (1 - b) * (1 + d) * (1 - b) := by
  have hdb' : d * (b * d) = d := by simpa only [mul_assoc] using hdb
  have hbd' : b * (d * b) = b := by simpa only [mul_assoc] using hbd
  noncomm_ring [hd, hb, hdb', hbd']

/-- The ambient Phi-six defect is exactly the harmonic idempotent. -/
theorem double_quadratic_defect {d b : A}
    (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) :
    doubleShear d b * doubleShear d b - doubleShear d b + 1 =
      1 - (d * b + b * d) := by
  have dd (x : A) : d * (d * x) = 0 := by rw [← mul_assoc, hd, zero_mul]
  have bb (x : A) : b * (b * x) = 0 := by rw [← mul_assoc, hb, zero_mul]
  have dbd (x : A) : d * (b * (d * x)) = d * x := by
    simpa only [mul_assoc] using congrArg (fun y : A => y * x) hdb
  have hdb' : d * (b * d) = d := by simpa only [mul_assoc] using hdb
  have hbd' : b * (d * b) = b := by simpa only [mul_assoc] using hbd
  unfold doubleShear
  noncomm_ring [hd, hb, dd, bb, dbd, hdb', hbd']

/-- The double product acts as the identity on the harmonic complement. -/
theorem double_harmonic {d b : A}
    (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) :
    doubleShear d b * (1 - (d * b + b * d)) = 1 - (d * b + b * d) := by
  have dd (x : A) : d * (d * x) = 0 := by rw [← mul_assoc, hd, zero_mul]
  have bb (x : A) : b * (b * x) = 0 := by rw [← mul_assoc, hb, zero_mul]
  have dbd (x : A) : d * (b * (d * x)) = d * x := by
    simpa only [mul_assoc] using congrArg (fun y : A => y * x) hdb
  have hdb' : d * (b * d) = d := by simpa only [mul_assoc] using hdb
  have hbd' : b * (d * b) = b := by simpa only [mul_assoc] using hbd
  unfold doubleShear
  noncomm_ring [hd, hb, dd, bb, dbd, hdb', hbd']

/-- The cube of the double product is the common sign element. -/
theorem double_cube {d b : A}
    (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) :
    doubleShear d b ^ 3 = supportSign d b := by
  have hq := double_quadratic_defect hd hb hdb hbd
  have hh := double_harmonic hd hb hdb hbd
  calc
    doubleShear d b ^ 3 =
      doubleShear d b * (doubleShear d b * doubleShear d b - doubleShear d b + 1) +
        (doubleShear d b * doubleShear d b - doubleShear d b + 1) - 1 := by noncomm_ring
    _ = supportSign d b := by rw [hq, hh]; unfold supportSign; abel

/-- Universal shared square/cube, independent of a star operation. -/
theorem triple_square {d b : A}
    (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) :
    tripleShear d b ^ 2 = supportSign d b := by
  rw [triple_expansion hd hdb]
  have dd (x : A) : d * (d * x) = 0 := by rw [← mul_assoc, hd, zero_mul]
  have bb (x : A) : b * (b * x) = 0 := by rw [← mul_assoc, hb, zero_mul]
  have dbd (x : A) : d * (b * (d * x)) = d * x := by
    simpa only [mul_assoc] using congrArg (fun y : A => y * x) hdb
  have bdb (x : A) : b * (d * (b * x)) = b * x := by
    simpa only [mul_assoc] using congrArg (fun y : A => y * x) hbd
  have hdb' : d * (b * d) = d := by simpa only [mul_assoc] using hdb
  have hbd' : b * (d * b) = b := by simpa only [mul_assoc] using hbd
  unfold supportSign
  noncomm_ring [hd, hb, dd, bb, dbd, bdb, hdb', hbd']

/-- The sign squares to one; this does not assert ambient centrality. -/
theorem supportSign_square {d b : A}
    (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) :
    supportSign d b * supportSign d b = 1 := by
  have dd (x : A) : d * (d * x) = 0 := by rw [← mul_assoc, hd, zero_mul]
  have bb (x : A) : b * (b * x) = 0 := by rw [← mul_assoc, hb, zero_mul]
  have dbd (x : A) : d * (b * (d * x)) = d * x := by
    simpa only [mul_assoc] using congrArg (fun y : A => y * x) hdb
  have bdb (x : A) : b * (d * (b * x)) = b * x := by
    simpa only [mul_assoc] using congrArg (fun y : A => y * x) hbd
  unfold supportSign
  noncomm_ring [hd, hb, dd, bb, dbd, bdb]

/-- The finite-power relations, without any exact-order assertion. -/
theorem power_relations {d b : A}
    (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) :
    tripleShear d b ^ 4 = 1 ∧ doubleShear d b ^ 6 = 1 ∧
      (doubleShear d b ^ 2) ^ 3 = 1 := by
  have hz := supportSign_square hd hb hdb hbd
  have hs : tripleShear d b ^ 4 = 1 := by
    calc _ = (tripleShear d b ^ 2) * (tripleShear d b ^ 2) := by noncomm_ring
         _ = 1 := by rw [triple_square hd hb hdb hbd]; exact hz
  have hu : doubleShear d b ^ 6 = 1 := by
    calc _ = (doubleShear d b ^ 3) * (doubleShear d b ^ 3) := by noncomm_ring
         _ = 1 := by rw [double_cube hd hb hdb hbd]; exact hz
  refine ⟨hs, hu, ?_⟩
  rw [← pow_mul]
  exact hu

end InfoGeometry.Core.ParabolicShearRelations
