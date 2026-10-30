/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Module.Defs

/-!
# Peirce operator spine: vocabulary and the corner normal form

Throughout, `B` is an arbitrary (non-commutative) ring and `P : B` an idempotent.
The two Peirce corners

* `conePlus P A = P A (1 - P)`  (written `N₊`),
* `coneMinus P C = (1 - P) C P` (written `N₋`)

generate the odd elements `Φ = N₊ + N₋`, `J = N₊ - N₋` and the even elements
`V = N₊ N₋ + N₋ N₊`, `Σ = N₊ N₋ - N₋ N₊`. The grading is `S = P - (1 - P)`.

## Normal form

All identities of the spine are identities in the path algebra of the two-vertex
quiver. Writing products right-associated, the rewriting rules

`P P → P`, `P N₊ → N₊`, `N₊ P → 0`, `N₋ P → N₋`, `P N₋ → 0`, `N₊ N₊' → 0`, `N₋ N₋' → 0`

(each also in the form `x (y z) → (x y) z`-reduced) are confluent, so a
`simp only` pass with these rules followed by `abel` decides the identities
used below. The rules are packaged as the tactic `peirce_nf hP`. The corners
are kept opaque; they are linear in their argument (`conePlus_add`, …).
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-! ### Vocabulary -/

/-- Commutator. -/
def comm (X Y : B) : B := X * Y - Y * X
/-- Anticommutator. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- The grading `S = P - (1 - P)`. -/
def invS (P : B) : B := P - (1 - P)
/-- The upper corner `N₊ = P A (1 - P)`. -/
def conePlus (P A : B) : B := P * A * (1 - P)
/-- The lower corner `N₋ = (1 - P) C P`. -/
def coneMinus (P C : B) : B := (1 - P) * C * P

def peirce11 (P X : B) : B := P * X * P
def peirce00 (P X : B) : B := (1 - P) * X * (1 - P)
def evenGrade (P X : B) : B := P * X * P + (1 - P) * X * (1 - P)
def oddGrade (P X : B) : B := P * X * (1 - P) + (1 - P) * X * P

/-- `Φ = N₊ + N₋`. -/
def genPhi (P A C : B) : B := conePlus P A + coneMinus P C
/-- `J = N₊ - N₋`. -/
def genJ (P A C : B) : B := conePlus P A - coneMinus P C
/-- The Jordan mass `V = {N₊, N₋}`. -/
def genV (P A C : B) : B := anticomm (conePlus P A) (coneMinus P C)
/-- The spin `Σ = [N₊, N₋]`. -/
def genSig (P A C : B) : B := comm (conePlus P A) (coneMinus P C)

/-! ### Corner relations -/

section Relations

variable {P : B} (hP : P * P = P)
include hP

theorem P_mul_P' (z : B) : P * (P * z) = P * z := by rw [← mul_assoc, hP]

theorem P_mul_conePlus (A : B) : P * conePlus P A = conePlus P A := by
  simp only [conePlus, ← mul_assoc, hP]

theorem P_mul_conePlus' (A z : B) : P * (conePlus P A * z) = conePlus P A * z := by
  rw [← mul_assoc, P_mul_conePlus hP]

theorem conePlus_mul_P (A : B) : conePlus P A * P = 0 := by
  simp only [conePlus, mul_assoc, sub_mul, one_mul, hP, sub_self, mul_zero]

theorem conePlus_mul_P' (A z : B) : conePlus P A * (P * z) = 0 := by
  rw [← mul_assoc, conePlus_mul_P hP, zero_mul]

theorem coneMinus_mul_P (C : B) : coneMinus P C * P = coneMinus P C := by
  simp only [coneMinus, mul_assoc, hP]

theorem coneMinus_mul_P' (C z : B) : coneMinus P C * (P * z) = coneMinus P C * z := by
  rw [← mul_assoc, coneMinus_mul_P hP]

theorem P_mul_coneMinus (C : B) : P * coneMinus P C = 0 := by
  simp only [coneMinus, ← mul_assoc, mul_sub, mul_one, hP, sub_self, zero_mul]

theorem P_mul_coneMinus' (C z : B) : P * (coneMinus P C * z) = 0 := by
  rw [← mul_assoc, P_mul_coneMinus hP, zero_mul]

/-- Two upper-corner elements multiply to zero. -/
theorem conePlus_mul_conePlus (A A' : B) : conePlus P A * conePlus P A' = 0 := by
  rw [← P_mul_conePlus hP A', ← mul_assoc, conePlus_mul_P hP, zero_mul]

theorem conePlus_mul_conePlus' (A A' z : B) :
    conePlus P A * (conePlus P A' * z) = 0 := by
  rw [← mul_assoc, conePlus_mul_conePlus hP, zero_mul]

/-- Two lower-corner elements multiply to zero. -/
theorem coneMinus_mul_coneMinus (C C' : B) : coneMinus P C * coneMinus P C' = 0 := by
  rw [← coneMinus_mul_P hP C, mul_assoc, P_mul_coneMinus hP, mul_zero]

theorem coneMinus_mul_coneMinus' (C C' z : B) :
    coneMinus P C * (coneMinus P C' * z) = 0 := by
  rw [← mul_assoc, coneMinus_mul_coneMinus hP, zero_mul]

end Relations

/-! ### Linearity of the corners -/

section Linearity

variable (P : B)

theorem conePlus_add (A A' : B) : conePlus P (A + A') = conePlus P A + conePlus P A' := by
  simp only [conePlus, mul_add, add_mul]

theorem conePlus_sub (A A' : B) : conePlus P (A - A') = conePlus P A - conePlus P A' := by
  simp only [conePlus]; noncomm_ring

theorem conePlus_neg (A : B) : conePlus P (-A) = -conePlus P A := by
  simp only [conePlus, mul_neg, neg_mul]

theorem conePlus_zero : conePlus P (0 : B) = 0 := by simp only [conePlus, mul_zero, zero_mul]

theorem coneMinus_add (C C' : B) : coneMinus P (C + C') = coneMinus P C + coneMinus P C' := by
  simp only [coneMinus, mul_add, add_mul]

theorem coneMinus_sub (C C' : B) : coneMinus P (C - C') = coneMinus P C - coneMinus P C' := by
  simp only [coneMinus]; noncomm_ring

theorem coneMinus_neg (C : B) : coneMinus P (-C) = -coneMinus P C := by
  simp only [coneMinus, mul_neg, neg_mul]

theorem coneMinus_zero : coneMinus P (0 : B) = 0 := by
  simp only [coneMinus, mul_zero, zero_mul]

end Linearity

/-- Base rewriting set of the corner normal form. Callers add the definitions
they want unfolded. -/
macro "peirce_nf" hP:ident : tactic =>
  `(tactic| (
    simp only [invS, comm, anticomm, genPhi, genJ, genV, genSig,
      peirce11, peirce00, evenGrade, oddGrade,
      conePlus_add, conePlus_sub, conePlus_neg, conePlus_zero,
      coneMinus_add, coneMinus_sub, coneMinus_neg, coneMinus_zero,
      mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, neg_neg, neg_sub,
      one_mul, mul_one, zero_mul, mul_zero, mul_assoc,
      smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg, smul_smul, smul_zero,
      $hP:ident, P_mul_P' $hP:ident,
      P_mul_conePlus $hP:ident, P_mul_conePlus' $hP:ident,
      conePlus_mul_P $hP:ident, conePlus_mul_P' $hP:ident,
      coneMinus_mul_P $hP:ident, coneMinus_mul_P' $hP:ident,
      P_mul_coneMinus $hP:ident, P_mul_coneMinus' $hP:ident,
      conePlus_mul_conePlus $hP:ident, conePlus_mul_conePlus' $hP:ident,
      coneMinus_mul_coneMinus $hP:ident, coneMinus_mul_coneMinus' $hP:ident]
    <;> abel))

end InfoGeometry.OperatorAlgebra.PeirceSpine
