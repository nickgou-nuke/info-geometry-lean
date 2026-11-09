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

theorem evenGrade_add (P X Y : B) :
    evenGrade P (X + Y) = evenGrade P X + evenGrade P Y := by
  calc
    evenGrade P (X + Y) = P * (X + Y) * P + (1 - P) * (X + Y) * (1 - P) := rfl
    _ = (P * X * P + P * Y * P) + ((1 - P) * X * (1 - P) + (1 - P) * Y * (1 - P)) := by
      simp [add_mul, mul_add]
    _ = evenGrade P X + evenGrade P Y := by
      simp only [evenGrade]
      abel

theorem oddGrade_add (P X Y : B) :
    oddGrade P (X + Y) = oddGrade P X + oddGrade P Y := by
  calc
    oddGrade P (X + Y) = P * (X + Y) * (1 - P) + (1 - P) * (X + Y) * P := rfl
    _ = (P * X * (1 - P) + P * Y * (1 - P)) + ((1 - P) * X * P + (1 - P) * Y * P) := by
      simp [add_mul, mul_add]
    _ = oddGrade P X + oddGrade P Y := by
      simp only [oddGrade]
      abel

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

section GradedMultiplication

variable {P : B} (hP : P * P = P)
include hP

/-- The even component of a product is the sum of the even-even and
odd-odd products. This is the multiplication law for the Peirce
`ℤ/2`-grading, in an arbitrary associative ring. -/
theorem evenGrade_mul (X Y : B) :
    evenGrade P (X * Y) =
      evenGrade P X * evenGrade P Y + oddGrade P X * oddGrade P Y := by
  peirce_nf hP

/-- The odd component of a product is the sum of its even-odd and
odd-even products. -/
theorem oddGrade_mul (X Y : B) :
    oddGrade P (X * Y) =
      evenGrade P X * oddGrade P Y + oddGrade P X * evenGrade P Y := by
  peirce_nf hP

/-- The two Peirce components are complementary projections: each is
idempotent, and applying either projection to the other component gives zero. -/
theorem grade_projection_laws (X : B) :
    evenGrade P (evenGrade P X) = evenGrade P X ∧
    evenGrade P (oddGrade P X) = 0 ∧
    oddGrade P (evenGrade P X) = 0 ∧
    oddGrade P (oddGrade P X) = oddGrade P X ∧
    evenGrade P X + oddGrade P X = X := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- A projection commutator has no diagonal compression, and its second
commutator is exactly the off-diagonal Peirce component. These are the
projection-geometric identities used by the matrix source packet, stated for
an arbitrary associative ring and without a star or matrix assumption. -/
theorem projection_commutator_geometry (X : B) :
    P * comm P X * P = 0 ∧
    comm P (comm P X) = P * X * (1 - P) + (1 - P) * X * P ∧
    comm P (comm P X) = P * X + X * P - (2 : ℤ) • (P * X * P) := by
  have hleft : P * (P * X) = P * X := by
    rw [← mul_assoc, hP]
  have hright : (X * P) * P = X * P := by
    rw [mul_assoc, hP]
  have hcomm : comm P (comm P X) =
      P * X - P * X * P - (P * X * P - X * P) := by
    unfold comm
    calc
      P * (P * X - X * P) - (P * X - X * P) * P =
          P * (P * X) - P * (X * P) - ((P * X) * P - (X * P) * P) := by
            noncomm_ring
      _ = P * X - P * X * P - (P * X * P - X * P) := by
            rw [hleft, hright]
            noncomm_ring
  have hcompress : P * comm P X * P = 0 := by
    unfold comm
    have h₁ : P * (P * X) * P = P * X * P := by rw [hleft]
    have h₂ : P * (X * P) * P = P * X * P := by
      calc
        P * (X * P) * P = P * X * (P * P) := by noncomm_ring
        _ = P * X * P := by rw [hP]
    calc
      P * (P * X - X * P) * P =
          P * (P * X) * P - P * (X * P) * P := by noncomm_ring
      _ = 0 := by rw [h₁, h₂, sub_self]
  refine ⟨hcompress, ?_, ?_⟩
  · rw [hcomm]
    noncomm_ring
  · rw [hcomm, two_zsmul]
    noncomm_ring

/-- A cut can fail to reproduce the whole input even when its double
commutator vanishes: the complementary diagonal corner `1 - P` is discarded
by compression but commutes with `P`. Thus `P * X * P ≠ X` is not equivalent
to a nonzero Peirce boundary (the double commutator). -/
theorem complementary_corner_disproves_compression_aporia_equivalence
    (hP_ne_one : P ≠ 1) :
    P * (1 - P) * P ≠ 1 - P ∧
      comm P (comm P (1 - P)) = 0 := by
  have hPcomp : P * (1 - P) = 0 := by
    calc
      P * (1 - P) = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP]; noncomm_ring
  have hcompP : (1 - P) * P = 0 := by
    calc
      (1 - P) * P = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP]; noncomm_ring
  have hcomm : comm P (1 - P) = 0 := by
    unfold comm
    rw [hPcomp, hcompP]
    simp
  constructor
  · intro h
    have hzero : P * (1 - P) * P = 0 := by rw [hPcomp]; simp
    rw [hzero] at h
    apply hP_ne_one
    exact (sub_eq_zero.mp h.symm).symm
  · rw [hcomm]
    simp [comm]

/-- The idempotency defect `X² - X` splits by Peirce parity. Its even part is
the sum of the even-even and odd-odd products, less the even part of `X`; its
odd part is the mixed product sum, less the odd part of `X`. -/
theorem idempotency_defect_peirce_grade_decomposition (X : B) :
    evenGrade P (X * X - X) =
      evenGrade P X * evenGrade P X + oddGrade P X * oddGrade P X - evenGrade P X ∧
    oddGrade P (X * X - X) =
      evenGrade P X * oddGrade P X + oddGrade P X * evenGrade P X - oddGrade P X := by
  have hEvenSub : evenGrade P (X * X - X) = evenGrade P (X * X) - evenGrade P X := by
    unfold evenGrade
    noncomm_ring
  have hOddSub : oddGrade P (X * X - X) = oddGrade P (X * X) - oddGrade P X := by
    unfold oddGrade
    noncomm_ring
  constructor
  · rw [hEvenSub, evenGrade_mul hP]
  · rw [hOddSub, oddGrade_mul hP]

/-- Squaring a sum of a Peirce-even element `D` and a Peirce-odd element `O`
separates into an even diagonal term and an odd mixed term. The four support
equalities state exactly which Peirce summands `D` and `O` occupy. -/
theorem even_odd_sum_square (D O : B)
    (hDe : evenGrade P D = D) (hDo : oddGrade P D = 0)
    (hOe : evenGrade P O = 0) (hOo : oddGrade P O = O) :
    evenGrade P ((D + O) * (D + O)) = D * D + O * O ∧
    oddGrade P ((D + O) * (D + O)) = D * O + O * D := by
  have hEven : evenGrade P (D + O) = D := by
    rw [evenGrade_add, hDe, hOe]
    simp
  have hOdd : oddGrade P (D + O) = O := by
    rw [oddGrade_add, hDo, hOo]
    simp
  rw [evenGrade_mul hP, oddGrade_mul hP, hEven, hOdd]
  exact ⟨rfl, rfl⟩

end GradedMultiplication

end InfoGeometry.OperatorAlgebra.PeirceSpine
