/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Algebra.PeirceLieJordanResolution
import InfoGeometry.OperatorAlgebra.LieJordanOctet

/-!
# Peirce support and grading of the two sandwich actions

The idempotent may be oblique and the two corner coefficients are independent.
The reflection below is the existing expression `p - compIdempotent p`.
Output grading interchanges the symmetric and signed actions; input grading
has the opposite sign. Both actions discard the off-diagonal input corners.
No self-adjointness, positivity, diagonal representation, or time flow is used.
-/

namespace InfoGeometry.Algebra.PeirceSandwichDuality

open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Output grading changes the symmetric action to the signed action. -/
theorem reflection_cross_left {p : A} (hp : p * p = p) (a b x : A) :
    (p - compIdempotent p) * (crossTransport (R := R) (peirce10 p a) (peirce01 p b) x) =
      orientedTransport (R := R) (peirce10 p a) (peirce01 p b) x := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- Output grading changes the signed action back to the symmetric action. -/
theorem reflection_oriented_left {p : A} (hp : p * p = p) (a b x : A) :
    (p - compIdempotent p) * (orientedTransport (R := R) (peirce10 p a) (peirce01 p b) x) =
      crossTransport (R := R) (peirce10 p a) (peirce01 p b) x := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The same output action holds by right multiplication. -/
theorem reflection_cross_right {p : A} (hp : p * p = p) (a b x : A) :
    (crossTransport (R := R) (peirce10 p a) (peirce01 p b) x) * (p - compIdempotent p) =
      orientedTransport (R := R) (peirce10 p a) (peirce01 p b) x := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- Right output grading also interchanges the actions. -/
theorem reflection_oriented_right {p : A} (hp : p * p = p) (a b x : A) :
    (orientedTransport (R := R) (peirce10 p a) (peirce01 p b) x) * (p - compIdempotent p) =
      crossTransport (R := R) (peirce10 p a) (peirce01 p b) x := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- Input grading has the opposite sign: it grades the source corner. -/
theorem cross_reflection_input {p : A} (hp : p * p = p) (a b x : A) :
    crossTransport (R := R) (peirce10 p a) (peirce01 p b) ((p - compIdempotent p) * x) =
      -(orientedTransport (R := R) (peirce10 p a) (peirce01 p b) x) := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The signed action also reverses the input grading sign. -/
theorem oriented_reflection_input {p : A} (hp : p * p = p) (a b x : A) :
    orientedTransport (R := R) (peirce10 p a) (peirce01 p b) ((p - compIdempotent p) * x) =
      -(crossTransport (R := R) (peirce10 p a) (peirce01 p b) x) := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- Only the two even input corners contribute. -/
theorem cross_reads_even {p : A} (hp : p * p = p) (a b x : A) :
    crossTransport (R := R) (peirce10 p a) (peirce01 p b) (peirce11 p x + peirce00 p x) =
      crossTransport (R := R) (peirce10 p a) (peirce01 p b) x := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The same input support holds for the signed action. -/
theorem oriented_reads_even {p : A} (hp : p * p = p) (a b x : A) :
    orientedTransport (R := R) (peirce10 p a) (peirce01 p b) (peirce11 p x + peirce00 p x) =
      orientedTransport (R := R) (peirce10 p a) (peirce01 p b) x := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The upper off-diagonal input corner is annihilated. -/
theorem cross_kills_upper {p : A} (hp : p * p = p) (a b x : A) :
    crossTransport (R := R) (peirce10 p a) (peirce01 p b) (peirce10 p x) = 0 := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The lower off-diagonal input corner is annihilated. -/
theorem cross_kills_lower {p : A} (hp : p * p = p) (a b x : A) :
    crossTransport (R := R) (peirce10 p a) (peirce01 p b) (peirce01 p x) = 0 := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The signed action annihilates the upper input corner. -/
theorem oriented_kills_upper {p : A} (hp : p * p = p) (a b x : A) :
    orientedTransport (R := R) (peirce10 p a) (peirce01 p b) (peirce10 p x) = 0 := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The signed action annihilates the lower input corner. -/
theorem oriented_kills_lower {p : A} (hp : p * p = p) (a b x : A) :
    orientedTransport (R := R) (peirce10 p a) (peirce01 p b) (peirce01 p x) = 0 := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The positive output corner is the first ordered sandwich. -/
theorem cross_corner11 {p : A} (hp : p * p = p) (a b x : A) :
    peirce11 p (crossTransport (R := R) (peirce10 p a) (peirce01 p b) x) =
      peirce10 p a * x * peirce01 p b := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The complementary output corner is the reverse ordered sandwich. -/
theorem cross_corner00 {p : A} (hp : p * p = p) (a b x : A) :
    peirce00 p (crossTransport (R := R) (peirce10 p a) (peirce01 p b) x) =
      peirce01 p b * x * peirce10 p a := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The positive signed-output corner has unchanged sign. -/
theorem oriented_corner11 {p : A} (hp : p * p = p) (a b x : A) :
    peirce11 p (orientedTransport (R := R) (peirce10 p a) (peirce01 p b) x) =
      peirce10 p a * x * peirce01 p b := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The complementary signed-output corner has the negative sign. -/
theorem oriented_corner00 {p : A} (hp : p * p = p) (a b x : A) :
    peirce00 p (orientedTransport (R := R) (peirce10 p a) (peirce01 p b) x) =
      -(peirce01 p b * x * peirce10 p a) := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The full output is even, without commuting the input with the idempotent. -/
theorem cross_commutes_projector {p : A} (hp : p * p = p) (a b x : A) :
    p * (crossTransport (R := R) (peirce10 p a) (peirce01 p b) x) =
      (crossTransport (R := R) (peirce10 p a) (peirce01 p b) x) * p := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

/-- The signed output is also even. -/
theorem oriented_commutes_projector {p : A} (hp : p * p = p) (a b x : A) :
    p * (orientedTransport (R := R) (peirce10 p a) (peirce01 p b) x) =
      (orientedTransport (R := R) (peirce10 p a) (peirce01 p b) x) * p := by
  have hl (z : A) : p * (p * z) = p * z := by
    rw [← mul_assoc, hp]
  simp only [crossTransport_apply, orientedTransport_apply,
    peirce11, peirce00, peirce10, peirce01, compIdempotent,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    one_mul, mul_one, mul_assoc, hp, hl] <;> abel

end InfoGeometry.Algebra.PeirceSandwichDuality
