/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanBoundaryComposition

/-! # Signed two-sided transport and the completed composition octet

All maps act on the full associative algebra. The symmetric map is the
existing `crossTransport`; its signed companion is not declared positive.
Multiplication of endomorphisms means composition, with the right map first.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- The difference of the two ordered sandwiches, without positivity claims. -/
def skewTransport (a b : A) : Module.End R A :=
  sandwichOp R a b - sandwichOp R b a

@[simp] theorem skewTransport_apply (a b x : A) :
    skewTransport R a b x = a * x * b - b * x * a := rfl

theorem skewTransport_one (a b : A) :
    skewTransport R a b 1 = a * b - b * a := by simp

theorem skewTransport_swap (a b : A) :
    skewTransport R b a = -skewTransport R a b := by
  unfold skewTransport
  abel

/-- The eighth row: reversing Lie/Jordan order reverses the sandwich defect. -/
theorem jordan_lie_mixed_difference (a b : A) :
    jordanOp R a * lieOp R b - jordanOp R b * lieOp R a =
      jordanOp R (a * b - b * a) - (2 : ℕ) • skewTransport R a b := by
  rw [two_nsmul]
  ext x
  change a * (b * x - x * b) + (b * x - x * b) * a -
    (b * (a * x - x * a) + (a * x - x * a) * b) =
    ((a * b - b * a) * x + x * (a * b - b * a)) -
    ((a * x * b - b * x * a) + (a * x * b - b * x * a))
  noncomm_ring

/-- The two mixed differences recover Jordan multiplication without division. -/
theorem mixed_difference_total (a b : A) :
    (lieOp R a * jordanOp R b - lieOp R b * jordanOp R a) +
      (jordanOp R a * lieOp R b - jordanOp R b * lieOp R a) =
        (2 : ℕ) • jordanOp R (a * b - b * a) := by
  rw [mixed_difference_defect, jordan_lie_mixed_difference]
  unfold skewTransport
  abel

/-- Subtracting the two mixed differences extracts the signed transport. -/
theorem mixed_difference_separation (a b : A) :
    (lieOp R a * jordanOp R b - lieOp R b * jordanOp R a) -
      (jordanOp R a * lieOp R b - jordanOp R b * lieOp R a) =
        (4 : ℕ) • skewTransport R a b := by
  rw [mixed_difference_defect, jordan_lie_mixed_difference]
  unfold skewTransport
  abel

/-- The complete eight identities, reusing the seven already-owned rows. -/
theorem composition_octet (a b : A) :
    jordanOp R a * lieOp R b + jordanOp R b * lieOp R a = lieOp R (a*b+b*a) ∧
    lieOp R a * jordanOp R b + lieOp R b * jordanOp R a = lieOp R (a*b+b*a) ∧
    lieOp R a * lieOp R b - lieOp R b * lieOp R a = lieOp R (a*b-b*a) ∧
    jordanOp R a * jordanOp R b - jordanOp R b * jordanOp R a = lieOp R (a*b-b*a) ∧
    jordanOp R a * jordanOp R b + jordanOp R b * jordanOp R a =
      jordanOp R (a*b+b*a) + (2 : ℕ) • crossTransport R a b ∧
    lieOp R a * lieOp R b + lieOp R b * lieOp R a =
      jordanOp R (a*b+b*a) - (2 : ℕ) • crossTransport R a b ∧
    lieOp R a * jordanOp R b - lieOp R b * jordanOp R a =
      jordanOp R (a*b-b*a) + (2 : ℕ) • skewTransport R a b ∧
    jordanOp R a * lieOp R b - jordanOp R b * lieOp R a =
      jordanOp R (a*b-b*a) - (2 : ℕ) • skewTransport R a b :=
  ⟨jordan_lie_mixed_sum R a b, lie_jordan_mixed_sum R a b,
    lie_lie R a b, jordan_jordan R a b, jordan_pair_sum R a b,
    lie_pair_sum R a b, mixed_difference_defect R a b,
    jordan_lie_mixed_difference R a b⟩

/-- Both sandwiches are transported; no commutation of their generators is used. -/
theorem skewTransport_natural {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (a b : A) :
    f.toLinearMap.comp (skewTransport R a b) =
      (skewTransport R (f a) (f b)).comp f.toLinearMap := by
  ext x
  change f (a*x*b-b*x*a) = f a*f x*f b-f b*f x*f a
  simp only [map_sub, map_mul]

section SquareZero
variable {a b : A}

private theorem squareZero_nested (a : A) (ha : a*a=0) (x : A) :
    a*(a*x)=0 := by rw [← mul_assoc, ha, zero_mul]

/-- Iterating the symmetric transfer gives two same-corner sandwiches. -/
theorem crossTransport_square (ha : a*a=0) (hb : b*b=0) :
    crossTransport R a b * crossTransport R a b =
      sandwichOp R (a*b) (a*b) + sandwichOp R (b*a) (b*a) := by
  ext x
  change a*(a*x*b+b*x*a)*b+b*(a*x*b+b*x*a)*a =
    (a*b)*x*(a*b)+(b*a)*x*(b*a)
  noncomm_ring [ha, hb, squareZero_nested a ha, squareZero_nested b hb]

/-- The signed transfer has the opposite square, on the full operator algebra. -/
theorem skewTransport_square (ha : a*a=0) (hb : b*b=0) :
    skewTransport R a b * skewTransport R a b =
      -(crossTransport R a b * crossTransport R a b) := by
  rw [crossTransport_square R ha hb]
  ext x
  change a*(a*x*b-b*x*a)*b-b*(a*x*b-b*x*a)*a =
    -((a*b)*x*(a*b)+(b*a)*x*(b*a))
  noncomm_ring [ha, hb, squareZero_nested a ha, squareZero_nested b hb]

/-- The symmetric and signed transfers anticommute as endomorphisms. -/
theorem cross_skew_anticommute (ha : a*a=0) (hb : b*b=0) :
    crossTransport R a b * skewTransport R a b +
      skewTransport R a b * crossTransport R a b = 0 := by
  ext x
  change (a*(a*x*b-b*x*a)*b+b*(a*x*b-b*x*a)*a) +
    (a*(a*x*b+b*x*a)*b-b*(a*x*b+b*x*a)*a) = 0
  noncomm_ring [ha, hb, squareZero_nested a ha, squareZero_nested b hb]

end SquareZero
end InfoGeometry.OperatorAlgebra.LieJordan
