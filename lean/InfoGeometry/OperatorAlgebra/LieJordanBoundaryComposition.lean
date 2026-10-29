/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms

/-! # Exact boundary compositions on the full associative algebra

Multiplication is composition in `Module.End R A`. In particular no two
matrix generators are assumed to commute. The mixed difference retains its
sandwich defect; neither an ordinary Jordan action nor an ordinary inner
derivation is asserted square-zero merely because its generator is.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- Ordered two-sided multiplication, as a native endomorphism. -/
def sandwichOp (a b : A) : Module.End R A :=
  (LinearMap.mulRight R b).comp (LinearMap.mulLeft R a)

/-- Symmetric two-sided transport; no positivity or normalization is implicit. -/
def crossTransport (a b : A) : Module.End R A :=
  sandwichOp R a b + sandwichOp R b a

@[simp] theorem sandwichOp_apply (a b x : A) :
    sandwichOp R a b x = a * x * b := rfl

@[simp] theorem crossTransport_apply (a b x : A) :
    crossTransport R a b x = a * x * b + b * x * a := rfl

/-- Squaring the ordinary commutator retains a negative sandwich term. -/
theorem lie_square_defect (q : A) :
    lieOp R q * lieOp R q =
      jordanOp R (q * q) - (2 : ℕ) • sandwichOp R q q := by
  rw [two_nsmul]
  ext x
  change q * (q * x - x * q) - (q * x - x * q) * q =
    ((q * q) * x + x * (q * q)) - (q * x * q + q * x * q)
  noncomm_ring

/-- Squaring the ordinary anticommutator retains the opposite defect. -/
theorem jordan_square_defect (q : A) :
    jordanOp R q * jordanOp R q =
      jordanOp R (q * q) + (2 : ℕ) • sandwichOp R q q := by
  rw [two_nsmul]
  ext x
  change q * (q * x + x * q) + (q * x + x * q) * q =
    ((q * q) * x + x * (q * q)) + (q * x * q + q * x * q)
  noncomm_ring

/-- Alternating the two actions, rather than squaring either one, cancels. -/
theorem lie_jordan_same (q : A) :
    lieOp R q * jordanOp R q = lieOp R (q * q) := by
  ext x
  change q * (q * x + x * q) - (q * x + x * q) * q =
    (q * q) * x - x * (q * q)
  noncomm_ring

theorem jordan_lie_same (q : A) :
    jordanOp R q * lieOp R q = lieOp R (q * q) := by
  ext x
  change q * (q * x - x * q) + (q * x - x * q) * q =
    (q * q) * x - x * (q * q)
  noncomm_ring

theorem mixed_self_zero {q : A} (hq : q * q = 0) :
    lieOp R q * jordanOp R q = 0 ∧ jordanOp R q * lieOp R q = 0 := by
  rw [lie_jordan_same, jordan_lie_same, hq]
  have hz : lieOp R (0 : A) = 0 := by ext x; simp
  exact ⟨hz, hz⟩

theorem jordan_lie_mixed_sum (a b : A) :
    jordanOp R a * lieOp R b + jordanOp R b * lieOp R a =
      lieOp R (a * b + b * a) := by
  ext x
  change a * (b * x - x * b) + (b * x - x * b) * a +
    (b * (a * x - x * a) + (a * x - x * a) * b) =
    (a * b + b * a) * x - x * (a * b + b * a)
  noncomm_ring

theorem lie_jordan_mixed_sum (a b : A) :
    lieOp R a * jordanOp R b + lieOp R b * jordanOp R a =
      lieOp R (a * b + b * a) := by
  ext x
  change a * (b * x + x * b) - (b * x + x * b) * a +
    (b * (a * x + x * a) - (a * x + x * a) * b) =
    (a * b + b * a) * x - x * (a * b + b * a)
  noncomm_ring

/-- The cross-swapped mixed difference is NOT the mixed operator commutator. -/
theorem mixed_difference_defect (a b : A) :
    lieOp R a * jordanOp R b - lieOp R b * jordanOp R a =
      jordanOp R (a * b - b * a) +
        (2 : ℕ) • (sandwichOp R a b - sandwichOp R b a) := by
  rw [two_nsmul]
  ext x
  change a * (b * x + x * b) - (b * x + x * b) * a -
    (b * (a * x + x * a) - (a * x + x * a) * b) =
    ((a * b - b * a) * x + x * (a * b - b * a)) +
    ((a * x * b - b * x * a) + (a * x * b - b * x * a))
  noncomm_ring

theorem jordan_pair_sum (a b : A) :
    jordanOp R a * jordanOp R b + jordanOp R b * jordanOp R a =
      jordanOp R (a * b + b * a) + (2 : ℕ) • crossTransport R a b := by
  rw [two_nsmul]
  ext x
  change a * (b * x + x * b) + (b * x + x * b) * a +
    (b * (a * x + x * a) + (a * x + x * a) * b) =
    ((a * b + b * a) * x + x * (a * b + b * a)) +
    ((a * x * b + b * x * a) + (a * x * b + b * x * a))
  noncomm_ring

theorem lie_pair_sum (a b : A) :
    lieOp R a * lieOp R b + lieOp R b * lieOp R a =
      jordanOp R (a * b + b * a) - (2 : ℕ) • crossTransport R a b := by
  rw [two_nsmul]
  ext x
  change a * (b * x - x * b) - (b * x - x * b) * a +
    (b * (a * x - x * a) - (a * x - x * a) * b) =
    ((a * b + b * a) * x + x * (a * b + b * a)) -
    ((a * x * b + b * x * a) + (a * x * b + b * x * a))
  noncomm_ring

theorem pure_pair_total (a b : A) :
    (jordanOp R a * jordanOp R b + jordanOp R b * jordanOp R a) +
      (lieOp R a * lieOp R b + lieOp R b * lieOp R a) =
        (2 : ℕ) • jordanOp R (a * b + b * a) := by
  rw [jordan_pair_sum, lie_pair_sum, two_nsmul]
  abel

theorem pure_pair_difference (a b : A) :
    (jordanOp R a * jordanOp R b + jordanOp R b * jordanOp R a) -
      (lieOp R a * lieOp R b + lieOp R b * lieOp R a) =
        (4 : ℕ) • crossTransport R a b := by
  rw [jordan_pair_sum, lie_pair_sum]
  abel

theorem crossTransport_one (a b : A) :
    crossTransport R a b 1 = a * b + b * a := by
  simp

/-- A real algebra map intertwines the complete two-sided transport. -/
theorem crossTransport_natural {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (a b : A) :
    f.toLinearMap.comp (crossTransport R a b) =
      (crossTransport R (f a) (f b)).comp f.toLinearMap := by
  ext x
  change f (a * x * b + b * x * a) =
    f a * f x * f b + f b * f x * f a
  simp only [map_add, map_mul]

end InfoGeometry.OperatorAlgebra.LieJordan
