import InfoGeometry.Algebra.SupergradedBracket
import Mathlib.Tactic
open InfoGeometry.Algebra.SupergradedBracket

/-!
# InfoGeometry.Canonical.SuperBracketInvolutionParity

Finite parity-closure lemmas for a ring endomorphism grading.

For a ring endomorphism `σ`, the eigenspaces `σ X = X` and `σ X = -X`
are closed under products, commutators, and anticommutators with the usual
superalgebra parity table.

No analytic continuation.
No witness packet.
No wrapper namespace over another theorem surface.
-/

namespace InfoGeometry.Canonical.SuperBracketInvolutionParity

section RingStage

variable {A : Type*}
variable [Ring A]

/-- Algebraic commutator in an associative ring. -/
def commutator (X Y : A) : A :=
  X * Y - Y * X

/-- Algebraic anticommutator in an associative ring. -/
def anticommutator (X Y : A) : A :=
  X * Y + Y * X

/-- Even times even is even. -/
theorem map_mul_even_even
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = Y) :
    σ (X * Y) = X * Y := by
  rw [map_mul, hX, hY]

/-- Even times odd is odd. -/
theorem map_mul_even_odd
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = -Y) :
    σ (X * Y) = -(X * Y) := by
  rw [map_mul, hX, hY]
  noncomm_ring

/-- Odd times even is odd. -/
theorem map_mul_odd_even
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = Y) :
    σ (X * Y) = -(X * Y) := by
  rw [map_mul, hX, hY]
  noncomm_ring

/-- Odd times odd is even. -/
theorem map_mul_odd_odd
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = -Y) :
    σ (X * Y) = X * Y := by
  rw [map_mul, hX, hY]
  noncomm_ring

/-- The commutator of two even elements is even. -/
theorem commutator_even_even
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = Y) :
    σ (commutator X Y) = commutator X Y := by
  unfold commutator
  rw [map_sub, map_mul, map_mul, hX, hY]

/-- The commutator of an even and an odd element is odd. -/
theorem commutator_even_odd
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = -Y) :
    σ (commutator X Y) = -commutator X Y := by
  unfold commutator
  rw [map_sub, map_mul, map_mul, hX, hY]
  noncomm_ring

/-- The commutator of an odd and an even element is odd. -/
theorem commutator_odd_even
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = Y) :
    σ (commutator X Y) = -commutator X Y := by
  unfold commutator
  rw [map_sub, map_mul, map_mul, hX, hY]
  noncomm_ring

/-- The commutator of two odd elements is even. -/
theorem commutator_odd_odd
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = -Y) :
    σ (commutator X Y) = commutator X Y := by
  unfold commutator
  rw [map_sub, map_mul, map_mul, hX, hY]
  noncomm_ring

/-- The anticommutator of two even elements is even. -/
theorem anticommutator_even_even
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = Y) :
    σ (anticommutator X Y) = anticommutator X Y := by
  unfold anticommutator
  rw [map_add, map_mul, map_mul, hX, hY]

/-- The anticommutator of an even and an odd element is odd. -/
theorem anticommutator_even_odd
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = -Y) :
    σ (anticommutator X Y) = -anticommutator X Y := by
  unfold anticommutator
  rw [map_add, map_mul, map_mul, hX, hY]
  noncomm_ring

/-- The anticommutator of an odd and an even element is odd. -/
theorem anticommutator_odd_even
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = Y) :
    σ (anticommutator X Y) = -anticommutator X Y := by
  unfold anticommutator
  rw [map_add, map_mul, map_mul, hX, hY]
  noncomm_ring

/-- The anticommutator of two odd elements is even. -/
theorem anticommutator_odd_odd
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = -Y) :
    σ (anticommutator X Y) = anticommutator X Y := by
  unfold anticommutator
  rw [map_add, map_mul, map_mul, hX, hY]
  noncomm_ring

/-- The square of an odd element is even. -/
theorem square_of_odd_is_even
    (σ : A →+* A)
    {X : A}
    (hX : σ X = -X) :
    σ (X * X) = X * X := by
  rw [map_mul, hX]
  noncomm_ring

/-- Odd square-zero elements map to zero through the grading. -/
theorem map_odd_square_zero
    (σ : A →+* A)
    {X : A}
    (hX : σ X = -X)
    (hNil : X * X = 0) :
    σ (X * X) = 0 := by
  rw [square_of_odd_is_even σ hX, hNil]

/-! ## Parity closure for the repository superbracket -/

/-- The repository superbracket of two even elements is even. -/
theorem superBracket_even_even
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = Y) :
    σ (superBracket false false X Y) =
      superBracket false false X Y := by
  change σ (X * Y - Y * X) = X * Y - Y * X
  rw [map_sub, map_mul, map_mul, hX, hY]

/-- The repository superbracket of an even and an odd element is odd. -/
theorem superBracket_even_odd
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = -Y) :
    σ (superBracket false true X Y) =
      -superBracket false true X Y := by
  change σ (X * Y - Y * X) = -(X * Y - Y * X)
  rw [map_sub, map_mul, map_mul, hX, hY]
  noncomm_ring

/-- The repository superbracket of an odd and an even element is odd. -/
theorem superBracket_odd_even
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = Y) :
    σ (superBracket true false X Y) =
      -superBracket true false X Y := by
  change σ (X * Y - Y * X) = -(X * Y - Y * X)
  rw [map_sub, map_mul, map_mul, hX, hY]
  noncomm_ring

/-- The repository odd-odd superbracket, i.e. the anticommutator, is even. -/
theorem superBracket_odd_odd
    (σ : A →+* A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = -Y) :
    σ (superBracket true true X Y) =
      superBracket true true X Y := by
  change σ (X * Y + Y * X) = X * Y + Y * X
  rw [map_add, map_mul, map_mul, hX, hY]
  noncomm_ring

/-! ## Zero and square-zero superbracket reductions -/

/-- A commuting pair has zero repository even-even superbracket. -/
theorem superBracket_even_even_eq_zero_of_mul_comm
    {X Y : A}
    (h : X * Y = Y * X) :
    superBracket false false X Y = 0 := by
  change X * Y - Y * X = 0
  rw [h]
  noncomm_ring

/-- Mutually annihilating elements have zero repository odd-odd superbracket. -/
theorem superBracket_odd_odd_eq_zero_of_mutual_annihilation
    {X Y : A}
    (hXY : X * Y = 0)
    (hYX : Y * X = 0) :
    superBracket true true X Y = 0 := by
  change X * Y + Y * X = 0
  rw [hXY, hYX]
  abel

/-- The repository odd-odd self-superbracket is the doubled square. -/
theorem superBracket_odd_odd_self_eq_square_add_square
    (X : A) :
    superBracket true true X X = X * X + X * X := by
  rfl

/-- Square-zero elements have zero repository odd-odd self-superbracket. -/
theorem superBracket_odd_odd_self_eq_zero_of_square_zero
    {X : A}
    (hX : X * X = 0) :
    superBracket true true X X = 0 := by
  rw [superBracket_odd_odd_self_eq_square_add_square, hX]
  abel

end RingStage

end InfoGeometry.Canonical.SuperBracketInvolutionParity
