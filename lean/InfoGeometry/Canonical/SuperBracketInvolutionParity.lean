import Mathlib.Tactic

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

end RingStage

end InfoGeometry.Canonical.SuperBracketInvolutionParity
