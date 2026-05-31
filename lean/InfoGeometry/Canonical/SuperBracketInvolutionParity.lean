import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.SuperBracketInvolutionParity

Concrete superbracket parity lemmas for an involutive grading.

If an algebra endomorphism `σ` grades operators by

* even: `σ X = X`,
* odd:  `σ X = -X`,

then products, commutators, and anticommutators land in the expected graded
sectors.

No wrappers.
No analytic continuation.
No `sorry`.
-/

namespace InfoGeometry.Canonical.SuperBracketInvolutionParity

section RingStage

variable {𝕜 A : Type*}
variable [CommRing 𝕜]
variable [Ring A] [Algebra 𝕜 A]

/-- Algebraic commutator. -/
def commutator (X Y : A) : A :=
  X * Y - Y * X

/-- Algebraic anticommutator. -/
def anticommutator (X Y : A) : A :=
  X * Y + Y * X

/--
Even times even is even.
-/
theorem map_mul_even_even
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = Y) :
    σ (X * Y) = X * Y := by
  rw [map_mul, hX, hY]

/--
Even times odd is odd.
-/
theorem map_mul_even_odd
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = -Y) :
    σ (X * Y) = -(X * Y) := by
  rw [map_mul, hX, hY]
  noncomm_ring

/--
Odd times even is odd.
-/
theorem map_mul_odd_even
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = Y) :
    σ (X * Y) = -(X * Y) := by
  rw [map_mul, hX, hY]
  noncomm_ring

/--
Odd times odd is even.
-/
theorem map_mul_odd_odd
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = -Y) :
    σ (X * Y) = X * Y := by
  rw [map_mul, hX, hY]
  noncomm_ring

/--
The commutator of two even operators is even.
-/
theorem commutator_even_even
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = Y) :
    σ (commutator X Y) = commutator X Y := by
  unfold commutator
  rw [map_sub, map_mul, map_mul, hX, hY]

/--
The commutator of an even and an odd operator is odd.
-/
theorem commutator_even_odd
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = -Y) :
    σ (commutator X Y) = - commutator X Y := by
  unfold commutator
  rw [map_sub, map_mul, map_mul, hX, hY]
  noncomm_ring

/--
The commutator of an odd and an even operator is odd.
-/
theorem commutator_odd_even
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = Y) :
    σ (commutator X Y) = - commutator X Y := by
  unfold commutator
  rw [map_sub, map_mul, map_mul, hX, hY]
  noncomm_ring

/--
The commutator of two odd operators is even.
-/
theorem commutator_odd_odd
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = -Y) :
    σ (commutator X Y) = commutator X Y := by
  unfold commutator
  rw [map_sub, map_mul, map_mul, hX, hY]
  noncomm_ring

/--
The anticommutator of two even operators is even.
-/
theorem anticommutator_even_even
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = Y) :
    σ (anticommutator X Y) = anticommutator X Y := by
  unfold anticommutator
  rw [map_add, map_mul, map_mul, hX, hY]

/--
The anticommutator of an even and an odd operator is odd.
-/
theorem anticommutator_even_odd
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = X)
    (hY : σ Y = -Y) :
    σ (anticommutator X Y) = - anticommutator X Y := by
  unfold anticommutator
  rw [map_add, map_mul, map_mul, hX, hY]
  noncomm_ring

/--
The anticommutator of an odd and an even operator is odd.
-/
theorem anticommutator_odd_even
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = Y) :
    σ (anticommutator X Y) = - anticommutator X Y := by
  unfold anticommutator
  rw [map_add, map_mul, map_mul, hX, hY]
  noncomm_ring

/--
The anticommutator of two odd operators is even.

This is the finite algebraic super-Lie closure rule:

`odd × odd → even`.
-/
theorem anticommutator_odd_odd
    (σ : A →ₐ[𝕜] A)
    {X Y : A}
    (hX : σ X = -X)
    (hY : σ Y = -Y) :
    σ (anticommutator X Y) = anticommutator X Y := by
  unfold anticommutator
  rw [map_add, map_mul, map_mul, hX, hY]
  noncomm_ring

/--
The square of an odd operator is even.

This is the parity statement behind odd nilpotent lanes:
if additionally `X * X = 0`, the nilpotency lives in the even zero sector.
-/
theorem square_of_odd_is_even
    (σ : A →ₐ[𝕜] A)
    {X : A}
    (hX : σ X = -X) :
    σ (X * X) = X * X := by
  rw [map_mul, hX]
  noncomm_ring

/--
Odd square-zero is transported by the grading map.

This is a useful sanity check for nilpotent transition channels.
-/
theorem map_odd_square_zero
    (σ : A →ₐ[𝕜] A)
    {X : A}
    (hX : σ X = -X)
    (hNil : X * X = 0) :
    σ (X * X) = 0 := by
  calc
    σ (X * X) = X * X := square_of_odd_is_even σ hX
    _ = 0 := hNil

end RingStage

end InfoGeometry.Canonical.SuperBracketInvolutionParity
