import InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LLM.FourierCharacterEncoding

/-!
# Fourier Characters and Positional Representations

## i. Overview

Connects additive Fourier characters to scalar positional representations and records the
commutativity limitation of one-dimensional multiplicative characters.

## ii. Key results

- `monoidCharacter_blind_to_commutator`
- `FourierCharacter.toPositionRepresentation_relative_kernel`

## iii. Table of contents

- Scalar character commutator blindness
- Positional representation induced by a Fourier character

## iv. References

- Repository owner for finite Fourier characters and positional dynamics.
-/

namespace InfoGeometry.Canonical.PositionalDynamicsRegimeBridge

open InfoGeometry.LLM

/-- A scalar multiplicative character into a commutative ring is blind to
the order of a two-letter product. This is the precise limitation of the
one-dimensional character channel; it makes no claim about matrix
representations. -/
theorem monoidCharacter_blind_to_commutator
    {G K : Type*} [Monoid G] [CommRing K] (χ : G →* K) (u v : G) :
    χ (u * v) - χ (v * u) = 0 := by
  rw [map_mul, map_mul, mul_comm]
  exact sub_self _

/-! A Fourier character is a positional representation on the complex carrier.
The action is scalar multiplication; composition is therefore inherited from
the character law rather than postulated separately.
-/

noncomputable def FourierCharacter.toPositionRepresentation
    {G : Type*} [AddMonoid G] (χ : FourierCharacter G) :
    AdditivePositionRepresentation (ℂ → ℂ) G where
  unit := id
  mul := fun f g => g ∘ f
  value := fun t z => (χ t : ℂ) * z
  value_zero := by
    funext z
    rw [χ.map_zero']
    simp
  value_add := by
    intro s t
    funext z
    rw [χ.map_add']
    simp [mul_assoc, mul_comm]

/-- The scalar action of a Fourier character at a point. -/
theorem FourierCharacter.toPositionRepresentation_value
    {G : Type*} [AddMonoid G] (χ : FourierCharacter G) (t : G) (z : ℂ) :
    (FourierCharacter.toPositionRepresentation χ).value t z = (χ t : ℂ) * z := rfl

/-- Composing the positional actions at `t` and `-s` recovers the translation-invariant
Fourier kernel evaluated at the relative coordinate `t - s`. -/
theorem FourierCharacter.toPositionRepresentation_relative_kernel
    {G : Type*} [AddCommGroup G] (χ : FourierCharacter G) (t s : G) :
    ((FourierCharacter.toPositionRepresentation χ).value t ∘
      (FourierCharacter.toPositionRepresentation χ).value (-s)) 1 =
      fourierCharacterKernel χ t (-s) := by
  simp [FourierCharacter.toPositionRepresentation,
    fourierCharacterKernel, χ.map_add']

end InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
