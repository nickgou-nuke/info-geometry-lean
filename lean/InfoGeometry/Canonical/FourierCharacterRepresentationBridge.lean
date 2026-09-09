import InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
import InfoGeometry.LLM.FourierCharacterEncoding

namespace InfoGeometry.Canonical.PositionalDynamicsRegimeBridge

open InfoGeometry.LLM

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
    simp [Function.comp_def, mul_assoc, mul_left_comm, mul_comm]

theorem FourierCharacter.toPositionRepresentation_value
    {G : Type*} [AddMonoid G] (χ : FourierCharacter G) (t : G) (z : ℂ) :
    (FourierCharacter.toPositionRepresentation χ).value t z = (χ t : ℂ) * z := rfl

theorem FourierCharacter.toPositionRepresentation_relative_kernel
    {G : Type*} [AddCommGroup G] (χ : FourierCharacter G) (t s : G) :
    ((FourierCharacter.toPositionRepresentation χ).value t ∘
      (FourierCharacter.toPositionRepresentation χ).value (-s)) 1 =
      fourierCharacterKernel χ t (-s) := by
  simp [FourierCharacter.toPositionRepresentation,
    fourierCharacterKernel, Function.comp_def, χ.map_add']

end InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
