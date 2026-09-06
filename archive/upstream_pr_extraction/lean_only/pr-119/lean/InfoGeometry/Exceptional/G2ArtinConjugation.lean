import InfoGeometry.Exceptional.G2ArtinPresentation

/-!
# Inner conjugation on the native `G₂` Artin carrier

This file packages conjugation by an actual element of the existing presented
Artin group.  It does not identify a Klein glide with such an element.
-/

namespace InfoGeometry.Exceptional.G2ArtinConjugation

open InfoGeometry.Exceptional.G2ArtinPresentation

def artinConjugation (g : ArtinG2) : ArtinG2 →* ArtinG2 where
  toFun x := g * x * g⁻¹
  map_one' := by simp
  map_mul' := by
    intro x y
    simp [mul_assoc]

@[simp] theorem artinConjugation_apply (g x : ArtinG2) :
    artinConjugation g x = g * x * g⁻¹ := rfl

theorem artinConjugation_generator (g : ArtinG2) (i : Generator) :
    artinConjugation g (PresentedGroup.of i) =
      g * PresentedGroup.of i * g⁻¹ := rfl

end InfoGeometry.Exceptional.G2ArtinConjugation
