import Mathlib

/-!
# The affine Klein semidirect-product relation

The quotient-group relation is represented here on the logarithmic affine
coordinate.  Translation is the additive Cartan/winding direction and the
reflection reverses it.  This is deliberately independent of any topological
quotient construction or projective anomaly phase.
-/

namespace InfoGeometry.Projective.KleinSemidirectProductBridge

def translation (a : ℝ) : ℝ → ℝ := fun x => x + a

def reflection : ℝ → ℝ := fun x => -x

theorem reflection_involutive : reflection ∘ reflection = id := by
  funext x
  simp [reflection, Function.comp_def]

theorem reflection_translation_reflection (a : ℝ) :
    reflection ∘ translation a ∘ reflection = translation (-a) := by
  funext x
  simp [reflection, translation, Function.comp_def]
  ring

theorem translation_add (a b : ℝ) :
    translation a ∘ translation b = translation (a + b) := by
  funext x
  simp [translation, Function.comp_def]
  ring

theorem translation_zero :
    translation 0 = id := by
  funext x
  simp [translation]

theorem reflection_translation (a : ℝ) :
    reflection ∘ translation a = translation (-a) ∘ reflection := by
  funext x
  simp [reflection, translation, Function.comp_def]
  ring

theorem klein_relation (a : ℝ) :
    reflection ∘ translation a ∘ reflection ∘ translation a = id := by
  funext x
  simp [reflection, translation, Function.comp_def]
  ring

theorem translation_inverse (a : ℝ) :
    translation (-a) ∘ translation a = id := by
  funext x
  simp [translation, Function.comp_def]

theorem translation_inverse_right (a : ℝ) :
    translation a ∘ translation (-a) = id := by
  funext x
  simp [translation, Function.comp_def]

end InfoGeometry.Projective.KleinSemidirectProductBridge
