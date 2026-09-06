import Mathlib

/-!
# Exceptional points on the Klein bottle: they do the glide

König's non-orientable extension says the usual torus-doubling intuition is
replaced by a glide-twisted identification.  On the Klein bottle the fundamental
relation is

`g a g⁻¹ = a⁻¹`, equivalently `g a g⁻¹ a = 1`.

Thus the apparent partner of an exceptional point is not an independent doubler:
it is the glide image with inverse braid/charge.  EPs "do the glide".
-/

namespace ExceptionalKleinGlideEP

variable {B : Type*} [Group B]

/-- Torus commutator word. -/
def torusWord (x y : B) : B := x * y * x⁻¹ * y⁻¹

/-- Klein bottle boundary word: glide-conjugate followed by the original translation. -/
def kleinWord (g a : B) : B := g * a * g⁻¹ * a

/-- The glide image of a charge. -/
def glidePartner (g a : B) : B := g * a * g⁻¹

/-- Klein relation: the glide sends a charge to its inverse. -/
def KleinGlideRelation (g a : B) : Prop := glidePartner g a = a⁻¹

/-- If the glide sends `a` to `a⁻¹`, then the Klein boundary word is trivial. -/
theorem klein_word_trivial_of_glide_inverse {g a : B} (h : KleinGlideRelation g a) :
    kleinWord g a = 1 := by
  unfold kleinWord KleinGlideRelation glidePartner at *
  rw [h]
  group

/-- Equivalently, the charge cancels with its glide partner. -/
theorem charge_times_glide_partner_trivial {g a : B} (h : KleinGlideRelation g a) :
    glidePartner g a * a = 1 := by
  unfold KleinGlideRelation at h
  rw [h]
  group

/-- The Klein word relation recovers the glide-inverse relation. -/
theorem glide_inverse_of_klein_word_trivial {g a : B} (h : kleinWord g a = 1) :
    KleinGlideRelation g a := by
  unfold kleinWord KleinGlideRelation glidePartner at *
  calc
    g * a * g⁻¹ = (g * a * g⁻¹ * a) * a⁻¹ := by group
    _ = 1 * a⁻¹ := by rw [h]
    _ = a⁻¹ := by group

/-- A glide-fixed charge is necessarily involutive. -/
theorem square_one_of_glide_fixed_and_inverse {g a : B}
    (hfix : glidePartner g a = a) (hinv : KleinGlideRelation g a) :
    a * a = 1 := by
  unfold KleinGlideRelation at hinv
  rw [hfix] at hinv
  have hmul : a * a = a⁻¹ * a := congrArg (fun x => x * a) hinv
  rw [hmul]
  group

/-- Main synthesis theorem for "EPs do the glide". -/
theorem exceptional_klein_glide_ep_synthesis (g a : B)
    (h : KleinGlideRelation g a) :
    glidePartner g a = a⁻¹ ∧
    kleinWord g a = 1 ∧
    glidePartner g a * a = 1 := by
  exact ⟨h, klein_word_trivial_of_glide_inverse h, charge_times_glide_partner_trivial h⟩

#check klein_word_trivial_of_glide_inverse
#check glide_inverse_of_klein_word_trivial
#check square_one_of_glide_fixed_and_inverse
#check exceptional_klein_glide_ep_synthesis

end ExceptionalKleinGlideEP
