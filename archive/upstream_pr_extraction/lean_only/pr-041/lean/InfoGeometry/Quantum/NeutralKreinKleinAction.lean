import Mathlib
import InfoGeometry.Quantum.NeutralKreinMajoranaFrame

/-!
# Neutral Krein carrier and the Klein-bottle group relation

This owner separates the linear neutral/Krein frame from the discrete quotient
data.  The former is supplied by `NeutralKreinMajoranaFrame`; this file adds
only the algebraic Klein-bottle action relation

`a b a⁻¹ = b⁻¹`.

The affine model on `ℤ × ℤ` is the standard glide/translation model.  It is
deliberately not packaged as a topological quotient: proving that quotient is
homeomorphic to a Klein bottle is a separate topological theorem.
-/

namespace InfoGeometry.Quantum.NeutralKreinKleinAction

section

variable {X : Type*}

/-- The algebraic data carried by a Klein-bottle action. -/
structure KleinBottleAction where
  translation : X ≃ X
  glide : X ≃ X
  conjugation_inverts :
    glide.symm.trans (translation.trans glide) = translation.symm

namespace KleinBottleAction

variable (A : KleinBottleAction (X := X))

theorem conjugation_inverts_pointwise (x : X) :
    A.glide (A.translation (A.glide.symm x)) = A.translation.symm x := by
  have h := congrArg (fun e : X ≃ X => e x) A.conjugation_inverts
  simpa [Equiv.trans_apply] using h

end KleinBottleAction

end

section AffineModel

abbrev AffinePoint := ℤ × ℤ

/-- The vertical winding translation. -/
def windingTranslation : AffinePoint ≃ AffinePoint where
  toFun p := (p.1, p.2 + 1)
  invFun p := (p.1, p.2 - 1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- Translation by an arbitrary integer winding number. -/
def windingTranslationBy (n : ℤ) : AffinePoint ≃ AffinePoint where
  toFun p := (p.1, p.2 + n)
  invFun p := (p.1, p.2 - n)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

theorem windingTranslationBy_zero :
    windingTranslationBy 0 = (Equiv.refl AffinePoint) := by
  ext p <;> simp [windingTranslationBy]

theorem windingTranslationBy_add (m n : ℤ) :
    (windingTranslationBy m).trans (windingTranslationBy n) =
      windingTranslationBy (m + n) := by
  ext p <;> simp [windingTranslationBy] <;> omega

theorem windingTranslationBy_neg (n : ℤ) :
    (windingTranslationBy (-n)) = (windingTranslationBy n).symm := by
  ext p <;> simp [windingTranslationBy] <;> omega

/-- The horizontal glide reflection of the universal cover. -/
def affineGlide : AffinePoint ≃ AffinePoint where
  toFun p := (p.1 + 1, -p.2)
  invFun p := (p.1 - 1, -p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

theorem windingTranslation_inverse :
    (windingTranslation : AffinePoint ≃ AffinePoint).symm =
      { toFun := fun p : AffinePoint => (p.1, p.2 - 1)
        invFun := fun p : AffinePoint => (p.1, p.2 + 1)
        left_inv := by intro p; ext <;> simp
        right_inv := by intro p; ext <;> simp } := by
  rfl

theorem affineGlide_square :
    (affineGlide : AffinePoint ≃ AffinePoint).trans affineGlide =
      { toFun := fun p : AffinePoint => (p.1 + 2, p.2)
        invFun := fun p : AffinePoint => (p.1 - 2, p.2)
        left_inv := by intro p; ext <;> simp
        right_inv := by intro p; ext <;> simp } := by
  ext p <;> simp [affineGlide] <;> omega

/-- The affine glide conjugates winding to inverse winding. -/
theorem affineGlide_conjugates_winding_inverse :
    affineGlide.symm.trans (windingTranslation.trans affineGlide) =
      windingTranslation.symm := by
  ext p <;> simp [affineGlide, windingTranslation] <;> omega

/-- The glide reverses every integer winding, not only the unit generator. -/
theorem affineGlide_conjugates_windingBy (n : ℤ) :
    affineGlide.symm.trans ((windingTranslationBy n).trans affineGlide) =
      windingTranslationBy (-n) := by
  ext p <;> simp [affineGlide, windingTranslationBy] <;> omega

/-- The glide has no fixed point on the affine universal-cover model. -/
theorem affineGlide_no_fixed (p : AffinePoint) : affineGlide p ≠ p := by
  intro h
  have hfirst := congrArg Prod.fst h
  simp [affineGlide] at hfirst

/-- A nonzero winding translation has no fixed point. -/
theorem windingTranslationBy_no_fixed {n : ℤ} (hn : n ≠ 0) (p : AffinePoint) :
    windingTranslationBy n p ≠ p := by
  intro h
  have hsecond := congrArg Prod.snd h
  simp [windingTranslationBy] at hsecond
  exact hn (by omega)

/-- The affine model is an algebraic Klein-bottle action packet. -/
def affineKleinBottleAction : KleinBottleAction (X := AffinePoint) where
  translation := windingTranslation
  glide := affineGlide
  conjugation_inverts := affineGlide_conjugates_winding_inverse

theorem affineKleinBottleAction_relation (p : AffinePoint) :
    affineGlide (windingTranslation (affineGlide.symm p)) =
      windingTranslation.symm p := by
  exact affineKleinBottleAction.conjugation_inverts_pointwise p

end AffineModel

end InfoGeometry.Quantum.NeutralKreinKleinAction
