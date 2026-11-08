import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.KleinQuadricPlucker

/-!
# Pluecker/Klein data of a complex twistor pair

This is the complex counterpart of the existing real exterior/Klein owner.  It
reuses the native `Twistor4` carrier and the generic Pluecker coordinates; it
does not identify the reconstructed spacetime node with its Pluecker line.
-/

namespace InfoGeometry.Twistor.TwoTwistorPluckerKlein

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6

def twistorVector (Z : Twistor4) : Vec4 ℂ where
  x0 := Z.1 0
  x1 := Z.1 1
  x2 := Z.2 0
  x3 := Z.2 1

def twistorPairPlucker (Z₁ Z₂ : Twistor4) : Plucker6 ℂ :=
  pluckerLine (twistorVector Z₁) (twistorVector Z₂)

theorem twistorPairPlucker_on_klein (Z₁ Z₂ : Twistor4) :
    kleinQ (twistorPairPlucker Z₁ Z₂) = 0 := by
  exact kleinQ_pluckerLine (twistorVector Z₁) (twistorVector Z₂)

theorem twistorVector_smul (c : ℂ) (Z : Twistor4) :
    twistorVector (c • Z) = Vec4.scale c (twistorVector Z) := by
  cases Z with
  | mk omega pi =>
    rfl

theorem twistorPairPlucker_smul_left (c : ℂ) (Z₁ Z₂ : Twistor4) :
    twistorPairPlucker (c • Z₁) Z₂ =
      Plucker6.scale c (twistorPairPlucker Z₁ Z₂) := by
  unfold twistorPairPlucker
  rw [twistorVector_smul]
  exact pluckerLine_scale_left c (twistorVector Z₁) (twistorVector Z₂)

theorem twistorPairPlucker_smul_right (c : ℂ) (Z₁ Z₂ : Twistor4) :
    twistorPairPlucker Z₁ (c • Z₂) =
      Plucker6.scale c (twistorPairPlucker Z₁ Z₂) := by
  unfold twistorPairPlucker
  rw [twistorVector_smul]
  exact pluckerLine_scale_right c (twistorVector Z₁) (twistorVector Z₂)

theorem twistorPairPlucker_smul_both (c d : ℂ) (Z₁ Z₂ : Twistor4) :
    twistorPairPlucker (c • Z₁) (d • Z₂) =
      Plucker6.scale (c * d) (twistorPairPlucker Z₁ Z₂) := by
  rw [twistorPairPlucker_smul_left, twistorPairPlucker_smul_right]
  apply Plucker6.ext <;> simp [Plucker6.scale] <;> ring

theorem twistorPairPlucker_swap (Z₁ Z₂ : Twistor4) :
    twistorPairPlucker Z₂ Z₁ =
      Plucker6.scale (-1) (twistorPairPlucker Z₁ Z₂) := by
  unfold twistorPairPlucker
  cases twistorVector Z₁ with
  | mk x0 x1 x2 x3 =>
    cases twistorVector Z₂ with
    | mk y0 y1 y2 y3 =>
      apply Plucker6.ext <;> simp [Plucker6.scale, Plucker6.pluckerLine] <;> ring

end InfoGeometry.Twistor.TwoTwistorPluckerKlein
