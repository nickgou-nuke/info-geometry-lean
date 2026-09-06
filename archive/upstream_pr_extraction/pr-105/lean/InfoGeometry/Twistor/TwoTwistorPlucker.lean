import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Projective.KleinQuadricPlucker

/-!
# Plücker/Klein readout of a twistor pair

The existing Klein owner supplies the decomposable-line theorem.  This file
only supplies the convention-preserving map from the repository's native
`Twistor4 = Spinor2 × Spinor2` carrier to complex homogeneous four-vectors.
-/

namespace InfoGeometry.Twistor.TwoTwistorPlucker

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Projective

abbrev ComplexVec4 := Vec4 ℂ
abbrev ComplexPlucker6 := Plucker6 ℂ

def twistorProjectiveVector (Z : Twistor4) : ComplexVec4 where
  x0 := Z.1 0
  x1 := Z.1 1
  x2 := Z.2 0
  x3 := Z.2 1

def twistorPairPlucker (Z₁ Z₂ : Twistor4) : ComplexPlucker6 :=
  pluckerLine (twistorProjectiveVector Z₁) (twistorProjectiveVector Z₂)

theorem twistorProjectiveVector_smul (c : ℂ) (Z : Twistor4) :
    twistorProjectiveVector (c • Z) =
      Vec4.scale c (twistorProjectiveVector Z) := by
  rcases Z with ⟨ω, π⟩
  rfl

theorem twistorPairPlucker_on_klein (Z₁ Z₂ : Twistor4) :
    kleinQ (twistorPairPlucker Z₁ Z₂) = 0 := by
  exact kleinQ_pluckerLine _ _

theorem twistorPairPlucker_swap (Z₁ Z₂ : Twistor4) :
    twistorPairPlucker Z₂ Z₁ =
      { p01 := -(twistorPairPlucker Z₁ Z₂).p01
        p02 := -(twistorPairPlucker Z₁ Z₂).p02
        p03 := -(twistorPairPlucker Z₁ Z₂).p03
        p12 := -(twistorPairPlucker Z₁ Z₂).p12
        p13 := -(twistorPairPlucker Z₁ Z₂).p13
        p23 := -(twistorPairPlucker Z₁ Z₂).p23 } := by
  rcases Z₁ with ⟨ω₁, π₁⟩
  rcases Z₂ with ⟨ω₂, π₂⟩
  apply Plucker6.ext <;>
    simp [twistorPairPlucker, twistorProjectiveVector, pluckerLine] <;>
    ring

theorem twistorPairPlucker_projective_rescaling
    (c d : ℂ) (Z₁ Z₂ : Twistor4) :
    twistorPairPlucker (c • Z₁) (d • Z₂) =
      Plucker6.scale (c * d) (twistorPairPlucker Z₁ Z₂) := by
  unfold twistorPairPlucker
  rw [twistorProjectiveVector_smul, twistorProjectiveVector_smul,
    pluckerLine_scale_left, pluckerLine_scale_right]
  rcases twistorPairPlucker Z₁ Z₂ with ⟨p01, p02, p03, p12, p13, p23⟩
  apply Plucker6.ext <;> simp [Plucker6.scale] <;> ring

end InfoGeometry.Twistor.TwoTwistorPlucker
