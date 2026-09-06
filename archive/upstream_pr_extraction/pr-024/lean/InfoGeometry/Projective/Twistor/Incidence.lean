import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Module.Basic

/-!
# Twistor incidence (abstract projective interface)

Incidence is modeled abstractly as a relation stable under independent scaling
on twistor and dual-twistor representatives.
-/

namespace InfoGeometry.Projective.Twistor

universe u

structure TwistorIncidenceDatum
    (𝕜 T D : Type u)
    [CommRing 𝕜]
    [AddCommGroup T] [Module 𝕜 T]
    [AddCommGroup D] [Module 𝕜 D] where
  incidence : D → T → Prop
  twScale : 𝕜ˣ → T → T
  dualScale : 𝕜ˣ → D → D
  incidence_scale_left : ∀ u ξ Z, incidence (dualScale u ξ) Z ↔ incidence ξ Z
  incidence_scale_right : ∀ u ξ Z, incidence ξ (twScale u Z) ↔ incidence ξ Z

namespace TwistorIncidenceDatum

variable {𝕜 T D : Type u}
variable [CommRing 𝕜]
variable [AddCommGroup T] [Module 𝕜 T]
variable [AddCommGroup D] [Module 𝕜 D]

def TwistorPair (I : TwistorIncidenceDatum 𝕜 T D) : Type u := T × D

def DualTwistor (I : TwistorIncidenceDatum 𝕜 T D) : Type u := D

def Incidence (I : TwistorIncidenceDatum 𝕜 T D) : DualTwistor I → T → Prop :=
  I.incidence

@[simp] theorem incidence_scale_left_iff
    (I : TwistorIncidenceDatum 𝕜 T D)
    (u : 𝕜ˣ) (ξ : DualTwistor I) (Z : T) :
    I.Incidence (I.dualScale u ξ) Z ↔ I.Incidence ξ Z :=
  I.incidence_scale_left u ξ Z

@[simp] theorem incidence_scale_right_iff
    (I : TwistorIncidenceDatum 𝕜 T D)
    (u : 𝕜ˣ) (ξ : DualTwistor I) (Z : T) :
    I.Incidence ξ (I.twScale u Z) ↔ I.Incidence ξ Z :=
  I.incidence_scale_right u ξ Z

end TwistorIncidenceDatum

end InfoGeometry.Projective.Twistor
