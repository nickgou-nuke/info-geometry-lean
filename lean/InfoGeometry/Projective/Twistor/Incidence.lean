import Mathlib.Algebra.Group.Units.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.Basic
import InfoGeometry.Twistor.PenroseTwistor

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

/-- The two vertex colors of the directed incidence graph: twistors are black,
and dual twistors are white. -/
abbrev BlackWhiteVertex (_I : TwistorIncidenceDatum 𝕜 T D) : Type u :=
  Sum T D

/-- A directed black-to-white graph edge is precisely the existing Penrose
incidence relation `I.Incidence W Z`; no beta or causal interpretation is
inserted here. -/
def blackWhiteIncidenceEdge (I : TwistorIncidenceDatum 𝕜 T D) :
    BlackWhiteVertex I → BlackWhiteVertex I → Prop
  | .inl Z, .inr W => I.Incidence W Z
  | _, _ => False

/-- The actual twistor-pair payload of a graph edge. -/
abbrev TwistorPairEdge (I : TwistorIncidenceDatum 𝕜 T D) : Type u :=
  {p : I.TwistorPair // I.Incidence p.2 p.1}

/-- Black endpoint of an incidence edge is its twistor component. -/
def incidenceEdgeSource (I : TwistorIncidenceDatum 𝕜 T D)
    (e : TwistorPairEdge I) : BlackWhiteVertex I :=
  Sum.inl e.1.1

/-- White endpoint of an incidence edge is its dual-twistor component. -/
def incidenceEdgeTarget (I : TwistorIncidenceDatum 𝕜 T D)
    (e : TwistorPairEdge I) : BlackWhiteVertex I :=
  Sum.inr e.1.2

/-- Construct the edge payload from an actual twistor-incidence proof. -/
def twistorPairEdgeOfIncidence (I : TwistorIncidenceDatum 𝕜 T D)
    (Z : T) (W : D) (h : I.Incidence W Z) : TwistorPairEdge I :=
  ⟨(Z, W), h⟩

@[simp] theorem incidenceEdgeSource_pair
    (I : TwistorIncidenceDatum 𝕜 T D) (Z : T) (W : D)
    (h : I.Incidence W Z) :
    incidenceEdgeSource I (twistorPairEdgeOfIncidence I Z W h) = Sum.inl Z := rfl

@[simp] theorem incidenceEdgeTarget_pair
    (I : TwistorIncidenceDatum 𝕜 T D) (Z : T) (W : D)
    (h : I.Incidence W Z) :
    incidenceEdgeTarget I (twistorPairEdgeOfIncidence I Z W h) = Sum.inr W := rfl

@[simp] theorem incidenceEdge_source_target (I : TwistorIncidenceDatum 𝕜 T D)
    (e : TwistorPairEdge I) :
    blackWhiteIncidenceEdge I (incidenceEdgeSource I e) (incidenceEdgeTarget I e) :=
  e.2

@[simp] theorem blackWhiteIncidenceEdge_twistor_dual
    (I : TwistorIncidenceDatum 𝕜 T D) (Z : T) (W : D) :
    blackWhiteIncidenceEdge I (.inl Z) (.inr W) ↔ I.Incidence W Z :=
  Iff.rfl

@[simp] theorem blackWhiteIncidenceEdge_dual_twistor
    (I : TwistorIncidenceDatum 𝕜 T D) (W : D) (Z : T) :
    blackWhiteIncidenceEdge I (.inr W) (.inl Z) ↔ False :=
  Iff.rfl

end TwistorIncidenceDatum

/-! ## Concrete Penrose null-projective owner

The projective null twistor carrier is provided by the canonical Penrose
twistor owner.  The explicit witness below is the nonzero vector
`(1, 0, 1, 0)`, which is null for the `(2,2)` helicity form.
-/

abbrev PenroseProjectiveNullTwistor : Type :=
  InfoGeometry.Twistor.PenroseTwistor.NullTwistorSpace

noncomputable def penroseProjectiveNullTwistor_nonempty :
    Nonempty PenroseProjectiveNullTwistor := by
  let z : InfoGeometry.Twistor.PenroseTwistor.TwistorCarrier :=
    fun i => if i = 0 then 1 else if i = 2 then 1 else 0
  have hz : z ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [z] at h0
  have hnull : InfoGeometry.Twistor.PenroseTwistor.helicity z = 0 := by
    rw [InfoGeometry.Twistor.PenroseTwistor.helicity,
      InfoGeometry.Twistor.PenroseTwistor.twistorHermitian_apply]
    norm_num [z, Fin.sum_univ_succ]
  exact ⟨InfoGeometry.Twistor.PenroseTwistor.twistorMk z hz hnull⟩

end InfoGeometry.Projective.Twistor
