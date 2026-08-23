import InfoGeometry.Twistor.TwoTwistorSpacetimeNode

/-!
# Reality criterion for a two-twistor spacetime node

The two-twistor reconstruction is naturally complex.  This owner isolates
the additional Hermitian condition needed to call the reconstructed matrix a
real spacetime representative, using the existing incidence and uniqueness
owners rather than introducing a second reality convention.
-/

namespace InfoGeometry.Twistor.TwoTwistorSpacetimeReality

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorSpacetimeNode

def IsHermitianSpacetime (X : ComplexSpacetime) : Prop :=
  Matrix.conjTranspose X = X

def HasHermitianFrameNode (P Ω : ComplexSpacetime) : Prop :=
  ∃ X : ComplexSpacetime,
    IsHermitianSpacetime X ∧
    incidenceLinearMap X (P.mulVec ![1, 0]) =
      (Ω.mulVec ![1, 0], P.mulVec ![1, 0]) ∧
    incidenceLinearMap X (P.mulVec ![0, 1]) =
      (Ω.mulVec ![0, 1], P.mulVec ![0, 1])

theorem hasHermitianFrameNode_iff_reconstructedNode_hermitian
    (P Ω : ComplexSpacetime) (hP : IsUnit P.det)
    (hpair : IndependentSpanningSpinorPair (P.mulVec ![1, 0])
      (P.mulVec ![0, 1])) :
    HasHermitianFrameNode P Ω ↔
      IsHermitianSpacetime (frameSpacetimeNode P Ω) := by
  constructor
  · rintro ⟨X, hX, h₁, h₂⟩
    have hnode := two_twistor_spacetime_node_unique
      (frameSpacetimeNode P Ω) X (P.mulVec ![1, 0]) (P.mulVec ![0, 1])
      (Ω.mulVec ![1, 0], P.mulVec ![1, 0])
      (Ω.mulVec ![0, 1], P.mulVec ![0, 1])
      (frameSpacetimeNode_incidence P Ω hP ![1, 0])
      (frameSpacetimeNode_incidence P Ω hP ![0, 1]) h₁ h₂ hpair
    rw [hnode]
    exact hX
  · intro hX
    refine ⟨frameSpacetimeNode P Ω, hX,
      frameSpacetimeNode_incidence P Ω hP ![1, 0],
      frameSpacetimeNode_incidence P Ω hP ![0, 1]⟩

end InfoGeometry.Twistor.TwoTwistorSpacetimeReality
