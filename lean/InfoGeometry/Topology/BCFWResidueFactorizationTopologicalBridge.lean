import InfoGeometry.Canonical.BCFWMeromorphicResidueRecursion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.PeirceBCFWResidueFactorizationTopological

namespace InfoGeometry.Topology.BCFWResidueFactorizationTopologicalBridge

open InfoGeometry.Canonical

noncomputable section

/-!
# Narrow bridge from finite BCFW residue algebra to the topological channel term

This file does not claim meromorphic continuation or a full contour argument.
It only packages the existing finite partial-fraction identity together with
the continuity of the Peirce channel term on the nonzero propagator locus.
-/

theorem continuous_peirceBCFWChannelTerm
    (amplitudeLeft amplitudeRight : ℂ) :
    ContinuousOn
      (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
        peirceBCFWChannelTerm amplitudeLeft amplitudeRight M)
      {M | splitQuadratic (embedRealSplit M) ≠ 0} :=
  InfoGeometry.Topology.continuousOn_peirceBCFWChannelTerm amplitudeLeft amplitudeRight

theorem peirceBCFWChannelTerm_factorized
    (amplitudeLeft amplitudeRight : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hprop : splitQuadratic (embedRealSplit M) ≠ 0) :
    (splitQuadratic (embedRealSplit M) : ℂ) *
        peirceBCFWChannelTerm amplitudeLeft amplitudeRight M =
      amplitudeLeft * amplitudeRight :=
  InfoGeometry.Canonical.peirceBCFWChannelTerm_factorized
    amplitudeLeft amplitudeRight M hprop

theorem peirce_bcfw_algebraic_residue_identity
    {I : Type*} [Fintype I]
    (c : I → ℂ)
    (data : I → PeirceBCFWShiftParameters)
    (PI : I → PeirceKinematicMomentum)
    (hslopes : ∀ i, 2 * peirceKinematicInner (PI i) (data i).q ≠ 0)
    (hpoles_nonzero : ∀ i, peirceChannelPole (data i) (PI i) ≠ 0) :
    (algebraicAmplitude c
        (fun i => peirceChannelPole (data i) (PI i)) 0 =
      - ∑ i, algebraicResidueOverZ c
        (fun i => peirceChannelPole (data i) (PI i)) i) ∧
    (∀ i, peirceKinematicInner
        (shiftedChannel (data i).toBCFWShiftData (PI i)
          (peirceChannelPole (data i) (PI i)))
        (shiftedChannel (data i).toBCFWShiftData (PI i)
          (peirceChannelPole (data i) (PI i))) = 0) :=
  InfoGeometry.Canonical.peirce_bcfw_algebraic_residue_identity
    c data PI hslopes hpoles_nonzero

theorem peirce_bcfw_residue_topological_bridge
    (amplitudeLeft amplitudeRight : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hprop : splitQuadratic (embedRealSplit M) ≠ 0) :
    ContinuousOn
      (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
        peirceBCFWChannelTerm amplitudeLeft amplitudeRight M)
      {M | splitQuadratic (embedRealSplit M) ≠ 0} ∧
    (splitQuadratic (embedRealSplit M) : ℂ) *
        peirceBCFWChannelTerm amplitudeLeft amplitudeRight M =
      amplitudeLeft * amplitudeRight := by
  refine ⟨continuous_peirceBCFWChannelTerm amplitudeLeft amplitudeRight, ?_⟩
  simpa using peirceBCFWChannelTerm_factorized amplitudeLeft amplitudeRight M hprop

end

end InfoGeometry.Topology.BCFWResidueFactorizationTopologicalBridge
