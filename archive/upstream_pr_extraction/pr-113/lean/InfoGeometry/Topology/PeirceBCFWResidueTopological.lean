import InfoGeometry.Canonical.PeirceBCFWResidueSpecialization
import InfoGeometry.Topology.BCFWMeromorphicTopological

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

noncomputable section

/-! Continuity of the finite partial-fraction model after replacing its
abstract pole family by typed Peirce channel poles. -/

theorem continuousOn_peirce_algebraicAmplitude
    {I : Type*} [Fintype I]
    (c : I → ℂ)
    (data : I → PeirceBCFWShiftParameters)
    (PI : I → PeirceKinematicMomentum) :
    ContinuousOn
      (algebraicAmplitude c
        (fun i => peirceChannelPole (data i) (PI i)))
      (BCFWMeromorphic.poleComplement
        (fun i => peirceChannelPole (data i) (PI i))) := by
  exact BCFWMeromorphic.continuousOn_algebraicAmplitude c
    (fun i => peirceChannelPole (data i) (PI i))

end

end InfoGeometry.Topology
