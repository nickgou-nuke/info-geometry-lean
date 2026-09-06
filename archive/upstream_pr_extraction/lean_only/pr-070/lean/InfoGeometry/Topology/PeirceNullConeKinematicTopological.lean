import InfoGeometry.Canonical.PeirceNullConeKinematicEmbedding

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

theorem continuous_channelCoordinates :
    Continuous channelCoordinates := by
  unfold channelCoordinates
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

theorem continuous_channelQuadratic :
    Continuous channelQuadratic := by
  unfold channelQuadratic
  fun_prop

theorem isClosed_peirceNullCone :
    IsClosed peirceNullCone := by
  exact isClosed_eq continuous_channelQuadratic continuous_const

end InfoGeometry.Topology
