import InfoGeometry.Canonical.PeirceBCFWResidueFactorization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.AlbertPeirceChiralFrameTopological

namespace InfoGeometry.Topology

open InfoGeometry.Algebra
open InfoGeometry.Canonical

noncomputable section

/-! The scalar channel term is continuous away from the zero set of its
quadratic propagator. -/

theorem continuous_splitQuadratic_embedRealSplit :
    Continuous (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      (splitQuadratic (embedRealSplit M) : ℂ)) := by
  unfold splitQuadratic
  fun_prop

theorem continuousOn_peirceBCFWChannelTerm
    (amplitudeLeft amplitudeRight : ℂ) :
    ContinuousOn
      (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
        peirceBCFWChannelTerm amplitudeLeft amplitudeRight M)
      {M | splitQuadratic (embedRealSplit M) ≠ 0} := by
  unfold peirceBCFWChannelTerm bcfwChannelTerm
    bcfwChannelNumerator
  apply ContinuousOn.div continuousOn_const
    continuous_splitQuadratic_embedRealSplit.continuousOn
  · intro M hM
    exact_mod_cast hM

end

end InfoGeometry.Topology
