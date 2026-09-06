import InfoGeometry.Canonical.HestenesLoxodromicRotor
import InfoGeometry.Canonical.HestenesPhaseBoostRotorsTopological
import InfoGeometry.Canonical.RealComplexRotorTopological

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

theorem continuous_realLoxodromicAction
    (K I : V →ₗ[ℝ] V)
    (hK_cont : Continuous K) (hI_cont : Continuous I) :
    Continuous (fun p : ℝ × ℝ × V =>
      realLoxodromicAction K I p.1 p.2.1 p.2.2) := by
  unfold realLoxodromicAction
  exact (continuous_realBoostAction K hK_cont).comp
    (continuous_fst.prodMk
      ((continuous_realRotorAction I hI_cont).comp
        (continuous_snd.fst.prodMk continuous_snd.snd)))

end

end InfoGeometry.Canonical
