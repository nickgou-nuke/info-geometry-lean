import InfoGeometry.Canonical.HestenesMirrorLoxodromic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesLoxodromicRotorTopological

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

theorem continuous_mirror_realLoxodromicAction
    (K I : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V)
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (hJ_cont : Continuous J) :
    Continuous (fun p : ℝ × ℝ × V =>
      J (realLoxodromicAction K I p.1 p.2.1 p.2.2)) := by
  exact hJ_cont.comp (continuous_realLoxodromicAction K I hK_cont hI_cont)

theorem continuous_mirror_realLoxodromicAction_eq_reverse
    (K I : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V)
    (hJK : ∀ v : V, J (K v) = -(K (J v)))
    (hJI : ∀ v : V, J (I v) = -(I (J v)))
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (hJ_cont : Continuous J) :
    Continuous (fun p : ℝ × ℝ × V =>
      realLoxodromicAction K I (-p.1) (-p.2.1) (J p.2.2)) := by
  exact (continuous_realLoxodromicAction K I hK_cont hI_cont).comp
    ((continuous_neg.comp continuous_fst).prodMk
      ((continuous_neg.comp continuous_snd.fst).prodMk
        (hJ_cont.comp continuous_snd.snd)))

end

end InfoGeometry.Canonical
