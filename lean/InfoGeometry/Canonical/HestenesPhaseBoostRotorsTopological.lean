import Mathlib.Topology.Algebra.Module.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesPhaseBoostRotors

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

theorem continuous_realBoostAction
    (K : V →ₗ[ℝ] V) (hK_cont : Continuous K) :
    Continuous (fun p : ℝ × V => realBoostAction K p.1 p.2) := by
  unfold realBoostAction
  exact ((Real.continuous_cosh.comp continuous_fst).smul continuous_snd).add
    ((Real.continuous_sinh.comp continuous_fst).smul (hK_cont.comp continuous_snd))

def realBoostHomeomorph
    (K : V →ₗ[ℝ] V) (hK : IsRealInvolution K)
    (hK_cont : Continuous K) (t : ℝ) : V ≃ₜ V :=
  { toFun := realBoostAction K t
    invFun := realBoostAction K (-t)
    left_inv := by
      intro v
      exact realBoostAction_inverse K hK t v
    right_inv := by
      intro v
      simpa only [neg_neg] using realBoostAction_inverse K hK (-t) v
    continuous_toFun :=
      (continuous_realBoostAction K hK_cont).comp
        (continuous_const.prodMk continuous_id)
    continuous_invFun := by
      exact (continuous_realBoostAction K hK_cont).comp
        (continuous_const.prodMk continuous_id) }

@[simp] theorem realBoostHomeomorph_apply
    (K : V →ₗ[ℝ] V) (hK : IsRealInvolution K)
    (hK_cont : Continuous K) (t : ℝ) (v : V) :
    realBoostHomeomorph K hK hK_cont t v = realBoostAction K t v := rfl

@[simp] theorem realBoostHomeomorph_symm_apply
    (K : V →ₗ[ℝ] V) (hK : IsRealInvolution K)
    (hK_cont : Continuous K) (t : ℝ) (v : V) :
    (realBoostHomeomorph K hK hK_cont t).symm v =
      realBoostAction K (-t) v := rfl

end

end InfoGeometry.Canonical
