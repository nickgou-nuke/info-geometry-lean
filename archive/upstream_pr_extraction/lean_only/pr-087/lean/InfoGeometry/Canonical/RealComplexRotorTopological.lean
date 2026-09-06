import Mathlib.Topology.Algebra.Module.Basic
import InfoGeometry.Canonical.RealComplexRotor

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

theorem continuous_realRotorAction
    (I : V →ₗ[ℝ] V) (hI_cont : Continuous I) :
    Continuous (fun p : ℝ × V => realRotorAction I p.1 p.2) := by
  unfold realRotorAction
  exact ((Real.continuous_cos.comp continuous_fst).smul continuous_snd).add
    ((Real.continuous_sin.comp continuous_fst).smul (hI_cont.comp continuous_snd))

def realRotorHomeomorph
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (hI_cont : Continuous I) (θ : ℝ) : V ≃ₜ V :=
  { toFun := realRotorAction I θ
    invFun := realRotorAction I (-θ)
    left_inv := by
      intro v
      exact realRotorAction_inverse I hI θ v
    right_inv := by
      intro v
      simpa only [neg_neg] using realRotorAction_inverse I hI (-θ) v
    continuous_toFun := by
      exact (continuous_realRotorAction I hI_cont).comp
        (continuous_const.prodMk continuous_id)
    continuous_invFun := by
      exact (continuous_realRotorAction I hI_cont).comp
        (continuous_const.prodMk continuous_id) }

@[simp] theorem realRotorHomeomorph_apply
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (hI_cont : Continuous I) (θ : ℝ) (v : V) :
    realRotorHomeomorph I hI hI_cont θ v = realRotorAction I θ v := rfl

@[simp] theorem realRotorHomeomorph_symm_apply
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (hI_cont : Continuous I) (θ : ℝ) (v : V) :
    (realRotorHomeomorph I hI hI_cont θ).symm v =
      realRotorAction I (-θ) v := rfl

end

end InfoGeometry.Canonical
