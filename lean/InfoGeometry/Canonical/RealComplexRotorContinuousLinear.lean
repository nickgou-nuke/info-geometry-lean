import Mathlib.Analysis.Normed.Module.FiniteDimension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealComplexRotorHomeomorph

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
variable [FiniteDimensional ℝ V]
variable [T2Space V]

def realRotorLinearMap (I : V →ₗ[ℝ] V) (θ : ℝ) : V →ₗ[ℝ] V where
  toFun := realRotorAction I θ
  map_add' v w := by
    simp [realRotorAction, smul_add, map_add]
    module
  map_smul' c v := by
    simp [realRotorAction, smul_smul, map_smul]
    ring

theorem realRotorLinearMap_apply
    (I : V →ₗ[ℝ] V) (θ : ℝ) (v : V) :
    realRotorLinearMap I θ v = realRotorAction I θ v := rfl

def realRotorLinearEquiv
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (θ : ℝ) : V ≃ₗ[ℝ] V where
  toLinearMap := realRotorLinearMap I θ
  invFun := realRotorAction I (-θ)
  left_inv v := realRotorAction_inverse I hI θ v
  right_inv v := by
    change realRotorAction I θ (realRotorAction I (-θ) v) = v
    rw [realRotorAction_add I hI θ (-θ), add_neg_cancel,
      realRotorAction_zero]

theorem realRotorLinearEquiv_apply
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (θ : ℝ) (v : V) :
    realRotorLinearEquiv I hI θ v = realRotorAction I θ v := rfl

def realRotorContinuousLinearEquiv
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (hI_cont : Continuous I) (θ : ℝ) : V ≃L[ℝ] V :=
  (realRotorLinearEquiv I hI θ).toContinuousLinearEquiv

theorem realRotorContinuousLinearEquiv_apply
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (hI_cont : Continuous I) (θ : ℝ) (v : V) :
    realRotorContinuousLinearEquiv I hI hI_cont θ v =
      realRotorAction I θ v := by
  change realRotorLinearEquiv I hI θ v = _
  rfl

end

end InfoGeometry.Canonical
