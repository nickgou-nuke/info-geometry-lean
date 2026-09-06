import InfoGeometry.Canonical.SouriauOnsagerBKMSelfAdjoint
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

noncomputable section

namespace SouriauOnsagerBKM

variable {n : ℕ}

/-- The Kubo--Mori transform restricted to Mathlib's native real self-adjoint
carrier.  No parallel tangent-space type is introduced. -/
noncomputable def FaithfulDensityOperator.restrictedKuboMoriCLM
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    selfAdjoint (FiniteOperatorAlgebra n) →L[ℝ]
      selfAdjoint (FiniteOperatorAlgebra n) := by
  let ΩR : FiniteOperatorAlgebra n →L[ℝ] FiniteOperatorAlgebra n :=
    (D.kuboMoriTransformCLM h_rpow).restrictScalars ℝ
  exact ΩR.restrict (p := selfAdjoint.submodule ℝ (FiniteOperatorAlgebra n))
    (q := selfAdjoint.submodule ℝ (FiniteOperatorAlgebra n)) (by
      intro A hA
      change star (D.kuboMoriTransform A) = D.kuboMoriTransform A
      exact D.kuboMoriTransform_preserves_selfAdjoint h_rpow A hA)

@[simp] theorem FaithfulDensityOperator.restrictedKuboMoriCLM_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    ((D.restrictedKuboMoriCLM h_rpow A :
      selfAdjoint (FiniteOperatorAlgebra n)) : FiniteOperatorAlgebra n) =
      D.kuboMoriTransform (A : FiniteOperatorAlgebra n) := by
  rfl

end SouriauOnsagerBKM
