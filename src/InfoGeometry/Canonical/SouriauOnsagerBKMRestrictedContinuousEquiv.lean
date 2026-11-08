import InfoGeometry.Canonical.SouriauOnsagerBKMSelfAdjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section

namespace SouriauOnsagerBKM

variable {n : ℕ}

noncomputable def FaithfulDensityOperator.restrictedKuboMoriCLE
    (D : FaithfulDensityOperator n) (h_rpow : Continuous D.rpow) :
    selfAdjoint (FiniteOperatorAlgebra n) ≃L[ℝ]
      selfAdjoint (FiniteOperatorAlgebra n) :=
  ContinuousLinearEquiv.equivOfInverse
    (D.restrictedKuboMoriCLM h_rpow)
    (D.restrictedInverseKuboMoriCLM h_rpow)
    (D.restrictedInverseKuboMoriCLM_apply_restricted h_rpow)
    (D.restrictedKuboMoriCLM_apply_restrictedInverse h_rpow)

@[simp] theorem FaithfulDensityOperator.restrictedKuboMoriCLE_apply
    (D : FaithfulDensityOperator n) (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    D.restrictedKuboMoriCLE h_rpow A = D.restrictedKuboMoriCLM h_rpow A := rfl

@[simp] theorem FaithfulDensityOperator.restrictedKuboMoriCLE_symm_apply
    (D : FaithfulDensityOperator n) (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    (D.restrictedKuboMoriCLE h_rpow).symm A =
      D.restrictedInverseKuboMoriCLM h_rpow A := rfl

@[simp] theorem FaithfulDensityOperator.restrictedKuboMoriCLE_symm_apply_apply
    (D : FaithfulDensityOperator n) (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    (D.restrictedKuboMoriCLE h_rpow).symm
        (D.restrictedKuboMoriCLE h_rpow A) = A := by
  exact (D.restrictedKuboMoriCLE h_rpow).symm_apply_apply A

@[simp] theorem FaithfulDensityOperator.restrictedKuboMoriCLE_apply_symm_apply
    (D : FaithfulDensityOperator n) (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    D.restrictedKuboMoriCLE h_rpow ((D.restrictedKuboMoriCLE h_rpow).symm A) = A := by
  exact (D.restrictedKuboMoriCLE h_rpow).apply_symm_apply A

theorem FaithfulDensityOperator.restrictedKuboMoriCLE_symm_toContinuousLinearMap
    (D : FaithfulDensityOperator n) (h_rpow : Continuous D.rpow) :
    (D.restrictedKuboMoriCLE h_rpow).symm.toContinuousLinearMap =
      D.restrictedInverseKuboMoriCLM h_rpow := by
  ext A
  rfl

end SouriauOnsagerBKM
