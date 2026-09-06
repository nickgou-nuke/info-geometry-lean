import InfoGeometry.Canonical.SouriauOnsagerBKMSelfAdjoint
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Continuous self-adjoint BKM equivalence

The self-adjoint Kubo--Mori transform and its inverse are already genuine
continuous linear maps.  This file packages the proved two-sided inverse laws
as Mathlib's native `ContinuousLinearEquiv`.

This is the finite noncommutative Hessian/Legendre linearization on the real
self-adjoint tangent carrier.  No new operator carrier or inverse is defined.
-/

noncomputable section

namespace SouriauOnsagerBKM

variable {n : ℕ}

/-- The restricted Kubo--Mori transform as a real continuous linear
equivalence of the native self-adjoint carrier. -/
noncomputable def FaithfulDensityOperator.restrictedKuboMoriCLE
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    selfAdjoint (FiniteOperatorAlgebra n) ≃L[ℝ]
      selfAdjoint (FiniteOperatorAlgebra n) :=
  ContinuousLinearEquiv.equivOfInverse
    (D.restrictedKuboMoriCLM h_rpow)
    (D.restrictedInverseKuboMoriCLM h_rpow)
    (D.restrictedInverseKuboMoriCLM_apply_restricted h_rpow)
    (D.restrictedKuboMoriCLM_apply_restrictedInverse h_rpow)

@[simp] theorem FaithfulDensityOperator.restrictedKuboMoriCLE_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    D.restrictedKuboMoriCLE h_rpow A =
      D.restrictedKuboMoriCLM h_rpow A :=
  rfl

@[simp] theorem FaithfulDensityOperator.restrictedKuboMoriCLE_symm_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    (D.restrictedKuboMoriCLE h_rpow).symm A =
      D.restrictedInverseKuboMoriCLM h_rpow A :=
  rfl

@[simp] theorem FaithfulDensityOperator.restrictedKuboMoriCLE_symm_apply_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    (D.restrictedKuboMoriCLE h_rpow).symm
        (D.restrictedKuboMoriCLE h_rpow A) = A := by
  exact (D.restrictedKuboMoriCLE h_rpow).symm_apply_apply A

@[simp] theorem FaithfulDensityOperator.restrictedKuboMoriCLE_apply_symm_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    D.restrictedKuboMoriCLE h_rpow
        ((D.restrictedKuboMoriCLE h_rpow).symm A) = A := by
  exact (D.restrictedKuboMoriCLE h_rpow).apply_symm_apply A

/-- The inverse continuous linear map of the BKM Hessian equivalence is
exactly the already-proved restricted inverse Kubo--Mori operator. -/
theorem FaithfulDensityOperator.restrictedKuboMoriCLE_symm_toContinuousLinearMap
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    (D.restrictedKuboMoriCLE h_rpow).symm.toContinuousLinearMap =
      D.restrictedInverseKuboMoriCLM h_rpow := by
  ext A
  rfl

end SouriauOnsagerBKM
