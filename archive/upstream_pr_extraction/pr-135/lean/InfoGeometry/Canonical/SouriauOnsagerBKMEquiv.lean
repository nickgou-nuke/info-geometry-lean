import Mathlib

import InfoGeometry.Canonical.SouriauOnsagerBKMInjectivity

/-!
# Canonical finite-dimensional Kubo--Mori equivalence

The finite operator carrier has the same domain and codomain.  Injectivity of
the existing Kubo--Mori continuous linear map therefore upgrades to
surjectivity and a canonical continuous linear equivalence.
-/

noncomputable section

namespace SouriauOnsagerBKM

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

theorem FaithfulDensityOperator.kuboMoriTransformLinear_injective
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    Function.Injective (D.kuboMoriTransformLinear h_rpow) := by
  intro A B hAB
  apply D.kuboMoriTransformCLM_injective h_rpow
  simpa [D.kuboMoriTransformCLM_apply,
    D.kuboMoriTransformLinear_apply] using hAB

theorem FaithfulDensityOperator.kuboMoriTransformCLM_surjective
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    Function.Surjective (D.kuboMoriTransformCLM h_rpow) := by
  have hlin :
      Function.Surjective (D.kuboMoriTransformLinear h_rpow) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
      (D.kuboMoriTransformLinear_injective h_rpow)
  intro B
  obtain ⟨A, hA⟩ := hlin B
  refine ⟨A, ?_⟩
  simpa [D.kuboMoriTransformCLM_apply,
    D.kuboMoriTransformLinear_apply] using hA

/-- The canonical continuous-linear Kubo--Mori equivalence. -/
noncomputable def FaithfulDensityOperator.kuboMoriTransformCLE
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    FiniteOperatorAlgebra n ≃L[ℂ] FiniteOperatorAlgebra n :=
  ContinuousLinearEquiv.ofBijective
    (D.kuboMoriTransformCLM h_rpow)
    (LinearMap.ker_eq_bot.mpr (D.kuboMoriTransformCLM_injective h_rpow))
    (LinearMap.range_eq_top.mpr (D.kuboMoriTransformCLM_surjective h_rpow))

@[simp] theorem FaithfulDensityOperator.kuboMoriTransformCLE_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n) :
    D.kuboMoriTransformCLE h_rpow A = D.kuboMoriTransform A := by
  rfl

/-- The canonical inverse of the finite-dimensional Kubo--Mori transform. -/
noncomputable def FaithfulDensityOperator.inverseKuboMoriCLM
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    FiniteOperatorAlgebra n →L[ℂ] FiniteOperatorAlgebra n :=
  (D.kuboMoriTransformCLE h_rpow).symm

theorem FaithfulDensityOperator.inverseKuboMoriCLM_apply_transform
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n) :
    D.inverseKuboMoriCLM h_rpow (D.kuboMoriTransform A) = A := by
  unfold inverseKuboMoriCLM
  rw [← D.kuboMoriTransformCLE_apply h_rpow A]
  exact (D.kuboMoriTransformCLE h_rpow).symm_apply_apply A

theorem FaithfulDensityOperator.transform_apply_inverseKuboMoriCLM
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n) :
    D.kuboMoriTransform
        (D.inverseKuboMoriCLM h_rpow A) = A := by
  unfold inverseKuboMoriCLM
  exact (D.kuboMoriTransformCLE h_rpow).apply_symm_apply A

end SouriauOnsagerBKM
