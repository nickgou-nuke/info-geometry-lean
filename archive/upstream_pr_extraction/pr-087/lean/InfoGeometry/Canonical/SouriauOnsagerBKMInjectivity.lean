import Mathlib

import InfoGeometry.Canonical.SouriauOnsagerBKMStrictPositivity

/-!
# Injectivity of the finite Kubo--Mori transform

The strict BKM pairing gives injectivity without first proving a separate
star-compatibility formula for the transform.  For `X`, use the pairing
`kuboMoriPairing (star X) X`; its trace readout contains
`kuboMoriTransform X` directly.
-/

noncomputable section

namespace SouriauOnsagerBKM

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

theorem FaithfulDensityOperator.kuboMoriTransform_eq_zero_of_eq_zero_pairing
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow)
    (hA : D.kuboMoriTransform A = 0) :
    A = 0 := by
  have hpair :
      (D.kuboMoriPairing (star A) (star A)).re = 0 := by
    rw [D.kuboMoriPairing_eq_trace_kuboMoriTransform (star A) (star A) h_rpow]
    simp [hA, finiteOperatorTrace]
  have hstar : star A = 0 :=
    (D.kuboMoriPairing_self_eq_zero_iff (star A) h_rpow).mp hpair
  exact star_eq_zero.mp hstar

theorem FaithfulDensityOperator.kuboMoriTransformCLM_injective
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    Function.Injective (D.kuboMoriTransformCLM h_rpow) := by
  intro A B hAB
  have hdiffCLM :
      (D.kuboMoriTransformCLM h_rpow) (A - B) = 0 := by
    rw [map_sub, hAB, sub_self]
  have hdiff :
      D.kuboMoriTransform (A - B) = 0 := by
    simpa [D.kuboMoriTransformCLM_apply] using hdiffCLM
  have hzero : A - B = 0 :=
    D.kuboMoriTransform_eq_zero_of_eq_zero_pairing (A - B) h_rpow hdiff
  exact sub_eq_zero.mp hzero

end SouriauOnsagerBKM
