import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment

/-!
# Native obstruction for the proposed third-generator rotation

The current native matrix certificates disprove the proposed equality
`c * pc3Aut * c⁻¹ = pc1Aut`.  We retain the obstruction explicitly instead
of promoting an incompatible coordinate convention.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootAutPC3Conjugation

open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment

theorem not_autMatrix_c_conj_pc3Aut_eq_C0 :
    ¬ autMatrix (c * pc3Aut * c⁻¹) = C0 := by
  intro h
  rw [autMatrix_mul, autMatrix_mul, autMatrix_pc3Aut_eq_C2,
    autMatrix_c, autMatrix_c_inv] at h
  have h02 := congrArg (fun M => M (0 : Fin 8) (2 : Fin 8)) h
  have hneq : ¬
      (((cycle012Matrix * swapCartanMatrix) ^ 5) *
        (C2 * (cycle012Matrix * swapCartanMatrix)))
          (0 : Fin 8) (2 : Fin 8) = C0 0 2 := by
    decide
  exact hneq h02

theorem not_c_conj_pc3Aut_eq_pc1Aut :
    ¬ c * pc3Aut * c⁻¹ = pc1Aut := by
  intro h
  apply not_autMatrix_c_conj_pc3Aut_eq_C0
  rw [h, autMatrix_pc1Aut_eq_C0]

end InfoGeometry.Algebra.Zorn.G2RootAutPC3Conjugation
