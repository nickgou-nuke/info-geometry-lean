import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Canonical.ZornQuadraticGaugeVariation

open InfoGeometry.Algebra

abbrev Zorn := ZornVectorMatrix ℝ

/-! These definitions use the native non-associative Zorn product.  In
particular, no `Ring Zorn` instance is introduced. -/

def deltaQuadratic (F Λ : Zorn) : Zorn :=
  ZornVectorMatrix.add
    (ZornVectorMatrix.mul (ZornVectorMatrix.commutator F Λ) F)
    (ZornVectorMatrix.mul F (ZornVectorMatrix.commutator F Λ))

theorem deltaQuadratic_decomposition (F Λ : Zorn) :
    deltaQuadratic F Λ =
      ZornVectorMatrix.add
        (ZornVectorMatrix.sub
          (ZornVectorMatrix.sub
            (ZornVectorMatrix.associator F Λ F)
            (ZornVectorMatrix.associator F F Λ))
          (ZornVectorMatrix.associator Λ F F))
        (ZornVectorMatrix.commutator (ZornVectorMatrix.mul F F) Λ) := by
  dsimp [deltaQuadratic, ZornVectorMatrix.associator, ZornVectorMatrix.commutator]
  rw [ZornVectorMatrix.sub_mul, ZornVectorMatrix.mul_sub]
  change (ZornVectorMatrix.mul (ZornVectorMatrix.mul F Λ) F) - (ZornVectorMatrix.mul (ZornVectorMatrix.mul Λ F) F) +
         ((ZornVectorMatrix.mul F (ZornVectorMatrix.mul F Λ)) - (ZornVectorMatrix.mul F (ZornVectorMatrix.mul Λ F))) =
         (((ZornVectorMatrix.mul (ZornVectorMatrix.mul F Λ) F - ZornVectorMatrix.mul F (ZornVectorMatrix.mul Λ F)) -
           (ZornVectorMatrix.mul (ZornVectorMatrix.mul F F) Λ - ZornVectorMatrix.mul F (ZornVectorMatrix.mul F Λ))) -
          (ZornVectorMatrix.mul (ZornVectorMatrix.mul Λ F) F - ZornVectorMatrix.mul Λ (ZornVectorMatrix.mul F F))) +
         (ZornVectorMatrix.mul (ZornVectorMatrix.mul F F) Λ - ZornVectorMatrix.mul Λ (ZornVectorMatrix.mul F F))
  abel

end InfoGeometry.Canonical.ZornQuadraticGaugeVariation
