import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl

/-!
# Explicit two-by-two operator coefficients in the chiral Zorn carrier

The generic operator-valued Zorn calculus is specialized here to
`A = Matrix (Fin 2) (Fin 2) ℂ`.  Thus every scalar Zorn coordinate is a
two-by-two operator matrix, while each `sigmaPlus`/`sigmaMinus` input is a
three-component vector of such matrices.
-/

namespace InfoGeometry.Canonical.TwoSheetOperatorZornChannels

open InfoGeometry.Canonical

abbrev Matrix2C :=
  InfoGeometry.Canonical.TwoSheetThreeColorWeyl.Mat2C

theorem sigma_plus_matrix2_mul_sigma_plus_matrix2
    (U V : Fin 3 → Matrix2C) :
    operatorZornMul (sigmaPlus U) (sigmaPlus V) =
      sigmaMinus (operatorCross U V) := by
  exact sigmaPlus_mul_sigmaPlus U V

theorem sigma_minus_matrix2_mul_sigma_minus_matrix2
    (U V : Fin 3 → Matrix2C) :
    operatorZornMul (sigmaMinus U) (sigmaMinus V) =
      sigmaPlus (-operatorCross U V) := by
  exact sigmaMinus_mul_sigmaMinus U V

theorem mixed_matrix2_chiral_product
    (U V : Fin 3 → Matrix2C) :
    operatorZornMul (sigmaPlus U) (sigmaMinus V) =
      nPlus (operatorDot U V) := by
  exact sigmaPlus_mul_sigmaMinus U V

theorem matrix2_chiral_zorn_square
    (U V : Fin 3 → Matrix2C) :
    operatorZornMul (chiralOperatorZorn U V)
      (chiralOperatorZorn U V) =
      ⟨operatorDot U V, operatorDot V U,
        -operatorCross V V, operatorCross U U⟩ := by
  exact operatorZornMul_chiralOperatorZorn U V

end InfoGeometry.Canonical.TwoSheetOperatorZornChannels
