import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.GroupTheory.G2BruhatInversions

namespace InfoGeometry.Algebra.Zorn.G2BruhatResidualLengthOne

open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.GroupTheory.G2BruhatInversions

theorem first_simple_length :
    dihedralLength (0, true) = 1 := by
  decide

theorem second_simple_length :
    dihedralLength (1, true) = 1 := by
  decide

theorem first_simple_residual_exponent_card :
    Fintype.card (BruhatResidualExponent (0, true)) = 2 := by
  rw [bruhatResidualExponent_card, first_simple_length]
  norm_num

theorem second_simple_residual_exponent_card :
    Fintype.card (BruhatResidualExponent (1, true)) = 2 := by
  rw [bruhatResidualExponent_card, second_simple_length]
  norm_num

end InfoGeometry.Algebra.Zorn.G2BruhatResidualLengthOne
