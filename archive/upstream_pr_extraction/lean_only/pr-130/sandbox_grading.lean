import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
import InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
import InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
import InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow
import InfoGeometry.Lie.SplitOctonionDiagEllFlowDecomposition

open InfoGeometry.Canonical
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
open InfoGeometry.Lie.SplitOctonionEllFlowOperator
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
open InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow

namespace InfoGeometry.Lie.SplitOctonionCircularZ3Grading

def circularGrade : Fin 8 → ZMod 3
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 0

theorem ellCommutator_not_derivation :
    ¬ ∀ X Y : CZ, ellCommutator (X * Y) = ellCommutator X * Y + X * ellCommutator Y := by
  sorry

theorem hyperbolicFlowZorn_not_mul_of_ne_zero (t : ℝ) (ht : t ≠ 0) :
    ¬ ∀ X Y : CZ, hyperbolicFlowZorn t (X * Y) = hyperbolicFlowZorn t X * hyperbolicFlowZorn t Y := by
  sorry

end InfoGeometry.Lie.SplitOctonionCircularZ3Grading
