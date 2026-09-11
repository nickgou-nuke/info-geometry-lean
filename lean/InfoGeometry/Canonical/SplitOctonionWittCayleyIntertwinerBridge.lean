import InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge

/-!
# Coordinate intertwining for the sectorwise Cayley readout

The coordinate carrier `(a,v,φ,d)` and the `Mat8` Peirce carrier use the same
ordered slots.  This owner proves the explicit intertwining theorem between
the coordinate Cayley conjugation and the sectorwise matrix
`S P_parallel - P_perp`.  It does not identify either operator with
split-octonion multiplication.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionWittCayleyIntertwinerBridge

open Matrix
open InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge
open InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge
open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
open InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge

abbrev Coord := Exterior3Coordinates
abbrev Carrier := PeirceCarrier
abbrev Mat8 := InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge.Mat8

/-- The coordinate matrix of Cayley conjugation in the Peirce slot order. -/
def coordinateCayleyMat : Mat8 :=
  ![![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1]]

theorem sectorwiseCayleyMat_eq_coordinateCayleyMat :
    sectorwiseCayleyMat = coordinateCayleyMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, coordinateCayleyMat,
      longitudinalProjectorMat, transverseProjectorMat,
      longitudinalTransverseMat, exchangeInvolutionMat,
      Matrix.mul_apply, Fin.sum_univ_eight] <;> norm_num

theorem toPeirce_cayleyConj (x : Coord) :
    toPeirce (cayleyConj x) =
      coordinateCayleyMat *ᵥ toPeirce x := by
  ext i
  fin_cases i <;>
    simp [toPeirce, cayleyConj, coordinateCayleyMat,
      Matrix.mulVec, Fin.sum_univ_eight]

theorem toPeirce_middleSignFlip (x : Coord) :
    toPeirce (middleSignFlip x) =
      longitudinalTransverseMat *ᵥ toPeirce x := by
  ext i
  fin_cases i <;>
    simp [toPeirce, middleSignFlip, longitudinalTransverseMat,
      Matrix.mulVec, Fin.sum_univ_eight]

theorem sectorwiseCayleyMat_intertwines (x : Coord) :
    toPeirce (cayleyConj x) =
      sectorwiseCayleyMat *ᵥ toPeirce x := by
  rw [sectorwiseCayleyMat_eq_coordinateCayleyMat]
  exact toPeirce_cayleyConj x

end InfoGeometry.Canonical.SplitOctonionWittCayleyIntertwinerBridge
