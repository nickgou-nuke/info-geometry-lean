import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

/-!
# Peirce grading and exchange on the `1 + 3 + 3 + 1` coordinate carrier

The existing coordinate bridge provides a graded-vector-space readout of the
Peirce carrier.  This owner adds the two distinct involutions: the diagonal
Peirce grading and the exchange of the two chiral halves.  It does not claim
that the coordinate carrier is already an `ExteriorAlgebra`, nor that either
map is a split-octonion multiplication operator.
-/

namespace InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

abbrev Carrier := PeirceCarrier

def peirceGrading : Carrier →ₗ[ℝ] Carrier where
  toFun x := ![x 0, x 1, x 2, x 3, -x 4, -x 5, -x 6, -x 7]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp

def chiralExchange : Carrier →ₗ[ℝ] Carrier where
  toFun x := ![x 4, x 5, x 6, x 7, x 0, x 1, x 2, x 3]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp

@[simp] theorem peirceGrading_sq (x : Carrier) :
    peirceGrading (peirceGrading x) = x := by
  ext i
  fin_cases i <;> simp [peirceGrading]

@[simp] theorem chiralExchange_sq (x : Carrier) :
    chiralExchange (chiralExchange x) = x := by
  ext i
  fin_cases i <;> simp [chiralExchange]

theorem chiralExchange_grading_anticomm (x : Carrier) :
    chiralExchange (peirceGrading x) =
      -peirceGrading (chiralExchange x) := by
  ext i
  fin_cases i <;> simp [peirceGrading, chiralExchange]

theorem peirceExterior3Equiv_is_coordinate_readout
    (x : Exterior3Coordinates) :
    peirceExterior3Equiv x = toPeirce x :=
  peirceExterior3Equiv_apply x

end InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge
