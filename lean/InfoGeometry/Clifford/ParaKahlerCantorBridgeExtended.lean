import InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge
import Mathlib.Tactic

/-!
# Finite six-channel readout for positive `Gr(2,4)` data

The existing Cantor/Clifford owners provide the five-mode CAR representation,
the positive Grassmannian blade, and the Plücker readout.  This file records
the explicit occupation-address convention that places the six ordered
two-subsets of the first four modes at depth-five addresses
`3, 5, 9, 6, 10, 12`.  It then transports positivity and the Klein quadric
relation to those six coordinates and derives the associated rational face
weight identity.

This is a finite-coordinate readout.  It does not identify the owner spinor
coordinate enumeration with these addresses, nor assert a new measure on the
infinite Cantor boundary.
-/

namespace InfoGeometry.Clifford.ParaKahlerCantorBridgeExtended

noncomputable section

open InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge
open InfoGeometry.Projective.MatrixPluckerPositiveBridge

abbrev Address := Fin 32

/-- The depth-five finite readout of the six `Gr(2,4)` Plücker channels in
the chosen binary occupation convention.  All other coordinates are zero. -/
def bladeCylinderWeight (M : Matrix2x4) (i : Address) : ℝ :=
  match i.val with
  | 3 => matrixPluckerCoords M 0
  | 5 => matrixPluckerCoords M 1
  | 9 => matrixPluckerCoords M 2
  | 6 => matrixPluckerCoords M 3
  | 10 => matrixPluckerCoords M 4
  | 12 => matrixPluckerCoords M 5
  | _ => 0

@[simp] theorem bladeCylinderWeight_three (M : Matrix2x4) :
    bladeCylinderWeight M ⟨3, by omega⟩ = matrixPluckerCoords M 0 := rfl

@[simp] theorem bladeCylinderWeight_five (M : Matrix2x4) :
    bladeCylinderWeight M ⟨5, by omega⟩ = matrixPluckerCoords M 1 := rfl

@[simp] theorem bladeCylinderWeight_nine (M : Matrix2x4) :
    bladeCylinderWeight M ⟨9, by omega⟩ = matrixPluckerCoords M 2 := rfl

@[simp] theorem bladeCylinderWeight_six (M : Matrix2x4) :
    bladeCylinderWeight M ⟨6, by omega⟩ = matrixPluckerCoords M 3 := rfl

@[simp] theorem bladeCylinderWeight_ten (M : Matrix2x4) :
    bladeCylinderWeight M ⟨10, by omega⟩ = matrixPluckerCoords M 4 := rfl

@[simp] theorem bladeCylinderWeight_twelve (M : Matrix2x4) :
    bladeCylinderWeight M ⟨12, by omega⟩ = matrixPluckerCoords M 5 := rfl

/-- The finite readout is supported inside the six declared channels. -/
theorem bladeCylinderWeight_eq_zero_of_not_active
    (M : Matrix2x4) (i : Address)
    (h : i.val ≠ 3 ∧ i.val ≠ 5 ∧ i.val ≠ 9 ∧
      i.val ≠ 6 ∧ i.val ≠ 10 ∧ i.val ≠ 12) :
    bladeCylinderWeight M i = 0 := by
  simp [bladeCylinderWeight, h.1, h.2.1, h.2.2.1,
    h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]

/-- Strict positivity of the chart makes each of the six active readout
coordinates strictly positive. -/
theorem bladeCylinderWeight_active_pos
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    (0 < bladeCylinderWeight M ⟨3, by omega⟩) ∧
    (0 < bladeCylinderWeight M ⟨5, by omega⟩) ∧
    (0 < bladeCylinderWeight M ⟨9, by omega⟩) ∧
    (0 < bladeCylinderWeight M ⟨6, by omega⟩) ∧
    (0 < bladeCylinderWeight M ⟨10, by omega⟩) ∧
    (0 < bladeCylinderWeight M ⟨12, by omega⟩) := by
  have hp := positiveGrassmannianInterior_mem_matrixPluckerPositive M hM
  simpa using ⟨hp 0, hp 1, hp 2, hp 3, hp 4, hp 5⟩

/-- The six-channel readout satisfies the Klein quadric relation. -/
theorem bladeCylinderWeight_klein_relation (M : Matrix2x4) :
    bladeCylinderWeight M ⟨3, by omega⟩ * bladeCylinderWeight M ⟨12, by omega⟩ -
      bladeCylinderWeight M ⟨5, by omega⟩ * bladeCylinderWeight M ⟨10, by omega⟩ +
      bladeCylinderWeight M ⟨9, by omega⟩ * bladeCylinderWeight M ⟨6, by omega⟩ = 0 := by
  simpa [bladeCylinderWeight] using matrixPluckerCoords_klein_relation M

/-- The square-face `X` weight in the chosen six-channel convention. -/
def plabicFaceWeight (M : Matrix2x4) : ℝ :=
  (matrixPluckerCoords M 0 * matrixPluckerCoords M 5) /
    (matrixPluckerCoords M 2 * matrixPluckerCoords M 3)

/-- The Plücker quadric gives the Ptolemy exchange identity for the face
weight whenever its denominator is nonzero. -/
theorem one_add_plabicFaceWeight
    (M : Matrix2x4)
    (hden : matrixPluckerCoords M 2 * matrixPluckerCoords M 3 ≠ 0) :
    1 + plabicFaceWeight M =
      (matrixPluckerCoords M 1 * matrixPluckerCoords M 4) /
        (matrixPluckerCoords M 2 * matrixPluckerCoords M 3) := by
  have hklein := matrixPluckerCoords_klein_relation M
  dsimp [plabicFaceWeight]
  let a := matrixPluckerCoords M 0 * matrixPluckerCoords M 5
  let b := matrixPluckerCoords M 1 * matrixPluckerCoords M 4
  let d := matrixPluckerCoords M 2 * matrixPluckerCoords M 3
  change 1 + a / d = b / d
  have hd : d ≠ 0 := by simpa [d] using hden
  have hsum : d + a = b := by
    dsimp [a, b, d]
    linarith [hklein]
  calc
    1 + a / d = d / d + a / d := by rw [div_self hd]
    _ = (d + a) / d := by rw [add_div]
    _ = b / d := by rw [hsum]

/-- Reciprocal face weight, with its exact algebraic readout.  This records
the rational inversion law; a plabic graph mutation is additional data. -/
theorem plabicFaceWeight_inv
    (M : Matrix2x4) :
    (plabicFaceWeight M)⁻¹ =
      (matrixPluckerCoords M 2 * matrixPluckerCoords M 3) /
        (matrixPluckerCoords M 0 * matrixPluckerCoords M 5) := by
  simp [plabicFaceWeight, div_eq_mul_inv, mul_inv_rev]

end
end InfoGeometry.Clifford.ParaKahlerCantorBridgeExtended
