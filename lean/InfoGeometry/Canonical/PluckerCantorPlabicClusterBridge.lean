import Mathlib
import InfoGeometry.Canonical.ParaKahlerCantorBridge32
import InfoGeometry.Topology.PlabicCluster

/-!
# Plücker sectors and the plabic square-face coordinate

This module reads the six coefficients of the existing depth-five Cantor
Plücker state as the six `Gr(2,4)` coordinates, then specializes the existing
plabic Ptolemy and square-mutation laws to those coefficients.  It does not
introduce a second Cantor model or a second mutation operation.
-/

namespace InfoGeometry.Canonical.PluckerCantorPlabicClusterBridge

open InfoGeometry.Canonical.ParaKahlerCantorBridge32
open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.PlabicCluster

/-- Real coefficient read from the actual normalized Cantor cylinder vector. -/
noncomputable def cantorSectorReadout (M : Matrix2x4) (i : Fin 6) : ℝ :=
  (inner ℂ (cylinderVector5 (pluckerAddress i)) (pluckerCantorState M)).re

/-- The (L^2) channel coefficient is exactly the corresponding matrix
Plücker coordinate. -/
theorem cantorSectorReadout_eq (M : Matrix2x4) (i : Fin 6) :
    cantorSectorReadout M i = matrixPluckerCoords M i := by
  simp [cantorSectorReadout, pluckerCantorState_channel_coefficient]

/-- Every actual Cantor `L²` channel coefficient is strictly positive on the
positive Grassmannian interior.  This transports positivity through the
normalized cylinder readout rather than assuming positivity of the readout. -/
theorem cantorSectorReadout_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    0 < cantorSectorReadout M i := by
  rw [cantorSectorReadout_eq]
  exact positiveGrassmannianInterior_mem_matrixPluckerPositive M hM i

/-- The central-face ratio read from the six Cantor Plücker channels.  With
the repository's `Fin 6` order this is `c₃ c₁₂ / (c₉ c₆)`. -/
noncomputable def cantorPlabicFaceWeight (M : Matrix2x4) : ℝ :=
  (cantorSectorReadout M 0 * cantorSectorReadout M 5) *
    (cantorSectorReadout M 2 * cantorSectorReadout M 3)⁻¹

/-- Reading the Cantor coefficient ratio gives the named Plücker ratio. -/
theorem cantorPlabicFaceWeight_eq_pluckerRatio (M : Matrix2x4) :
    cantorPlabicFaceWeight M =
      (matrixPluckerCoords M 0 * matrixPluckerCoords M 5) *
        (matrixPluckerCoords M 2 * matrixPluckerCoords M 3)⁻¹ := by
  simp [cantorPlabicFaceWeight, cantorSectorReadout_eq]

/-- The face coordinate read from the Cantor `L²` state is positive on the
positive Grassmannian chart. -/
theorem cantorPlabicFaceWeight_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    0 < cantorPlabicFaceWeight M := by
  dsimp [cantorPlabicFaceWeight]
  exact mul_pos
    (mul_pos (cantorSectorReadout_pos M hM 0)
      (cantorSectorReadout_pos M hM 5))
    (inv_pos.mpr (mul_pos (cantorSectorReadout_pos M hM 2)
      (cantorSectorReadout_pos M hM 3)))

private theorem cantor_plucker_exchange (M : Matrix2x4) :
    matrixPluckerCoords M 1 * matrixPluckerCoords M 4 =
      matrixPluckerCoords M 0 * matrixPluckerCoords M 5 +
        matrixPluckerCoords M 2 * matrixPluckerCoords M 3 := by
  have h := matrixPluckerCoords_klein_relation M
  linear_combination -h

private theorem cantor_face_denominator_ne_zero (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    matrixPluckerCoords M 2 * matrixPluckerCoords M 3 ≠ 0 := by
  have hp := positiveGrassmannianInterior_mem_matrixPluckerPositive M hM
  exact mul_ne_zero (ne_of_gt (hp 2)) (ne_of_gt (hp 3))

private theorem cantor_face_numerator_ne_zero (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    matrixPluckerCoords M 0 * matrixPluckerCoords M 5 ≠ 0 := by
  have hp := positiveGrassmannianInterior_mem_matrixPluckerPositive M hM
  exact mul_ne_zero (ne_of_gt (hp 0)) (ne_of_gt (hp 5))

/-- The Plücker quadric gives the square-face Ptolemy exchange formula on the
actual six Cantor channel coefficients. -/
theorem one_add_cantorPlabicFaceWeight (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    1 + cantorPlabicFaceWeight M =
      (matrixPluckerCoords M 1 * matrixPluckerCoords M 4) *
        (matrixPluckerCoords M 2 * matrixPluckerCoords M 3)⁻¹ := by
  rw [cantorPlabicFaceWeight_eq_pluckerRatio]
  exact ptolemy_face_weight_add_one
    (matrixPluckerCoords M 1) (matrixPluckerCoords M 4)
    (matrixPluckerCoords M 0) (matrixPluckerCoords M 2)
    (matrixPluckerCoords M 5) (matrixPluckerCoords M 3)
    (cantor_plucker_exchange M) (cantor_face_denominator_ne_zero M hM)

/-- Instantiate the owner square-mutation law with the Cantor/Plücker face
coordinate.  The four neighboring X-coordinates are set to the unit only
because this theorem reads the central coordinate, which is independent of
them; no neighboring face data is asserted by this specialization. -/
noncomputable def cantorFaceNeighborhood (M : Matrix2x4) : SquareFaceWeights ℝ where
  yf := cantorPlabicFaceWeight M
  y1 := 1
  y2 := 1
  y3 := 1
  y4 := 1

/-- Urban renewal inverts the central face coordinate after reading it from
the six Cantor Plücker sectors. -/
theorem cantorFace_mutates_to_inverse (M : Matrix2x4) :
    (mutateF (cantorFaceNeighborhood M)).yf =
      (cantorPlabicFaceWeight M)⁻¹ := by
  exact square_move_central_inversion (cantorFaceNeighborhood M)

/-- The inverse face coordinate is the reversed Plücker ratio, with
nonvanishing guaranteed on the positive Grassmannian chart. -/
theorem cantorFace_inverse_ratio (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    (cantorPlabicFaceWeight M)⁻¹ =
      (matrixPluckerCoords M 2 * matrixPluckerCoords M 3) *
        (matrixPluckerCoords M 0 * matrixPluckerCoords M 5)⁻¹ := by
  rw [cantorPlabicFaceWeight_eq_pluckerRatio]
  exact ptolemy_face_weight_inv
    (matrixPluckerCoords M 0) (matrixPluckerCoords M 2)
    (matrixPluckerCoords M 5) (matrixPluckerCoords M 3)
    (cantor_face_numerator_ne_zero M hM) (cantor_face_denominator_ne_zero M hM)

end InfoGeometry.Canonical.PluckerCantorPlabicClusterBridge
