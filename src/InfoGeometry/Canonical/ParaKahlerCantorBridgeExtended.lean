import Mathlib
import InfoGeometry.Clifford.Cl55CantorL2VectorIntertwiner
import InfoGeometry.Clifford.Cl55NambuCARBridge
import InfoGeometry.Projective.MatrixPluckerPositiveBridge

/-!
# Plücker face coordinate on the six active `Gr(2,4)` channels

The five-mode CAR and the finite spinor-to-Cantor `L²` map are already owned
by `Cl55NambuCARBridge` and `Cl55CantorL2VectorIntertwiner`; this file does not
restate them.  It proves the ratio identity that follows from the Klein
quadric.  The reciprocal coordinate is named algebraically; no plabic graph
mutation or urban-renewal action is asserted without an owner for that action.
-/

namespace InfoGeometry.Canonical.ParaKahlerCantorBridgeExtended

open InfoGeometry.Projective.MatrixPluckerPositiveBridge

/-- The Plücker quadratic equation in the standard six-coordinate ordering. -/
def KleinPluckerRelation {F : Type*} [Ring F] (p : Fin 6 → F) : Prop :=
  p 0 * p 5 - p 1 * p 4 + p 2 * p 3 = 0

/-- The square-face ratio on the six Plücker coordinates, when the denominator
is invertible. -/
def plabicFaceWeight {F : Type*} [Field F] (p : Fin 6 → F) : F :=
  (p 0 * p 5) * (p 2 * p 3)⁻¹

/-- The Plücker quadric rewrites the face ratio as the usual Ptolemy sum. -/
theorem one_add_plabicFaceWeight {F : Type*} [Field F]
    (p : Fin 6 → F) (hK : KleinPluckerRelation p)
    (hden : p 2 * p 3 ≠ 0) :
    1 + plabicFaceWeight p = (p 1 * p 4) * (p 2 * p 3)⁻¹ := by
  have hsum : p 1 * p 4 = p 0 * p 5 + p 2 * p 3 := by
    dsimp [KleinPluckerRelation] at hK
    linear_combination -hK
  dsimp [plabicFaceWeight]
  calc
    1 + (p 0 * p 5) * (p 2 * p 3)⁻¹ =
        (p 2 * p 3) * (p 2 * p 3)⁻¹ + (p 0 * p 5) * (p 2 * p 3)⁻¹ := by
          rw [mul_inv_cancel₀ hden]
    _ = (p 0 * p 5 + p 2 * p 3) * (p 2 * p 3)⁻¹ := by ring
    _ = (p 1 * p 4) * (p 2 * p 3)⁻¹ := by rw [← hsum]

/-- Inverting the face ratio exchanges numerator and denominator. -/
theorem plabicFaceWeight_inv {F : Type*} [Field F] (p : Fin 6 → F) :
    (plabicFaceWeight p)⁻¹ = (p 2 * p 3) * (p 0 * p 5)⁻¹ := by
  simp [plabicFaceWeight, mul_inv_rev]

/-- The matrix Plücker coordinates satisfy the Klein relation in the same
coordinate order used by the six Cantor channels. -/
theorem matrixKleinPluckerRelation (M : Matrix2x4) :
    KleinPluckerRelation (matrixPluckerCoords M) :=
  matrixPluckerCoords_klein_relation M

/-- On the positive Grassmannian chart, the face-weight denominator is
nonzero, so the Ptolemy identity applies. -/
theorem positiveChart_faceWeight_ptolemy
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    1 + plabicFaceWeight (matrixPluckerCoords M) =
      (matrixPluckerCoords M 1 * matrixPluckerCoords M 4) *
        (matrixPluckerCoords M 2 * matrixPluckerCoords M 3)⁻¹ := by
  have hp := positiveGrassmannianInterior_mem_matrixPluckerPositive M hM
  apply one_add_plabicFaceWeight (matrixPluckerCoords M)
    (matrixKleinPluckerRelation M)
  exact ne_of_gt (mul_pos (hp 2) (hp 3))

end InfoGeometry.Canonical.ParaKahlerCantorBridgeExtended
