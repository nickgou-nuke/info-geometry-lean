import InfoGeometry.Physics.KreinDiracKasparovSpinorBilinear
import InfoGeometry.Algebra.IdempotentCornerCommutant
import InfoGeometry.Clifford.OperatorValuedJones
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace InfoGeometry.CliffordWeyl.KreinIdealBilinears

open InfoGeometry.Physics
open InfoGeometry.Algebra.IdempotentCornerCommutant

variable {Carrier : Type*} [Ring Carrier] [StarRing Carrier]
variable (geometry : KasparovKreinData Carrier)

theorem adjoint_maps_left_ideal (projection : Carrier) :
    Set.MapsTo geometry.diracAdjoint (principalLeftIdeal projection)
      (principalRightIdeal (geometry.diracAdjoint projection)) := by
  intro spinor supported
  change geometry.diracAdjoint projection * geometry.diracAdjoint spinor =
    geometry.diracAdjoint spinor
  change spinor * projection = spinor at supported
  rw [← geometry.diracAdjoint_mul, supported]

theorem adjoint_maps_right_ideal (projection : Carrier) :
    Set.MapsTo geometry.diracAdjoint (principalRightIdeal projection)
      (principalLeftIdeal (geometry.diracAdjoint projection)) := by
  intro spinor supported
  change geometry.diracAdjoint spinor * geometry.diracAdjoint projection =
    geometry.diracAdjoint spinor
  change projection * spinor = spinor at supported
  rw [← geometry.diracAdjoint_mul, supported]

def sandwich (left insertion right : Carrier) : Carrier :=
  geometry.diracAdjoint left * insertion * right

theorem sandwich_supported (leftProjection rightProjection left insertion right : Carrier)
    (leftSupported : left ∈ principalLeftIdeal leftProjection)
    (rightSupported : right ∈ principalLeftIdeal rightProjection) :
    geometry.diracAdjoint leftProjection * geometry.sandwich left insertion right *
      rightProjection = geometry.sandwich left insertion right := by
  have adjointSupported := adjoint_maps_left_ideal geometry leftProjection leftSupported
  change geometry.diracAdjoint leftProjection * geometry.diracAdjoint left =
    geometry.diracAdjoint left at adjointSupported
  change right * rightProjection = right at rightSupported
  unfold sandwich
  calc
    geometry.diracAdjoint leftProjection *
        (geometry.diracAdjoint left * insertion * right) * rightProjection =
        (geometry.diracAdjoint leftProjection * geometry.diracAdjoint left) *
          insertion * (right * rightProjection) := by simp only [mul_assoc]
    _ = geometry.diracAdjoint left * insertion * right := by
      rw [adjointSupported, rightSupported]

theorem adjoint_sandwich (left insertion right : Carrier) :
    geometry.diracAdjoint (geometry.sandwich left insertion right) =
      geometry.sandwich right (geometry.diracAdjoint insertion) left := by
  simp only [sandwich, geometry.diracAdjoint_mul,
    geometry.diracAdjoint_involution, mul_assoc]

theorem sandwich_add_insertion (left first second right : Carrier) :
    geometry.sandwich left (first + second) right =
      geometry.sandwich left first right + geometry.sandwich left second right := by
  simp only [sandwich, mul_add, add_mul]

theorem jones_coordinates_reconstruct_sandwich
    {Coefficient : Type*} [Ring Coefficient] [StarRing Coefficient] [Algebra ℂ Coefficient]
    (sheetGeometry : KasparovKreinData (Matrix (Fin 2) (Fin 2) Coefficient))
    (left insertion right : Matrix (Fin 2) (Fin 2) Coefficient) :
    InfoGeometry.Clifford.reconstruct_causal
      (InfoGeometry.Clifford.causalCoordinates
        (sheetGeometry.sandwich left insertion right)) =
      sheetGeometry.sandwich left insertion right := by
  exact InfoGeometry.Clifford.reconstruct_causalCoordinates _

end InfoGeometry.CliffordWeyl.KreinIdealBilinears
