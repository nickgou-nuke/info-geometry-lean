import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Topology.KleinQuotientDeckInvariants

/-!
# Exterior-algebra readout of the Klein glide orientation character

The Klein deck glide acts on the two-dimensional covering vector space by
`diag (-1, 1)`.  Functoriality of the exterior algebra lifts this linear map
to an algebra automorphism.  On the top exterior generator the lift acts by
the determinant, hence by `-1`; applying the glide twice acts trivially.

This records the orientation character of the already specified Klein deck
action in the exterior-algebra carrier.  It does not claim that graded
commutativity alone constructs the Klein-bottle quotient.
-/

namespace InfoGeometry.Topology.KleinBottleExteriorOrientationBridge

open InfoGeometry.Topology.KleinQuotientDeckInvariants

abbrev PlaneVector := Fin 2 → ℝ

/-- The linear part of the orientation-reversing Klein deck glide. -/
def glideLinear : PlaneVector →ₗ[ℝ] PlaneVector :=
  Matrix.mulVecLin deckB_diff

/-- The first coordinate basis vector of the covering plane. -/
def firstAxis : PlaneVector := fun i => if i = 0 then 1 else 0

/-- The second coordinate basis vector of the covering plane. -/
def secondAxis : PlaneVector := fun i => if i = 1 then 1 else 0

@[simp] theorem glideLinear_firstAxis :
    glideLinear firstAxis = -firstAxis := by
  ext i
  fin_cases i <;>
    simp [glideLinear, firstAxis, deckB_diff, Matrix.mulVec, dotProduct]

@[simp] theorem glideLinear_secondAxis :
    glideLinear secondAxis = secondAxis := by
  ext i
  fin_cases i <;>
    simp [glideLinear, secondAxis, deckB_diff, Matrix.mulVec, dotProduct]

/-- The exterior-algebra map induced by the linear part of the Klein glide. -/
def glideExterior : ExteriorAlgebra ℝ PlaneVector →ₐ[ℝ]
    ExteriorAlgebra ℝ PlaneVector :=
  ExteriorAlgebra.map glideLinear

@[simp] theorem glideExterior_generator (v : PlaneVector) :
    glideExterior (ExteriorAlgebra.ι ℝ v) =
      ExteriorAlgebra.ι ℝ (glideLinear v) := by
  exact ExteriorAlgebra.map_apply_ι glideLinear v

/-- The top exterior generator changes sign under the orientation-reversing glide. -/
theorem glideExterior_topForm :
    glideExterior (ExteriorAlgebra.ι ℝ firstAxis *
      ExteriorAlgebra.ι ℝ secondAxis) =
        -(ExteriorAlgebra.ι ℝ firstAxis * ExteriorAlgebra.ι ℝ secondAxis) := by
  rw [map_mul, glideExterior_generator, glideExterior_generator,
    glideLinear_firstAxis, glideLinear_secondAxis]
  simp

/-- The linear glide is an involution on the covering vector space. -/
theorem glideLinear_involutive (v : PlaneVector) :
    glideLinear (glideLinear v) = v := by
  ext i
  fin_cases i <;>
    simp [glideLinear, deckB_diff, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The induced exterior-algebra automorphism squares to the identity. -/
theorem glideExterior_involutive :
    AlgHom.comp glideExterior glideExterior =
      AlgHom.id ℝ (ExteriorAlgebra ℝ PlaneVector) := by
  apply ExteriorAlgebra.hom_ext
  ext v
  simp [glideExterior, glideLinear_involutive]

end InfoGeometry.Topology.KleinBottleExteriorOrientationBridge
