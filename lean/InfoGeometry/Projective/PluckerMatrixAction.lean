/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.KleinQuadric
import InfoGeometry.Algebra.FiniteMatrixNoncommutativity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The second compound and the Klein relative invariant

The coefficient ring is commutative, while the four by four matrices are
unrestricted and their multiplication order is preserved. The six coordinates
use the existing order `(01,02,03,12,13,23)`, so the middle Klein term is
`-p02*p13`. The covariance theorem applies to all bivectors, including those
which are not decomposable.

Source: R. Dahm, J. Phys.: Conf. Ser. 2912 (2024), 012036, section 2.
See `docs/DAHM_EXTERIOR_SQUARE_CONTRACT.md` for the source corrections.
-/

namespace InfoGeometry.Projective.PluckerMatrixAction

open Matrix
open InfoGeometry.Projective.KleinQuadric

/-- The six independent increasing pairs, in the existing Plücker order. -/
def coordinatePair : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- Read and reconstruct the existing six-field carrier without a new carrier. -/
def coordinates {R : Type*} : Plucker6 R ≃ (Fin 6 → R) where
  toFun P := ![P.p01, P.p02, P.p03, P.p12, P.p13, P.p23]
  invFun p := ⟨p 0, p 1, p 2, p 3, p 4, p 5⟩
  left_inv P := by cases P; rfl
  right_inv p := by funext i; fin_cases i <;> rfl

section CommRing

variable {K : Type*} [CommRing K]

/-- The second compound matrix: one two by two minor per ordered pair of
independent bivector coordinates. -/
def secondCompound (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 6) (Fin 6) K :=
  fun i j =>
    A (coordinatePair i).1 (coordinatePair j).1 *
        A (coordinatePair i).2 (coordinatePair j).2 -
      A (coordinatePair i).1 (coordinatePair j).2 *
        A (coordinatePair i).2 (coordinatePair j).1

@[simp] theorem secondCompound_one :
    secondCompound (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondCompound, coordinatePair, Matrix.one_apply]

/-- Cauchy–Binet in degree two, with the original matrix order intact. -/
theorem secondCompound_mul (A B : Matrix (Fin 4) (Fin 4) K) :
    secondCompound (A * B) = secondCompound A * secondCompound B := by
  ext i j
  simp [secondCompound, coordinatePair, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- A monoid representation, not an additive map of the matrix algebra. -/
def secondCompoundHom :
    Matrix (Fin 4) (Fin 4) K →* Matrix (Fin 6) (Fin 6) K where
  toFun := secondCompound
  map_one' := secondCompound_one
  map_mul' := secondCompound_mul

/-- The induced action on the existing Plücker carrier. -/
def transform (A : Matrix (Fin 4) (Fin 4) K) (P : Plucker6 K) : Plucker6 K :=
  coordinates.symm (secondCompound A *ᵥ coordinates P)

@[simp] theorem coordinates_transform (A : Matrix (Fin 4) (Fin 4) K)
    (P : Plucker6 K) :
    coordinates (transform A P) = secondCompound A *ᵥ coordinates P :=
  coordinates.apply_symm_apply _

@[simp] theorem transform_one (P : Plucker6 K) :
    transform (1 : Matrix (Fin 4) (Fin 4) K) P = P := by
  apply coordinates.injective
  simp

/-- Successive transformations are composed in their noncommutative order. -/
theorem transform_mul (A B : Matrix (Fin 4) (Fin 4) K) (P : Plucker6 K) :
    transform (A * B) P = transform A (transform B P) := by
  apply coordinates.injective
  simp only [coordinates_transform, secondCompound_mul, Matrix.mulVec_mulVec]

/-- The original four-coordinate carrier acted on by an arbitrary matrix. -/
def transformPoint (A : Matrix (Fin 4) (Fin 4) K) (u : Vec4 K) : Vec4 K :=
  let v := A *ᵥ ![u.x0, u.x1, u.x2, u.x3]
  ⟨v 0, v 1, v 2, v 3⟩

/-- The minor action is the action induced on the wedge of two points. -/
theorem transform_wedge (A : Matrix (Fin 4) (Fin 4) K) (u v : Vec4 K) :
    transform A (Vec4.wedge u v) =
      Vec4.wedge (transformPoint A u) (transformPoint A v) := by
  apply Plucker6.ext <;>
    simp [transform, coordinates, secondCompound, coordinatePair,
      transformPoint, Vec4.wedge, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

theorem transform_add (A : Matrix (Fin 4) (Fin 4) K) (P Q : Plucker6 K) :
    transform A (Plucker6.add P Q) =
      Plucker6.add (transform A P) (transform A Q) := by
  apply Plucker6.ext <;>
    simp [transform, coordinates, secondCompound, coordinatePair, Plucker6.add,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The Klein polynomial is a relative invariant with multiplier `det A`.
No decomposability, invertibility, or commutation hypothesis is imposed. -/
theorem kleinQ_transform (A : Matrix (Fin 4) (Fin 4) K) (P : Plucker6 K) :
    Plucker6.kleinQ (transform A P) = A.det * Plucker6.kleinQ P := by
  have h12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  rw [Matrix.det_succ_row_zero]
  simp [Plucker6.kleinQ, transform, coordinates, secondCompound, coordinatePair,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.det_fin_three,
    h12, h22, h32]
  ring

/-- Polar incidence has the same determinant multiplier. -/
theorem polar_transform (A : Matrix (Fin 4) (Fin 4) K) (P Q : Plucker6 K) :
    Plucker6.polar (transform A P) (transform A Q) =
      A.det * Plucker6.polar P Q := by
  unfold Plucker6.polar
  rw [← transform_add, kleinQ_transform, kleinQ_transform, kleinQ_transform]
  ring

theorem isKlein_transform (A : Matrix (Fin 4) (Fin 4) K) (P : Plucker6 K)
    (hP : Plucker6.IsKlein P) : Plucker6.IsKlein (transform A P) := by
  change Plucker6.kleinQ (transform A P) = 0
  rw [kleinQ_transform, hP, mul_zero]

/-- A nonzero determinant reflects the affine null equation over a domain. -/
theorem isKlein_transform_iff [NoZeroDivisors K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0) (P : Plucker6 K) :
    Plucker6.IsKlein (transform A P) ↔ Plucker6.IsKlein P := by
  change Plucker6.kleinQ (transform A P) = 0 ↔ Plucker6.kleinQ P = 0
  rw [kleinQ_transform, mul_eq_zero]
  simp [hA]

theorem incident_transform_iff [NoZeroDivisors K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0) (P Q : Plucker6 K) :
    Plucker6.Incident (transform A P) (transform A Q) ↔ Plucker6.Incident P Q := by
  change Plucker6.polar (transform A P) (transform A Q) = 0 ↔ Plucker6.polar P Q = 0
  rw [polar_transform, mul_eq_zero]
  simp [hA]

end CommRing

end InfoGeometry.Projective.PluckerMatrixAction
