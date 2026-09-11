import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Projective.Quadrics.PluckerKlein

Coordinate Plücker relation for the Klein quadric.

This file proves the finite algebraic core:

If `pᵢⱼ = xᵢ yⱼ - xⱼ yᵢ` are the Plücker coordinates of a decomposable
2-vector `x ∧ y` in `R⁴`, then

  `p01 * p23 - p02 * p13 + p03 * p12 = 0`.

No Grassmannian scheme.
No Schubert calculus.
No Hodge-star wrapper.
No axiom.
-/

namespace InfoGeometry.Projective.Quadrics.PluckerKlein

variable {R : Type*} [CommRing R]

/-- Coordinate model for `R⁴`. -/
abbrev Vec4 (R : Type*) :=
  Fin 4 → R

/-- Plücker coordinate `pᵢⱼ = xᵢ yⱼ - xⱼ yᵢ`. -/
def pluckerCoord (x y : Vec4 R) (i j : Fin 4) : R :=
  x i * y j - x j * y i

/-- The Plücker coordinate vanishes on repeated indices. -/
@[simp]
theorem pluckerCoord_self
    (x y : Vec4 R) (i : Fin 4) :
    pluckerCoord x y i i = 0 := by
  unfold pluckerCoord
  ring

/-- Plücker coordinates are antisymmetric. -/
theorem pluckerCoord_swap
    (x y : Vec4 R) (i j : Fin 4) :
    pluckerCoord x y j i = - pluckerCoord x y i j := by
  unfold pluckerCoord
  ring

/-- Scaling the first vector scales all Plücker coordinates. -/
theorem pluckerCoord_smul_left
    (a : R) (x y : Vec4 R) (i j : Fin 4) :
    pluckerCoord (fun k => a * x k) y i j =
      a * pluckerCoord x y i j := by
  unfold pluckerCoord
  ring

/-- Scaling the second vector scales all Plücker coordinates. -/
theorem pluckerCoord_smul_right
    (a : R) (x y : Vec4 R) (i j : Fin 4) :
    pluckerCoord x (fun k => a * y k) i j =
      a * pluckerCoord x y i j := by
  unfold pluckerCoord
  ring

/-- Scaling both vectors scales all Plücker coordinates by the product of scalars. -/
theorem pluckerCoord_smul_both
    (a b : R) (x y : Vec4 R) (i j : Fin 4) :
    pluckerCoord (fun k => a * x k) (fun k => b * y k) i j =
      (a * b) * pluckerCoord x y i j := by
  unfold pluckerCoord
  ring

/--
The Klein quadric relation in Plücker coordinates.

A decomposable bivector `x ∧ y` satisfies

`p01*p23 - p02*p13 + p03*p12 = 0`.
-/
theorem plucker_klein_relation
    (x y : Vec4 R) :
    pluckerCoord x y 0 1 * pluckerCoord x y 2 3
      - pluckerCoord x y 0 2 * pluckerCoord x y 1 3
      + pluckerCoord x y 0 3 * pluckerCoord x y 1 2
        = 0 := by
  unfold pluckerCoord
  ring

/--
Named predicate for the Klein quadric equation in six coordinates.
-/
def KleinRel
    (p01 p02 p03 p12 p13 p23 : R) : Prop :=
  p01 * p23 - p02 * p13 + p03 * p12 = 0

/-- The Klein relation is homogeneous under uniform scaling of all six coordinates. -/
theorem KleinRel_smul
    {p01 p02 p03 p12 p13 p23 : R} (a : R)
    (h : KleinRel p01 p02 p03 p12 p13 p23) :
    KleinRel (a * p01) (a * p02) (a * p03) (a * p12) (a * p13) (a * p23) := by
  unfold KleinRel at h ⊢
  calc
    (a * p01) * (a * p23) - (a * p02) * (a * p13) + (a * p03) * (a * p12)
        = a ^ 2 * (p01 * p23 - p02 * p13 + p03 * p12) := by
          ring
    _ = 0 := by rw [h, mul_zero]

/--
The Plücker coordinates of two explicit vectors land on the Klein quadric.
-/
theorem plucker_coordinates_satisfy_KleinRel
    (x y : Vec4 R) :
    KleinRel
      (pluckerCoord x y 0 1)
      (pluckerCoord x y 0 2)
      (pluckerCoord x y 0 3)
      (pluckerCoord x y 1 2)
      (pluckerCoord x y 1 3)
      (pluckerCoord x y 2 3) := by
  unfold KleinRel
  exact plucker_klein_relation x y

/--
Projective scaling law for the six Plücker coordinates obtained by scaling the
input vectors separately.
-/
theorem plucker_coordinates_smul_both_satisfy_KleinRel
    (a b : R) (x y : Vec4 R) :
    KleinRel
      ((a * b) * pluckerCoord x y 0 1)
      ((a * b) * pluckerCoord x y 0 2)
      ((a * b) * pluckerCoord x y 0 3)
      ((a * b) * pluckerCoord x y 1 2)
      ((a * b) * pluckerCoord x y 1 3)
      ((a * b) * pluckerCoord x y 2 3) := by
  exact KleinRel_smul (a * b) (plucker_coordinates_satisfy_KleinRel x y)

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[pluckerCoord_self, pluckerCoord_swap, pluckerCoord_smul_left,
 pluckerCoord_smul_right, pluckerCoord_smul_both, plucker_klein_relation,
 KleinRel_smul, plucker_coordinates_satisfy_KleinRel,
 plucker_coordinates_smul_both_satisfy_KleinRel]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[All theorems are over an arbitrary commutative ring `R`.]

#### BUCKET 3: OPEN CLOSURE DEBT
[Converse decomposability theorem, projective quotient of nonzero Plücker
 coordinates, Grassmannian `Gr(2,4)`, Plücker embedding as an equivalence onto
 the Klein quadric, Schubert calculus, and Gromov--Witten intersection
 readouts are not proved here.]
-/

end InfoGeometry.Projective.Quadrics.PluckerKlein
