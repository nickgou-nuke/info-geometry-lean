import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Algebra.Category.Ring.Basic
import InfoGeometry.Causal.Alexandrov
import InfoGeometry.Algebra.ZornVectorMatrix

open CategoryTheory

namespace InfoGeometry.Causal

open InfoGeometry.Algebra

variable {α : Type*} [Preorder α]

/-- Functorial map of `ZornVec3` under a ring homomorphism. -/
def ZornVec3.map {R S : Type*} (f : R → S) (v : ZornVec3 R) : ZornVec3 S :=
  fun i => f (v i)

/-- Functorial map of a `ZornVectorMatrix` under a ring homomorphism. -/
def ZornVectorMatrix.map {R S : Type*} (f : R → S) (X : ZornVectorMatrix R) : ZornVectorMatrix S :=
  ⟨f X.a, ZornVec3.map f X.v, ZornVec3.map f X.w, f X.b⟩

section MapProperties

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem ZornVec3.map_dot (x y : ZornVec3 R) :
    ZornVec3.dot (ZornVec3.map f x) (ZornVec3.map f y) = f (ZornVec3.dot x y) := by
  simp [ZornVec3.dot, ZornVec3.map, map_sum]

theorem ZornVec3.map_cross (x y : ZornVec3 R) (i : Fin 3) :
    ZornVec3.cross (ZornVec3.map f x) (ZornVec3.map f y) i = f (ZornVec3.cross x y i) := by
  fin_cases i <;> simp [ZornVec3.cross, ZornVec3.map, map_sub]

theorem ZornVectorMatrix.map_mul (X Y : ZornVectorMatrix R) :
    ZornVectorMatrix.map f (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.mul (ZornVectorMatrix.map f X) (ZornVectorMatrix.map f Y) := by
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.map, ZornVectorMatrix.mul, map_add, ZornVec3.map_dot]
  · ext i
    simp [ZornVectorMatrix.map, ZornVectorMatrix.mul, ZornVec3.map, map_sub, map_add, ZornVec3.map_cross]
  · ext i
    simp [ZornVectorMatrix.map, ZornVectorMatrix.mul, ZornVec3.map, map_add, ZornVec3.map_cross]
  · simp [ZornVectorMatrix.map, ZornVectorMatrix.mul, map_add, ZornVec3.map_dot]

end MapProperties

/-- A Zorn presheaf over the proof DAG preorder is a covariant functor from `α` to `RingCat`. -/
abbrev ZornPresheaf (α : Type*) [Preorder α] :=
  α ⥤ RingCat

/-- 
  Causal boundary projection: For any link `A ≤ B`, the presheaf provides a 
  morphism mapping observables at `A` to observables at `B`.
-/
def boundaryProjection {α : Type*} [Preorder α] (P : ZornPresheaf α) {A B : α} (h : A ≤ B) :
    P.obj A ⟶ P.obj B :=
  P.map (homOfLE h)

/-- 
  Causal projection preserves Zorn algebra multiplication. 
  This shows that the non-associative Zorn algebra structure is preserved along the boundary projection.
-/
theorem boundary_projection_preserves_mul {α : Type*} [Preorder α] (P : ZornPresheaf α)
    {A B : α} (h : A ≤ B) (X Y : P.obj A) :
    (boundaryProjection P h) (X * Y) = (boundaryProjection P h) X * (boundaryProjection P h) Y := by
  exact map_mul (boundaryProjection P h).hom' X Y

end InfoGeometry.Causal
