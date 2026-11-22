/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.AssociatorObstruction
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Transfer the Akivis identity to concrete Zorn cells

The basis-table owner has a finite `8^3` check.  This bridge identifies its
integer cell coordinates with the repository's general Zorn vector-matrix
owner and transports the all-elements Akivis identity to that concrete
carrier.
-/

namespace InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
namespace Basis8
namespace AkivisBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8

abbrev Cell := ZornCell ℤ
abbrev VectorMatrix := ZornVectorMatrix ℤ

def vec3 (x y z : ℤ) : Fin 3 → ℤ := ![x, y, z]

/-- Coordinate identification from the concrete eight-coordinate cell. -/
def toVectorMatrix (X : Cell) : VectorMatrix :=
  ⟨X.r, vec3 X.x1 X.x2 X.x3, vec3 X.y1 X.y2 X.y3, X.s⟩

theorem toVectorMatrix_injective : Function.Injective toVectorMatrix := by
  intro X Y h
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x1', x2', x3', y1', y2', y3'⟩
  have hr := congrArg ZornVectorMatrix.a h
  have hs := congrArg ZornVectorMatrix.b h
  have hx := congrArg ZornVectorMatrix.v h
  have hy := congrArg ZornVectorMatrix.w h
  simp [toVectorMatrix, vec3] at hr hs hx hy
  rcases hx with ⟨hx1, hx2, hx3⟩
  rcases hy with ⟨hy1, hy2, hy3⟩
  subst r'
  subst s'
  subst x1'
  subst x2'
  subst x3'
  subst y1'
  subst y2'
  subst y3'
  rfl

theorem toVectorMatrix_add (X Y : Cell) :
    toVectorMatrix (addZ X Y) = ZornVectorMatrix.add (toVectorMatrix X) (toVectorMatrix Y) := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x1', x2', x3', y1', y2', y3'⟩
  simp [toVectorMatrix, vec3,
    InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.addZ,
    ZornVectorMatrix.add]
  constructor <;> funext i <;> fin_cases i <;> rfl

theorem toVectorMatrix_sub (X Y : Cell) :
    toVectorMatrix (subZ X Y) = ZornVectorMatrix.sub (toVectorMatrix X) (toVectorMatrix Y) := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x1', x2', x3', y1', y2', y3'⟩
  ext i
  · change r - r' = r + -r'
    ring
  · fin_cases i <;> simp [toVectorMatrix, vec3,
      InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8.subZ,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg] <;> ring_nf
  · fin_cases i <;> simp [toVectorMatrix, vec3,
      InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8.subZ,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg] <;> ring_nf
  · change s - s' = s + -s'
    ring

theorem toVectorMatrix_mul (X Y : Cell) :
    toVectorMatrix (X * Y) = ZornVectorMatrix.mul (toVectorMatrix X) (toVectorMatrix Y) := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x1', x2', x3', y1', y2', y3'⟩
  change toVectorMatrix
      (InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.mulZ
        ⟨r, s, x1, x2, x3, y1, y2, y3⟩ ⟨r', s', x1', x2', x3', y1', y2', y3'⟩) = _
  ext i
  · simp [toVectorMatrix, vec3,
      InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.mulZ,
      ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]
  · fin_cases i <;> simp [toVectorMatrix, vec3,
      InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.mulZ,
      ZornVectorMatrix.mul,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  · fin_cases i <;> simp [toVectorMatrix, vec3,
      InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.mulZ,
      ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
  · simp [toVectorMatrix, vec3,
      InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.mulZ,
      ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]

theorem toVectorMatrix_associator (X Y Z : Cell) :
    toVectorMatrix (associatorZ X Y Z) =
      ZornVectorMatrix.associator (toVectorMatrix X) (toVectorMatrix Y) (toVectorMatrix Z) := by
  simp only [associatorZ, ZornVectorMatrix.associator,
    toVectorMatrix_sub, toVectorMatrix_mul]

theorem toVectorMatrix_commutator (X Y : Cell) :
    toVectorMatrix (commutatorZ X Y) =
      ZornVectorMatrix.commutator (toVectorMatrix X) (toVectorMatrix Y) := by
  simp only [commutatorZ, ZornVectorMatrix.commutator,
    toVectorMatrix_sub, toVectorMatrix_mul]

theorem toVectorMatrix_jacobiator (X Y Z : Cell) :
    toVectorMatrix (commutatorJacobiatorZ X Y Z) =
      ZornVectorMatrix.commutatorJacobiator
        (toVectorMatrix X) (toVectorMatrix Y) (toVectorMatrix Z) := by
  simp only [commutatorJacobiatorZ, ZornVectorMatrix.commutatorJacobiator,
    toVectorMatrix_add, toVectorMatrix_commutator]

theorem toVectorMatrix_akivisRhs (X Y Z : Cell) :
    toVectorMatrix (akivisRhsZ X Y Z) =
      ZornVectorMatrix.sub
        (ZornVectorMatrix.add
          (ZornVectorMatrix.add
            (ZornVectorMatrix.associator (toVectorMatrix X) (toVectorMatrix Z) (toVectorMatrix Y))
            (ZornVectorMatrix.associator (toVectorMatrix Y) (toVectorMatrix X) (toVectorMatrix Z)))
          (ZornVectorMatrix.associator (toVectorMatrix Z) (toVectorMatrix Y) (toVectorMatrix X)))
        (ZornVectorMatrix.add
          (ZornVectorMatrix.add
            (ZornVectorMatrix.associator (toVectorMatrix X) (toVectorMatrix Y) (toVectorMatrix Z))
            (ZornVectorMatrix.associator (toVectorMatrix Y) (toVectorMatrix Z) (toVectorMatrix X)))
          (ZornVectorMatrix.associator (toVectorMatrix Z) (toVectorMatrix X) (toVectorMatrix Y))) := by
  simp only [akivisRhsZ, ZornVectorMatrix.sub, ZornVectorMatrix.add,
    toVectorMatrix_sub, toVectorMatrix_add, toVectorMatrix_associator]

/-- The concrete integer Zorn commutator Jacobiator is the alternating
associator defect for arbitrary cells, not only for basis triples. -/
theorem commutatorJacobiator_eq_akivisRhs (X Y Z : Cell) :
    commutatorJacobiatorZ X Y Z = akivisRhsZ X Y Z := by
  apply toVectorMatrix_injective
  rw [toVectorMatrix_jacobiator, toVectorMatrix_akivisRhs]
  exact ZornVectorMatrix.commutatorJacobiator_eq_associator_alternating
    (toVectorMatrix X) (toVectorMatrix Y) (toVectorMatrix Z)

end AkivisBridge
end Basis8
end InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
