import InfoGeometry.Algebra.Zorn.BasisTable
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Concrete Zorn associator obstruction

This module gives a finite, coordinate-level nonassociativity witness for the
repository's concrete Zorn product.  The witness is expressed in the standard
8-basis table `E11,E22,U1,U2,U3,V1,V2,V3`.
-/

namespace InfoGeometry.Algebra.Zorn.ConcreteComposition
namespace ZornCell
namespace Basis8

open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open SignedBasis

/-- Coordinatewise subtraction of concrete integer Zorn cells. -/
def subZ (X Y : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ) :
    InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ where
  r := X.r - Y.r
  s := X.s - Y.s
  x1 := X.x1 - Y.x1
  x2 := X.x2 - Y.x2
  x3 := X.x3 - Y.x3
  y1 := X.y1 - Y.y1
  y2 := X.y2 - Y.y2
  y3 := X.y3 - Y.y3

/-- Coordinatewise negation of concrete integer Zorn cells. -/
def negZ (X : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ) :
    InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ where
  r := -X.r
  s := -X.s
  x1 := -X.x1
  x2 := -X.x2
  x3 := -X.x3
  y1 := -X.y1
  y2 := -X.y2
  y3 := -X.y3

/-- Concrete associator `(X*Y)*Z - X*(Y*Z)` for integer Zorn cells. -/
def associatorZ (X Y Z : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ) :
    InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ :=
  subZ ((X * Y) * Z) (X * (Y * Z))

/-- Concrete commutator `X*Y - Y*X` for integer Zorn cells. -/
def commutatorZ (X Y : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ) :
    InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ :=
  subZ (X * Y) (Y * X)

/-- The concrete commutator of a cell with itself is zero. -/
theorem commutatorZ_self
    (X : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ) :
    commutatorZ X X = SignedBasis.cell zero := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  simp [commutatorZ, subZ, SignedBasis.cell]

/-- Reversing the concrete commutator negates it. -/
theorem commutatorZ_skew
    (X Y : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ) :
    commutatorZ X Y = negZ (commutatorZ Y X) := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x1', x2', x3', y1', y2', y3'⟩
  simp [commutatorZ, subZ, negZ]

/-- The two ordered concrete commutators cancel under componentwise addition. -/
theorem commutatorZ_add_reverse
    (X Y : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ) :
    addZ (commutatorZ X Y) (commutatorZ Y X) = SignedBasis.cell zero := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x1', x2', x3', y1', y2', y3'⟩
  simp [commutatorZ, subZ, addZ, SignedBasis.cell]

/-- Concrete cyclic Jacobiator of the Zorn element commutator. -/
def commutatorJacobiatorZ
    (X Y Z : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ) :
    InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ :=
  addZ
    (commutatorZ X (commutatorZ Y Z))
    (addZ (commutatorZ Y (commutatorZ Z X)) (commutatorZ Z (commutatorZ X Y)))

/--
The alternating associator sum from the Akivis identity for a commutator in a
non-associative algebra.
-/
def akivisRhsZ
    (X Y Z : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ) :
    InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ :=
  subZ
    (addZ (addZ (associatorZ X Z Y) (associatorZ Y X Z)) (associatorZ Z Y X))
    (addZ (addZ (associatorZ X Y Z) (associatorZ Y Z X)) (associatorZ Z X Y))

/-- The diagonal/off-diagonal/off-diagonal triple `(E11,U1,U2)` has associator `V3`. -/
theorem associator_e11_u1_u2_eq_v3 :
    associatorZ (cell e11) (cell u1) (cell u2) = cell v3 := by
  decide

/-- The concrete Zorn product is not associative on the standard 8-basis. -/
theorem associator_e11_u1_u2_ne_zero :
    associatorZ (cell e11) (cell u1) (cell u2) ≠ SignedBasis.cell zero := by
  decide

/-- The obstruction witness is exactly the lower off-diagonal basis direction `V3`. -/
theorem associator_obstruction_witness_packet :
    associatorZ (cell e11) (cell u1) (cell u2) = cell v3 ∧
      associatorZ (cell e11) (cell u1) (cell u2) ≠ SignedBasis.cell zero := by
  exact ⟨associator_e11_u1_u2_eq_v3, associator_e11_u1_u2_ne_zero⟩

/-- The left-associated product in the witness is `V3`. -/
theorem associator_witness_left_product :
    (cell e11 * cell u1) * cell u2 = cell v3 := by
  decide

/-- The right-associated product in the witness is zero. -/
theorem associator_witness_right_product :
    cell e11 * (cell u1 * cell u2) = SignedBasis.cell zero := by
  decide

/--
The concrete Zorn product is not associative on integer cells.

This is the theorem-level blocker for any attempt to treat the concrete Zorn
product as an associative matrix multiplication.
-/
theorem not_associative_concrete_zorn :
    ¬ (∀ X Y Z : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ,
      associatorZ X Y Z = SignedBasis.cell zero) := by
  intro h
  exact associator_e11_u1_u2_ne_zero (h (cell e11) (cell u1) (cell u2))

/-- Concrete noncommutativity witness in the upper off-diagonal sector. -/
theorem commutator_u1_u2 :
    commutatorZ (cell u1) (cell u2) =
      ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ := by
  decide

/-- The concrete upper-sector commutator witness is nonzero. -/
theorem commutator_u1_u2_ne_zero :
    commutatorZ (cell u1) (cell u2) ≠ SignedBasis.cell zero := by
  decide

/-- The concrete Zorn product is not commutative on integer cells. -/
theorem not_commutative_concrete_zorn :
    ¬ (∀ X Y : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ,
      commutatorZ X Y = SignedBasis.cell zero) := by
  intro h
  exact commutator_u1_u2_ne_zero (h (cell u1) (cell u2))

/-- Every concrete basis cell has zero self-commutator. -/
theorem commutator_self_all_basis (a : Basis8) :
    commutatorZ (cell a) (cell a) = SignedBasis.cell zero :=
  commutatorZ_self (cell a)

/-- The finite basis commutator is skew under argument reversal. -/
theorem commutator_skew_all_basis (a b : Basis8) :
    commutatorZ (cell a) (cell b) =
      negZ (commutatorZ (cell b) (cell a)) :=
  commutatorZ_skew (cell a) (cell b)

/-- The upper-sector basis commutator Jacobiator is the nonzero diagonal cell `(6,-6)`. -/
theorem commutator_jacobi_u1_u2_u3 :
    commutatorJacobiatorZ (cell u1) (cell u2) (cell u3) =
      ⟨6, -6, 0, 0, 0, 0, 0, 0⟩ := by
  decide

/-- The lower-sector basis commutator Jacobiator is the same nonzero diagonal cell. -/
theorem commutator_jacobi_v1_v2_v3 :
    commutatorJacobiatorZ (cell v1) (cell v2) (cell v3) =
      ⟨6, -6, 0, 0, 0, 0, 0, 0⟩ := by
  decide

/-- The upper-sector Jacobiator witness is nonzero. -/
theorem commutator_jacobi_u1_u2_u3_ne_zero :
    commutatorJacobiatorZ (cell u1) (cell u2) (cell u3) ≠ SignedBasis.cell zero := by
  decide

/-- The lower-sector Jacobiator witness is nonzero. -/
theorem commutator_jacobi_v1_v2_v3_ne_zero :
    commutatorJacobiatorZ (cell v1) (cell v2) (cell v3) ≠ SignedBasis.cell zero := by
  decide

/-- Determinant/norm readout of the upper-sector Jacobiator witness. -/
theorem detZ_commutator_jacobi_u1_u2_u3 :
    detZ (commutatorJacobiatorZ (cell u1) (cell u2) (cell u3)) = -36 := by
  decide

/-- Determinant/norm readout of the lower-sector Jacobiator witness. -/
theorem detZ_commutator_jacobi_v1_v2_v3 :
    detZ (commutatorJacobiatorZ (cell v1) (cell v2) (cell v3)) = -36 := by
  decide

/--
The element commutator of the concrete Zorn product does not satisfy the Jacobi
identity on integer cells.

This is the direct finite obstruction to installing a full-element `LieRing`
structure from the Zorn element commutator.
-/
theorem not_jacobi_commutator_concrete_zorn :
    ¬ (∀ X Y Z : InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ,
      commutatorJacobiatorZ X Y Z = SignedBasis.cell zero) := by
  intro h
  exact commutator_jacobi_u1_u2_u3_ne_zero (h (cell u1) (cell u2) (cell u3))

/-- Finite upper-sector readout of the Akivis commutator-Jacobiator identity. -/
theorem akivis_u1_u2_u3 :
    commutatorJacobiatorZ (cell u1) (cell u2) (cell u3) =
      akivisRhsZ (cell u1) (cell u2) (cell u3) := by
  decide

/-- Finite lower-sector readout of the Akivis commutator-Jacobiator identity. -/
theorem akivis_v1_v2_v3 :
    commutatorJacobiatorZ (cell v1) (cell v2) (cell v3) =
      akivisRhsZ (cell v1) (cell v2) (cell v3) := by
  decide

/--
Finite all-basis Akivis identity for the concrete Zorn product.

This is a total check over the `8^3` standard basis triples.  It is deliberately
finite and coordinate-level: it does not install a Lie structure on Zorn
elements, and it does not replace the generic coordinate theorem in
`ZornVectorMatrix`.
-/
theorem akivis_all_basis (a b c : Basis8) :
    commutatorJacobiatorZ (cell a) (cell b) (cell c) =
      akivisRhsZ (cell a) (cell b) (cell c) := by
  cases a <;> cases b <;> cases c <;> decide

/--
The finite basis packet: Zorn element commutators are not Lie brackets on this
basis, and their Jacobiator is exactly the Akivis alternating associator sum on
the same witnesses.
-/
theorem commutator_jacobi_akivis_obstruction_packet :
    commutatorJacobiatorZ (cell u1) (cell u2) (cell u3) ≠ SignedBasis.cell zero ∧
      commutatorJacobiatorZ (cell v1) (cell v2) (cell v3) ≠ SignedBasis.cell zero ∧
      commutatorJacobiatorZ (cell u1) (cell u2) (cell u3) =
        akivisRhsZ (cell u1) (cell u2) (cell u3) ∧
      commutatorJacobiatorZ (cell v1) (cell v2) (cell v3) =
        akivisRhsZ (cell v1) (cell v2) (cell v3) := by
  exact
    ⟨commutator_jacobi_u1_u2_u3_ne_zero,
      commutator_jacobi_v1_v2_v3_ne_zero,
      akivis_u1_u2_u3,
      akivis_v1_v2_v3⟩

end Basis8
end ZornCell
end InfoGeometry.Algebra.Zorn.ConcreteComposition
