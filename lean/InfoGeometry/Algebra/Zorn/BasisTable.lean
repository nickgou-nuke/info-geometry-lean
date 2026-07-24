import InfoGeometry.Algebra.Zorn.ConcreteComposition

/-!
# Finite 8-basis multiplication table for concrete Zorn cells

This module proves the complete multiplication table for the concrete integer
basis of the Zorn cell model from `InfoGeometry.Algebra.Zorn.ConcreteComposition`.
Rows multiply columns.  The basis is
`E11,E22,U1,U2,U3,V1,V2,V3`, where `Ui` is the upper-vector slot and `Vi` is
the lower-vector slot.

The theorem surface is finite and exact: it proves only the 8×8 table for the
concrete product convention in this repository.  It does not claim any global
group-identification theorem.
-/

namespace InfoGeometry.Algebra.Zorn.ConcreteComposition
namespace ZornCell

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

deriving instance DecidableEq for ZornCell

/-- The eight standard Zorn matrix basis slots. -/
inductive Basis8 where
  | e11 | e22 | u1 | u2 | u3 | v1 | v2 | v3
  deriving DecidableEq, Repr

namespace Basis8

/-- Concrete integer Zorn cell attached to a basis slot. -/
def cell : Basis8 → ZornCell ℤ
  | e11 => ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
  | e22 => ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
  | u1  => ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
  | u2  => ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
  | u3  => ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
  | v1  => ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
  | v2  => ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
  | v3  => ⟨0, 0, 0, 0, 0, 0, 0, 1⟩

/-- A signed basis-table entry, including zero. -/
inductive SignedBasis where
  | zero
  | pos : Basis8 → SignedBasis
  | neg : Basis8 → SignedBasis
  deriving DecidableEq, Repr

namespace SignedBasis

/-- Interpret a signed table entry as an integer Zorn cell. -/
def cell : SignedBasis → ZornCell ℤ
  | zero => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
  | pos b => Basis8.cell b
  | neg b =>
      let X := Basis8.cell b
      ⟨-X.r, -X.s, -X.x1, -X.x2, -X.x3, -X.y1, -X.y2, -X.y3⟩

end SignedBasis

open SignedBasis

/-- Complete multiplication table for rows times columns. -/
def mulTable : Basis8 → Basis8 → SignedBasis
  | e11, e11 => pos e11
  | e11, e22 => zero
  | e11, u1 => pos u1
  | e11, u2 => pos u2
  | e11, u3 => pos u3
  | e11, v1 => zero
  | e11, v2 => zero
  | e11, v3 => zero

  | e22, e11 => zero
  | e22, e22 => pos e22
  | e22, u1 => zero
  | e22, u2 => zero
  | e22, u3 => zero
  | e22, v1 => pos v1
  | e22, v2 => pos v2
  | e22, v3 => pos v3

  | u1, e11 => zero
  | u1, e22 => pos u1
  | u1, u1 => zero
  | u1, u2 => pos v3
  | u1, u3 => neg v2
  | u1, v1 => pos e11
  | u1, v2 => zero
  | u1, v3 => zero

  | u2, e11 => zero
  | u2, e22 => pos u2
  | u2, u1 => neg v3
  | u2, u2 => zero
  | u2, u3 => pos v1
  | u2, v1 => zero
  | u2, v2 => pos e11
  | u2, v3 => zero

  | u3, e11 => zero
  | u3, e22 => pos u3
  | u3, u1 => pos v2
  | u3, u2 => neg v1
  | u3, u3 => zero
  | u3, v1 => zero
  | u3, v2 => zero
  | u3, v3 => pos e11

  | v1, e11 => pos v1
  | v1, e22 => zero
  | v1, u1 => pos e22
  | v1, u2 => zero
  | v1, u3 => zero
  | v1, v1 => zero
  | v1, v2 => neg u3
  | v1, v3 => pos u2

  | v2, e11 => pos v2
  | v2, e22 => zero
  | v2, u1 => zero
  | v2, u2 => pos e22
  | v2, u3 => zero
  | v2, v1 => pos u3
  | v2, v2 => zero
  | v2, v3 => neg u1

  | v3, e11 => pos v3
  | v3, e22 => zero
  | v3, u1 => zero
  | v3, u2 => zero
  | v3, u3 => pos e22
  | v3, v1 => neg u2
  | v3, v2 => pos u1
  | v3, v3 => zero

/-- The complete 8×8 multiplication table is correct for the concrete Zorn product. -/
theorem mulTable_correct (a b : Basis8) :
    Basis8.cell a * Basis8.cell b = SignedBasis.cell (mulTable a b) := by
  cases a <;> cases b <;> decide

/-- Diagonal idempotent packet. -/
theorem diagonal_idempotent_packet :
    Basis8.cell e11 * Basis8.cell e11 = Basis8.cell e11 ∧
      Basis8.cell e22 * Basis8.cell e22 = Basis8.cell e22 ∧
      Basis8.cell e11 * Basis8.cell e22 = SignedBasis.cell zero ∧
      Basis8.cell e22 * Basis8.cell e11 = SignedBasis.cell zero := by
  constructor
  · exact mulTable_correct e11 e11
  constructor
  · exact mulTable_correct e22 e22
  constructor
  · exact mulTable_correct e11 e22
  · exact mulTable_correct e22 e11

/-- Representative cross-product sign packet for the repository's Zorn convention. -/
theorem cross_sign_packet :
    Basis8.cell u1 * Basis8.cell u2 = Basis8.cell v3 ∧
      Basis8.cell u2 * Basis8.cell u1 = SignedBasis.cell (neg v3) ∧
      Basis8.cell v1 * Basis8.cell v2 = SignedBasis.cell (neg u3) ∧
      Basis8.cell v2 * Basis8.cell v1 = Basis8.cell u3 := by
  constructor
  · exact mulTable_correct u1 u2
  constructor
  · exact mulTable_correct u2 u1
  constructor
  · exact mulTable_correct v1 v2
  · exact mulTable_correct v2 v1

end Basis8
end ZornCell
end InfoGeometry.Algebra.Zorn.ConcreteComposition
