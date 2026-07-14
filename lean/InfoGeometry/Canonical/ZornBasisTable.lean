import InfoGeometry.Algebra.Zorn.BasisTable

/-!
# Canonical finite Zorn basis table facade

This canonical module exposes the already-proved concrete 8-basis Zorn
multiplication table from `InfoGeometry.Algebra.Zorn.BasisTable` under the
canonical layer.  It is a theorem-facing facade, not a competing Zorn model.

Closed content:
* the indexed basis `E11,E22,U1,U2,U3,V1,V2,V3`;
* the signed table entries, including zero;
* the complete 8×8 multiplication table theorem;
* small canonical readback packets for the diagonal idempotents and cross signs.

It intentionally does not claim any global group-identification theorem.
-/

namespace ZornBasisTable

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

/-- Canonical alias for the finite Zorn basis index type. -/
abbrev Basis8 := ZornCell.Basis8

/-- Canonical alias for signed entries of the finite Zorn basis table. -/
abbrev SignedBasis := ZornCell.Basis8.SignedBasis

namespace Basis8

/-- Canonical readback of a basis slot as a concrete integer Zorn cell. -/
def cell : Basis8 → ZornCell ℤ :=
  ZornCell.Basis8.cell

/-- Canonical readback of a signed table entry as a concrete integer Zorn cell. -/
def signedCell : SignedBasis → ZornCell ℤ :=
  ZornCell.Basis8.SignedBasis.cell

/-- Canonical alias for the complete rows-times-columns multiplication table. -/
def mulTable : Basis8 → Basis8 → SignedBasis :=
  ZornCell.Basis8.mulTable

/-- Canonical finite table theorem: rows multiply columns under the concrete Zorn product. -/
theorem mulTable_correct (a b : Basis8) :
    cell a * cell b = signedCell (mulTable a b) :=
  ZornCell.Basis8.mulTable_correct a b

/-- Canonical diagonal idempotent packet for the finite Zorn table. -/
theorem diagonal_idempotent_packet :
    cell .e11 * cell .e11 = cell .e11 ∧
      cell .e22 * cell .e22 = cell .e22 ∧
      cell .e11 * cell .e22 = signedCell .zero ∧
      cell .e22 * cell .e11 = signedCell .zero :=
  ZornCell.Basis8.diagonal_idempotent_packet

/-- Canonical representative cross-sign packet for the repository's Zorn convention. -/
theorem cross_sign_packet :
    cell .u1 * cell .u2 = cell .v3 ∧
      cell .u2 * cell .u1 = signedCell (.neg .v3) ∧
      cell .v1 * cell .v2 = signedCell (.neg .u3) ∧
      cell .v2 * cell .v1 = cell .u3 :=
  ZornCell.Basis8.cross_sign_packet

end Basis8

end ZornBasisTable
