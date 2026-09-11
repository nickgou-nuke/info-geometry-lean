import InfoGeometry.Algebra.Zorn.BasisTable
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native Zorn basis versus unit-valued twisted-group readouts

The concrete Zorn basis contains zero products (for example `e11 * e22 = 0`).
Therefore it cannot be identified, on the full eight-element basis, with a
twisted group algebra whose structure constants are units.  This is a useful
negative boundary for the cochain bridge: a later positive identification must
use a different carrier or a restricted sector.
-/

namespace InfoGeometry.Algebra.Zorn.ZornTwistedGroupReadoutObstruction

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8

def unitScaledBasis (b : Basis8) (u : ℤˣ) : ZornCell ℤ :=
  let X := Basis8.cell b
  { r := (u : ℤ) * X.r
    s := (u : ℤ) * X.s
    x1 := (u : ℤ) * X.x1
    x2 := (u : ℤ) * X.x2
    x3 := (u : ℤ) * X.x3
    y1 := (u : ℤ) * X.y1
    y2 := (u : ℤ) * X.y2
    y3 := (u : ℤ) * X.y3 }

def zeroZornCell : ZornCell ℤ :=
  { r := 0, s := 0, x1 := 0, x2 := 0, x3 := 0,
    y1 := 0, y2 := 0, y3 := 0 }

theorem basisCell_smul_unit_ne_zero (b : Basis8) (u : ℤˣ) :
    unitScaledBasis b u ≠ zeroZornCell := by
  intro h
  have hu : (u : ℤ) ≠ 0 := Units.ne_zero u
  cases b <;>
    first
    | exact hu (by simpa [unitScaledBasis, Basis8.cell, zeroZornCell]
        using congrArg (fun X : ZornCell ℤ => X.r) h)
    | exact hu (by simpa [unitScaledBasis, Basis8.cell, zeroZornCell]
        using congrArg (fun X : ZornCell ℤ => X.s) h)
    | exact hu (by simpa [unitScaledBasis, Basis8.cell, zeroZornCell]
        using congrArg (fun X : ZornCell ℤ => X.x1) h)
    | exact hu (by simpa [unitScaledBasis, Basis8.cell, zeroZornCell]
        using congrArg (fun X : ZornCell ℤ => X.x2) h)
    | exact hu (by simpa [unitScaledBasis, Basis8.cell, zeroZornCell]
        using congrArg (fun X : ZornCell ℤ => X.x3) h)
    | exact hu (by simpa [unitScaledBasis, Basis8.cell, zeroZornCell]
        using congrArg (fun X : ZornCell ℤ => X.y1) h)
    | exact hu (by simpa [unitScaledBasis, Basis8.cell, zeroZornCell]
        using congrArg (fun X : ZornCell ℤ => X.y2) h)
    | exact hu (by simpa [unitScaledBasis, Basis8.cell, zeroZornCell]
        using congrArg (fun X : ZornCell ℤ => X.y3) h)

theorem e11_mul_e22_not_unit_smul_basis :
    ¬ ∃ (b : Basis8) (u : ℤˣ),
      Basis8.cell e11 * Basis8.cell e22 = unitScaledBasis b u := by
  rintro ⟨b, u, h⟩
  have hzero : Basis8.cell e11 * Basis8.cell e22 = zeroZornCell := by
    simpa [zeroZornCell, SignedBasis.cell] using (mulTable_correct e11 e22)
  have hnonzero : unitScaledBasis b u ≠ zeroZornCell := by
    simpa [zeroZornCell] using basisCell_smul_unit_ne_zero b u
  apply hnonzero
  rw [← h, hzero]

end InfoGeometry.Algebra.Zorn.ZornTwistedGroupReadoutObstruction
