import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionGogberashviliCarrierBridge
import InfoGeometry.Canonical.ZornBasisTable

/-!
# Scalar extension of the concrete Zorn-cell carrier

The integer coordinate lattice is included in the real carrier coordinatewise.
This is the sound carrier edge used before transporting the real carrier to
the canonical `CZ` presentation.  The indexed eight-cell family is retained
as the rational/integral basis readout; no tensor-product claim is made here.
-/

namespace InfoGeometry.Canonical.ZornCellScalarExtensionBridge

set_option maxHeartbeats 1000000

noncomputable section

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open InfoGeometry.Canonical.SplitOctonionGogberashviliCarrierBridge

abbrev IntCell := ZornCell ℤ
abbrev RealCell := ZornCell ℝ
abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ

/-! The explicit real carrier equivalence is the canonical downstream handle. -/
noncomputable def realCellToCZ : RealCell ≃ₗ[ℝ] CZ :=
  cellToCanonical

theorem realCellToCZ_mul (X Y : RealCell) :
    realCellToCZ (X * Y) = realCellToCZ X * realCellToCZ Y := by
  exact cellToCanonical_mul X Y

def intToReal (X : IntCell) : RealCell :=
  { r := X.r, s := X.s, x1 := X.x1, x2 := X.x2, x3 := X.x3,
    y1 := X.y1, y2 := X.y2, y3 := X.y3 }

@[simp] theorem intToReal_apply (X : IntCell) :
    intToReal X =
      ({ r := X.r, s := X.s, x1 := X.x1, x2 := X.x2, x3 := X.x3,
         y1 := X.y1, y2 := X.y2, y3 := X.y3 } : RealCell) := rfl

theorem intToReal_mul (X Y : IntCell) :
    intToReal (X * Y) = intToReal X * intToReal Y := by
  cases X
  cases Y
  change intToReal (ZornCell.mulZ _ _) =
    ZornCell.mulZ (intToReal _) (intToReal _)
  change ({ r := _, s := _, x1 := _, x2 := _, x3 := _, y1 := _, y2 := _, y3 := _ } : RealCell) = _
  congr 1 <;>
    norm_num [intToReal, ZornCell.mulZ, Int.cast_add, Int.cast_mul] <;>
    ring

noncomputable def intToCanonical (X : IntCell) : CZ :=
  realCellToCZ (intToReal X)

theorem intToCanonical_mul (X Y : IntCell) :
    intToCanonical (X * Y) = intToCanonical X * intToCanonical Y := by
  rw [intToCanonical, intToCanonical, intToCanonical]
  rw [intToReal_mul, realCellToCZ_mul]

def transportedIntegralBasis (i : ZornCell.Basis8) : CZ :=
  intToCanonical (ZornCell.Basis8.cell i)

/-! Public name for the rational/integral lattice readout transported to `CZ`. -/
abbrev transportedRationalBasis := transportedIntegralBasis

theorem transportedIntegralBasis_mul (i j : ZornCell.Basis8) :
    transportedIntegralBasis i * transportedIntegralBasis j =
      intToCanonical (ZornCell.Basis8.SignedBasis.cell (ZornCell.Basis8.mulTable i j)) := by
  change intToCanonical (ZornCell.Basis8.cell i) *
      intToCanonical (ZornCell.Basis8.cell j) = _
  rw [← intToCanonical_mul]
  exact congrArg intToCanonical (ZornCell.Basis8.mulTable_correct i j)

theorem transportedRationalBasis_mul (i j : ZornCell.Basis8) :
    transportedRationalBasis i * transportedRationalBasis j =
      intToCanonical (ZornCell.Basis8.SignedBasis.cell
        (ZornCell.Basis8.mulTable i j)) :=
  transportedIntegralBasis_mul i j

end
end InfoGeometry.Canonical.ZornCellScalarExtensionBridge
