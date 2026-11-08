import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Basic

/-!
# TopCat finite readout approximants

The finite binary partial readouts are continuous cylinder observables.  This
owner exposes them as `TopCat` arrows and records the existing geometric-tail
error bound, without adding a completion or measure-theoretic limit.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryFiniteReadoutTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds

def realBinaryPartialReadoutTopCatHom (N : ℕ) :
    TopCat.of CantorBoundary ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun w => realBinaryPartialReadout N w
      continuous_toFun := continuous_realBinaryPartialReadout N }

@[simp] theorem realBinaryPartialReadoutTopCatHom_apply
    (N : ℕ) (w : CantorBoundary) :
    realBinaryPartialReadoutTopCatHom N w = realBinaryPartialReadout N w := rfl

theorem realBinaryPartialReadoutTopCatHom_error_bound
    (N : ℕ) (w : CantorBoundary) :
    realBinaryReadout w - realBinaryPartialReadoutTopCatHom N w ≤
      (1 / 2 : ℝ) ^ N := by
  exact realBinaryReadout_sub_partial_le_half_pow N w

theorem realBinaryPartialReadoutTopCatHom_abs_error_bound
    (N : ℕ) (w : CantorBoundary) :
    |realBinaryReadout w - realBinaryPartialReadoutTopCatHom N w| ≤
      (1 / 2 : ℝ) ^ N := by
  have hnonneg :
      0 ≤ realBinaryReadout w - realBinaryPartialReadout N w :=
    sub_nonneg.mpr (realBinaryPartialReadout_le_readout N w)
  simpa [realBinaryPartialReadoutTopCatHom, abs_of_nonneg hnonneg] using
    realBinaryReadout_sub_partial_le_half_pow N w

end InfoGeometry.Canonical.CantorBoundaryFiniteReadoutTopCat
