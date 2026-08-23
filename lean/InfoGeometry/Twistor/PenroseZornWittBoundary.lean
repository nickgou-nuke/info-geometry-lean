import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import Mathlib.Tactic.FinCases

/-!
# Witt-polarized Penrose/Zorn null boundary

A raw real-linear identification `ℂ⁴_R ≃ ℝ⁸` does not by itself transport the
Penrose split signature to the Zorn reduced norm.  This owner inserts the
required Witt/light-cone polarization explicitly.

Write a Penrose twistor as two complex spinor sheets `(ω,π)`.  Each sheet has
four real coordinates.  The Witt coordinates are the sum of the two sheets in
the positive Peirce half and a signature-twisted difference in the negative
Peirce half.  In these coordinates the Zorn reduced norm is exactly the
`(4,4)` real split-signature quadratic expression

`|ω|_R² - |π|_R²`.

This is the finite algebraic null-boundary bridge.  Identification with the
separate Hermitian owner `PenroseTwistor.twistorRealQuadraticForm` is a small
follow-up compatibility theorem and is not assumed definitionally here.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseZornWittBoundary

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

abbrev Real8 := Fin 8 → ℝ
abbrev CZ := InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.CZ

/-- The real `(4,4)` Penrose sheet signature written directly in spinor
coordinates. -/
def penroseRealSplitSignature (Z : Twistor4) : ℝ :=
  ((Z.1 0).re ^ 2 + (Z.1 0).im ^ 2 +
      (Z.1 1).re ^ 2 + (Z.1 1).im ^ 2) -
    ((Z.2 0).re ^ 2 + (Z.2 0).im ^ 2 +
      (Z.2 1).re ^ 2 + (Z.2 1).im ^ 2)

/-- Witt/light-cone coordinates adapted to the Zorn Peirce ordering
`u₊ | V₊ | u₋ | V₋`.

If `A` are the four real coordinates of `ω` and `B` those of `π`, the positive
half is `A+B`, while the negative half is `η(A-B)` with
`η = diag(1,-1,-1,-1)`. -/
def penroseWittCoordinates : Twistor4 →ₗ[ℝ] Real8 where
  toFun Z := ![
    (Z.1 0).re + (Z.2 0).re,
    (Z.1 0).im + (Z.2 0).im,
    (Z.1 1).re + (Z.2 1).re,
    (Z.1 1).im + (Z.2 1).im,
    (Z.1 0).re - (Z.2 0).re,
    -(Z.1 0).im + (Z.2 0).im,
    -(Z.1 1).re + (Z.2 1).re,
    -(Z.1 1).im + (Z.2 1).im]
  map_add' Z W := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r Z := by
    ext i
    fin_cases i <;> simp <;> ring

/-- Circular Peirce coordinates are literally the coordinate function of the
established Zorn basis. -/
noncomputable def real8CircularPeirceEquiv : Real8 ≃ₗ[ℝ] CZ :=
  circularPeirceBasis.equivFun.symm

/-- The Witt-polarized real-linear Penrose-to-Zorn map. -/
noncomputable def penroseWittZornMap : Twistor4 →ₗ[ℝ] CZ :=
  real8CircularPeirceEquiv.toLinearMap.comp penroseWittCoordinates

@[simp] theorem circularPeirce_coordinates_real8 (c : Real8) :
    circularPeirceBasis.equivFun (real8CircularPeirceEquiv c) = c := by
  change circularPeirceBasis.equivFun
      (circularPeirceBasis.equivFun.symm c) = c
  exact circularPeirceBasis.equivFun.apply_symm_apply c

/-- Reduced norm in literal circular Peirce coordinates. -/
theorem real8CircularPeirce_norm (c : Real8) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (real8CircularPeirceEquiv c) =
      c 0 * c 4 - (c 1 * c 5 + c 2 * c 6 + c 3 * c 7) := by
  have hcoord (i : Fin 8) :
      circularCoordinate
          (cartesianZornLinearEquiv.symm (real8CircularPeirceEquiv c)) i = c i := by
    rw [circularPeirceBasis_coordinate_eq_equivFun]
    exact congrFun (circularPeirce_coordinates_real8 c) i
  rw [circularPeirceBasis_norm_formula]
  rw [hcoord 0, hcoord 4, hcoord 1, hcoord 5,
    hcoord 2, hcoord 6, hcoord 3, hcoord 7]

/-- Main Witt-polarization theorem: the Zorn reduced norm of the polarized
Penrose carrier is exactly the real split-signature `(4,4)` sheet norm. -/
theorem penroseWittZorn_norm_eq_splitSignature (Z : Twistor4) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (penroseWittZornMap Z) =
      penroseRealSplitSignature Z := by
  change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      (real8CircularPeirceEquiv (penroseWittCoordinates Z)) = _
  rw [real8CircularPeirce_norm]
  simp [penroseWittCoordinates, penroseRealSplitSignature]
  ring

/-- Nullness is preserved exactly by the Witt-polarized Penrose-to-Zorn map. -/
theorem penrose_split_null_iff_zorn_null (Z : Twistor4) :
    penroseRealSplitSignature Z = 0 ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (penroseWittZornMap Z) = 0 := by
  rw [penroseWittZorn_norm_eq_splitSignature]

/-- Real rescaling changes the defect quadratically, hence preserves the null
locus for nonzero scale. -/
theorem penroseRealSplitSignature_smul (r : ℝ) (Z : Twistor4) :
    penroseRealSplitSignature (r • Z) = r ^ 2 * penroseRealSplitSignature Z := by
  simp [penroseRealSplitSignature]
  ring

end InfoGeometry.Twistor.PenroseZornWittBoundary
