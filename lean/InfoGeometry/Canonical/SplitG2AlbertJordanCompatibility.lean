/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Canonical.SplitG2AlbertEntrywiseLift
import InfoGeometry.Algebra.H3ZornCoordinateReadback
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
import InfoGeometry.Lie.CanonicalZornRootWittBlockBridge
import InfoGeometry.Lie.SplitDerivationCoordinates

noncomputable section

namespace InfoGeometry.Canonical.SplitG2AlbertJordanCompatibility

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
open InfoGeometry.Canonical.SplitG2AlbertEntrywiseLift
open InfoGeometry.Lie.CanonicalZornRootWittBlockBridge
open InfoGeometry.Lie.SplitDerivationCoordinates
open InfoGeometry.Lie.CanonicalZornDerivationDimension

abbrev G2Der := canonicalZornDerivations
abbrev Zorn := ZornVectorMatrix ℝ
abbrev H3 := H3Zorn ℝ

private abbrev vDer (D : G2Der) : ZornVectorMatrix.Derivation (R := ℝ) :=
  canonicalToVectorDerivation D

theorem zornDerivation_output_trace_zero (D : G2Der) (X : Zorn) :
    ZornVectorMatrix.trace (vDer D X) = 0 := by
  let p : Params := derivationParameters (vDer D)
  have hp : parameterDerivation p = vDer D := parameterLinearEquiv.right_inv (vDer D)
  rw [← hp]
  rcases X with ⟨a, v, w, b⟩
  simp [vDer, parameterDerivation, parameterAction, ZornVectorMatrix.trace]

theorem zornDerivation_output_conj_eq_neg (D : G2Der) (X : Zorn) :
    ZornVectorMatrix.conj (vDer D X) = ZornVectorMatrix.neg (vDer D X) := by
  rw [ZornVectorMatrix.conj_eq_scalar_trace_sub, zornDerivation_output_trace_zero]
  ext <;> simp [ZornVectorMatrix.scalar, ZornVectorMatrix.sub,
    ZornVectorMatrix.zero, ZornVectorMatrix.neg]

theorem zornDerivation_tracePair_skew (D : G2Der) (X Y : Zorn) :
    ZornVectorMatrix.trace
        (ZornVectorMatrix.mul (vDer D X) (ZornVectorMatrix.conj Y)) +
      ZornVectorMatrix.trace
        (ZornVectorMatrix.mul X (ZornVectorMatrix.conj (vDer D Y))) = 0 := by
  have h := derivation_native_witt_skew D
    (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.symm X)
    (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.symm Y)
  simpa [nativeCanonicalWittPairing, vDer, canonicalToVectorDerivation_apply,
    ZornVectorMatrix.trace_mul_comm] using h

end InfoGeometry.Canonical.SplitG2AlbertJordanCompatibility
