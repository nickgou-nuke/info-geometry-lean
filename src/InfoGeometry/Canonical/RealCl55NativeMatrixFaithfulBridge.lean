import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge

/-!
# Faithfulness of the native matrix transport

The finite matrix-to-native continuous-linear-map transport is injective.  No
completion or quotient is involved: this is the faithful finite-dimensional
readback supplied by the native matrix equivalence.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeMatrixFaithfulBridge

open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge

abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32

theorem nativeContinuous_injective :
    Function.Injective (nativeContinuous : Mat32 → NativeSpinorCLM) := by
  intro A B hAB
  have hlin := congrArg ContinuousLinearMap.toLinearMap hAB
  change Matrix.toEuclideanLin (nativeMatrix A) =
      Matrix.toEuclideanLin (nativeMatrix B) at hlin
  have hmatrix : nativeMatrix A = nativeMatrix B :=
    Matrix.toEuclideanLin.injective hlin
  exact (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).injective hmatrix

theorem nativeContinuous_eq_iff (A B : Mat32) :
    nativeContinuous A = nativeContinuous B ↔ A = B := by
  constructor
  · intro h
    exact nativeContinuous_injective h
  · intro h
    rw [h]

end InfoGeometry.Canonical.RealCl55NativeMatrixFaithfulBridge
