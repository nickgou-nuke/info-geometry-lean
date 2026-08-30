/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Canonical.RealSplitOctonionAutTopology
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Bilinear owner for canonical Zorn multiplication

This file packages the already proved additivity and scalar-compatibility
laws for `zMul` as Mathlib's native bilinear linear-map constructor.  It adds
no algebraic or topological structure to the carrier.
-/

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore

noncomputable def zMulBilinear : CZ →ₗ[ℝ] CZ →ₗ[ℝ] CZ :=
  LinearMap.mk₂ ℝ zMul
    (fun X Y Z => zMul_add_left X Y Z)
    (fun r X Y => zMul_smul_left r X Y)
    (fun X Y Z => zMul_add_right X Y Z)
    (fun r X Y => zMul_smul_right r X Y)

@[simp] theorem zMulBilinear_apply (X Y : CZ) :
    zMulBilinear X Y = zMul X Y := rfl

theorem zMulBilinear_isLinearLeft (X : CZ) :
    IsLinearMap ℝ (zMul X) := by
  exact (zMulBilinear X).isLinear

theorem zMulBilinear_isLinearRight (Y : CZ) :
    IsLinearMap ℝ (fun X => zMul X Y) := by
  exact (zMulBilinear.flip Y).isLinear

end
end InfoGeometry.Canonical
