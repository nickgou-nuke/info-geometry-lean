/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Canonical.KreinMajoranaZeroModeBlock
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Nonzero kernel vectors for the existing polarized-block Pfaffian bridge

The model equality and square-law witness remain explicit. A chiral projector
called zeroModeProjector is not, merely by its name, an energy-kernel projector.
-/
namespace InfoGeometry.Canonical.KreinMajoranaKernelCriterion

open KreinMajoranaZeroModeBlock ProjectivePfaffianDeterminantCounts
open InfoGeometry.Canonical.KKTCore

variable {H I : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [Fintype I] [DecidableEq I]

theorem polarized_nonzero_kernel_iff_pfaffian_zero
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : H →L[ℝ] H)
    (toMatrix : (H →L[ℝ] H) → Matrix I I ℝ)
    (P : PfaffianKernel I)
    (hModel : toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) =
      P.omega) :
    (∃ v : I → ℝ, v ≠ 0 ∧
      (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).mulVec v = 0) ↔
      P.pfaffian = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff]
  exact zeroMode_polarized_det_shadow_zero_iff_pfaffian_zero X A B toMatrix P hModel

end InfoGeometry.Canonical.KreinMajoranaKernelCriterion
