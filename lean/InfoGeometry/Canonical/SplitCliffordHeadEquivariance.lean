import InfoGeometry.Canonical.SplitCliffordHeadProjectors
import Mathlib.Tactic.Module

/-!
# InfoGeometry.Canonical.SplitCliffordHeadEquivariance

Head-level phase-flip equivariance on the Bott tensor side.

This file is a translator surface above the canonical head projector lane. It
does not introduce a new anomaly primitive. It only packages the residual of
the canonical head `K`-flip and identifies the fixed versus anti-fixed
projector combinations.
-/

namespace SplitCliffordHeadEquivariance

open InfoGeometry.Canonical.SplitCliffordHeadLift
open InfoGeometry.Canonical.SplitCliffordHeadPhaseFlip
open InfoGeometry.Canonical.SplitCliffordHeadProjectors
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- The residual of the canonical head `K`-flip on the Bott tensor side. -/
@[rep_depth krein]
noncomputable def headKFlipResidualTensor (n : ℕ) (x : SplitClNNTensorStep n) :
    SplitClNNTensorStep n :=
  headKFlipTensor n x - x

/-- The head projector difference is exactly `-ε` on the Bott tensor side. -/
@[rep_depth krein, simp] theorem headEpsProjectorTensor_diff_eq_neg_headEpsTensor (n : ℕ) :
    headEpsMinusProjectorTensor n - headEpsPlusProjectorTensor n = -headEpsTensor n := by
  rw [headEpsMinusProjectorTensor_eq_formula, headEpsPlusProjectorTensor_eq_formula]
  simp [sub_eq_add_neg, smul_add]
  module

/-- The head `K`-flip residual vanishes on the fixed projector sum. -/
@[rep_depth krein, simp] theorem headKFlipResidualTensor_apply_headEpsProjectorTensor_sum
    (n : ℕ) :
    headKFlipResidualTensor n
        (headEpsMinusProjectorTensor n + headEpsPlusProjectorTensor n) = 0 := by
  unfold headKFlipResidualTensor
  rw [headKFlipTensor_apply_headEpsProjectorTensor_sum, sub_self]

/-- Explicit vanishing closure for the canonical head `K`-flip residual. -/
@[rep_depth krein, simp] theorem headKFlipResidualTensor_vanishes_on_headEpsProjectorTensor_sum
    (n : ℕ) :
    headKFlipResidualTensor n
        (headEpsMinusProjectorTensor n + headEpsPlusProjectorTensor n) = 0 :=
  headKFlipResidualTensor_apply_headEpsProjectorTensor_sum n

/-- The head projector difference is anti-fixed under the head `K`-flip. -/
@[rep_depth krein, simp] theorem headKFlipTensor_apply_headEpsProjectorTensor_diff
    (n : ℕ) :
    headKFlipTensor n (headEpsMinusProjectorTensor n - headEpsPlusProjectorTensor n)
      = -(headEpsMinusProjectorTensor n - headEpsPlusProjectorTensor n) := by
  rw [sub_eq_add_neg, map_add, map_neg,
    headKFlipTensor_apply_headEpsMinusProjectorTensor,
    headKFlipTensor_apply_headEpsPlusProjectorTensor]
  abel_nf

/-- The head `K`-flip residual of the projector difference is `-2` times that difference. -/
@[rep_depth krein, simp] theorem headKFlipResidualTensor_apply_headEpsProjectorTensor_diff
    (n : ℕ) :
    headKFlipResidualTensor n
        (headEpsMinusProjectorTensor n - headEpsPlusProjectorTensor n)
      = -((2 : ℝ) • (headEpsMinusProjectorTensor n - headEpsPlusProjectorTensor n)) := by
  unfold headKFlipResidualTensor
  rw [headKFlipTensor_apply_headEpsProjectorTensor_diff]
  module

/-- The head `K`-flip residual of head `ε` is `-2 ε`. -/
@[rep_depth krein, simp] theorem headKFlipResidualTensor_apply_headEpsTensor (n : ℕ) :
    headKFlipResidualTensor n (headEpsTensor n)
      = -((2 : ℝ) • headEpsTensor n) := by
  unfold headKFlipResidualTensor
  rw [headKFlipTensor_apply_headEpsTensor]
  module

end SplitCliffordHeadEquivariance
