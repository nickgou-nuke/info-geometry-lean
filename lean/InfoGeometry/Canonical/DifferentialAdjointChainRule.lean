/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

/-!
# Differential chain rule with reverse adjoint transport

For two differentiable Hilbert-space stages, the derivative of their composite
is the forward composition of derivatives, while its Hilbert adjoint acts in
reverse stage order. This is the two-stage reverse-mode rule; it does not
assert a neural-network training theorem or an optimizer result.
-/

namespace InfoGeometry.Canonical.DifferentialAdjointChainRule

/-- The derivative chain rule together with its reverse-mode adjoint law. -/
theorem reverse_mode_chain_rule
    {𝕜 E F G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]
    [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    {f : E → F} {g : F → G} {x : E}
    {f' : E →L[𝕜] F} {g' : F →L[𝕜] G}
    (hf : HasFDerivAt f f' x)
    (hg : HasFDerivAt g g' (f x)) :
    HasFDerivAt (g ∘ f) (g'.comp f') x ∧
      ContinuousLinearMap.adjoint (g'.comp f') =
        (ContinuousLinearMap.adjoint f').comp
          (ContinuousLinearMap.adjoint g') := by
  constructor
  · exact hg.comp x hf
  · exact ContinuousLinearMap.adjoint_comp g' f'

/-- Reverse-mode differentiation for a real-valued loss: the gradient of the
composite is the adjoint of the stage derivative applied to the loss gradient.
This is a local differential statement, not a result about training or
optimization. -/
theorem gradient_comp_reverse_mode
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    {f : E → F} {loss : F → ℝ} {x : E}
    {Df : E →L[ℝ] F} {gradLoss : F}
    (hf : HasFDerivAt f Df x)
    (hloss : HasGradientAt loss gradLoss (f x)) :
    HasGradientAt (loss ∘ f)
      (ContinuousLinearMap.adjoint Df gradLoss) x := by
  have hchain := hloss.hasFDerivAt.comp x hf
  have hdual : InnerProductSpace.toDual ℝ E
        (ContinuousLinearMap.adjoint Df gradLoss) =
      (InnerProductSpace.toDual ℝ F gradLoss).comp Df := by
    ext v
    simpa only [InnerProductSpace.toDual_apply_apply,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_left Df v gradLoss)
  have hresult : HasFDerivAt (loss ∘ f)
      (InnerProductSpace.toDual ℝ E
        (ContinuousLinearMap.adjoint Df gradLoss)) x := by
    rw [hdual]
    exact hchain
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hresult.hasGradientAt

end InfoGeometry.Canonical.DifferentialAdjointChainRule
