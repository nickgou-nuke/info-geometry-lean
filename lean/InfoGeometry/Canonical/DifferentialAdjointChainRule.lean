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

end InfoGeometry.Canonical.DifferentialAdjointChainRule
