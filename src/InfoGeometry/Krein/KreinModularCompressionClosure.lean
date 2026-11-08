/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.KreinModularConjugatedCartanBridge

namespace InfoGeometry.Krein

open KreinSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]

/-- Modular conjugation transports the compression of an operator to the
ε-plus sector to the compression of its modular conjugate.
The statement uses the actual native flow and projector carriers. -/
theorem modularConjugatedOperator_positive_compression
    (X : InvolutiveSelfDualCarrier)
    (G : KreinSkewGenerator (H := X.H))
    (C : ModularCartanCompatibility X G)
    (t : ℝ) (B : X.H →L[ℝ] X.H) :
    modularConjugatedOperator G t (X.Pplus.comp (B.comp X.Pplus)) =
      X.Pplus.comp ((modularConjugatedOperator G t B).comp X.Pplus) := by
  ext x
  change G.modularFlow.flow t
      (X.Pplus (B (X.Pplus (G.modularFlow.flow (-t) x)))) =
    X.Pplus (G.modularFlow.flow t
      (B (G.modularFlow.flow (-t) (X.Pplus x))))
  rw [modularFlow_preserves_Pplus X G C t]
  rw [modularFlow_preserves_Pplus X G C (-t)]

/-- The same modular transport law holds for compression to the ε-minus
sector. -/
theorem modularConjugatedOperator_negative_compression
    (X : InvolutiveSelfDualCarrier)
    (G : KreinSkewGenerator (H := X.H))
    (C : ModularCartanCompatibility X G)
    (t : ℝ) (B : X.H →L[ℝ] X.H) :
    modularConjugatedOperator G t (X.Pminus.comp (B.comp X.Pminus)) =
      X.Pminus.comp ((modularConjugatedOperator G t B).comp X.Pminus) := by
  ext x
  change G.modularFlow.flow t
      (X.Pminus (B (X.Pminus (G.modularFlow.flow (-t) x)))) =
    X.Pminus (G.modularFlow.flow t
      (B (G.modularFlow.flow (-t) (X.Pminus x))))
  rw [modularFlow_preserves_Pminus X G C t]
  rw [modularFlow_preserves_Pminus X G C (-t)]

end InfoGeometry.Krein
