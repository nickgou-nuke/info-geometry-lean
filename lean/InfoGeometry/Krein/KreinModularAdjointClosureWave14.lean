/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.KreinModularProductClosureWave10

namespace InfoGeometry.Krein

open KreinSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]

local notation "EndH" => H →L[ℝ] H

/-- The Krein adjoint intertwines the canonical modular conjugation with
the same time parameter acting on the Krein adjoint of the observable. -/
theorem modularConjugatedOperator_kreinAdjoint
    (G : KreinSkewGenerator (H := H)) (t : ℝ) (B : EndH) :
    kreinAdjoint (modularConjugatedOperator G t B) =
      modularConjugatedOperator G t (kreinAdjoint B) := by
  unfold modularConjugatedOperator
  have hsharp : ∀ r : ℝ,
      kreinAdjoint (G.modularFlow.flow r) = G.modularFlow.flow (-r) := by
    intro r
    have hiso := (isKreinIsometry_iff_star_comp_self
      (G.modularFlow.flow r)).mp (G.flow_isKreinIsometry r)
    change kreinAdjoint (G.modularFlow.flow r) *
        G.modularFlow.flow r = (1 : EndH) at hiso
    have hleft :
        kreinAdjoint (G.modularFlow.flow r) *
            (G.modularFlow.flow r * G.modularFlow.flow (-r)) =
          (1 : EndH) * G.modularFlow.flow (-r) := by
      rw [← mul_assoc, hiso]
    rw [← G.flow_add r (-r), add_neg_cancel, G.flow_zero] at hleft
    simpa using hleft
  rw [kreinAdjoint_mul, kreinAdjoint_mul, hsharp, hsharp]
  simp only [neg_neg]
  rw [mul_assoc]

end InfoGeometry.Krein
