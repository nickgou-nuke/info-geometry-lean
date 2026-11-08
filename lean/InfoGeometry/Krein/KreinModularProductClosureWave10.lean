/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.KreinModularConjugatedOperatorBridge

namespace InfoGeometry.Krein

open KreinSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]

local notation "EndH" => H →L[ℝ] H

/-- Modular conjugation is multiplicative on the native continuous-operator carrier. -/
theorem modularConjugatedOperator_mul
    (G : KreinSkewGenerator (H := H)) (t : ℝ) (B C : EndH) :
    modularConjugatedOperator G t (B * C) =
      modularConjugatedOperator G t B * modularConjugatedOperator G t C := by
  unfold modularConjugatedOperator
  have h_inv :
      G.modularFlow.flow (-t) * G.modularFlow.flow t =
        (1 : EndH) := by
    calc
      G.modularFlow.flow (-t) * G.modularFlow.flow t =
          G.modularFlow.flow ((-t) + t) := (G.flow_add (-t) t).symm
      _ = G.modularFlow.flow 0 := by rw [neg_add_cancel]
      _ = (1 : EndH) := by simpa using G.flow_zero
  calc
    G.modularFlow.flow t * (B * C) * G.modularFlow.flow (-t) =
        (G.modularFlow.flow t * B * G.modularFlow.flow (-t)) *
          (G.modularFlow.flow t * C * G.modularFlow.flow (-t)) := by
            simp only [mul_assoc]
            rw [← mul_assoc (G.modularFlow.flow (-t))
              (G.modularFlow.flow t) (C * G.modularFlow.flow (-t)), h_inv]
            simp only [one_mul]

end InfoGeometry.Krein
#print axioms InfoGeometry.Krein.modularConjugatedOperator_mul
