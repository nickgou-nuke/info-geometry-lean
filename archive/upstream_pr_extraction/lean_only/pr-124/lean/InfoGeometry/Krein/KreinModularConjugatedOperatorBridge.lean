import InfoGeometry.Krein.KreinModularCartanCompatibility
import InfoGeometry.Krein.Thermal

namespace InfoGeometry.Krein

open KreinSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]

local notation "EndH" => H →L[ℝ] H

/-- The operator-valued modular conjugation written using the native modular
flow and its negative-time slice. -/
noncomputable def modularConjugatedOperator
    (G : KreinSkewGenerator (H := H)) (t : ℝ) (B : EndH) : EndH :=
  G.modularFlow.flow t * B * G.modularFlow.flow (-t)

theorem modularConjugatedOperator_eq_kreinModularShift
    (G : KreinSkewGenerator (H := H)) (t : ℝ) (B : EndH) :
    modularConjugatedOperator G t B =
      krein_modular_shift G.1 t B := by
  rfl

@[simp] theorem modularConjugatedOperator_zero
    (G : KreinSkewGenerator (H := H)) (B : EndH) :
    modularConjugatedOperator G 0 B = B := by
  rw [modularConjugatedOperator_eq_kreinModularShift]
  exact krein_modular_shift_zero G.1 B

theorem modularConjugatedOperator_add
    (G : KreinSkewGenerator (H := H)) (s t : ℝ) (B : EndH) :
    modularConjugatedOperator G (s + t) B =
      modularConjugatedOperator G s
        (modularConjugatedOperator G t B) := by
  rw [modularConjugatedOperator_eq_kreinModularShift,
    modularConjugatedOperator_eq_kreinModularShift,
    modularConjugatedOperator_eq_kreinModularShift]
  exact krein_modular_shift_add G.1 s t B

end InfoGeometry.Krein
