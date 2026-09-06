import Mathlib.Analysis.InnerProductSpace.Dual
import InfoGeometry.Krein.KreinSpace

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace

namespace InfoGeometry.OperatorAlgebra

open scoped InnerProductSpace

section
variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

/-- Fréchet-Riesz readout on the Krein lane: precompose `toDual` with `J`. -/
noncomputable def kreinToDual (x : H) : StrongDual ℝ H :=
  (InnerProductSpace.toDual ℝ H) ((KreinSpace.J : H ≃ₗᵢ[ℝ] H) x)

@[simp] theorem kreinToDual_apply (x y : H) :
    kreinToDual x y = ⟪(KreinSpace.J : H ≃ₗᵢ[ℝ] H) x, y⟫_ℝ := rfl

end

end InfoGeometry.OperatorAlgebra
