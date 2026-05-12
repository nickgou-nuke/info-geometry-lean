import InfoGeometry.Krein.KreinSpace

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace

/-!
# Krein adjoint bridge

Alias layer to existing owner theorem surface in `InfoGeometry.Krein.KreinSpace`.
-/

namespace InfoGeometry.OperatorAlgebra

open scoped InnerProductSpace

section
variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

noncomputable def kreinAdjoint (A : H →L[ℝ] H) : H →L[ℝ] H :=
  InfoGeometry.Krein.KreinSpace.kreinAdjoint (H := H) A

@[simp] theorem kreinAdjoint_apply (A : H →L[ℝ] H) (u : H) :
    kreinAdjoint (H := H) A u
      = (KreinSpace.J : H ≃ₗᵢ[ℝ] H)
          (ContinuousLinearMap.adjoint A ((KreinSpace.J : H ≃ₗᵢ[ℝ] H) u)) :=
  InfoGeometry.Krein.KreinSpace.kreinAdjoint_apply (H := H) A u

@[simp] theorem kreinAdjoint_involutive (A : H →L[ℝ] H) :
    kreinAdjoint (H := H) (kreinAdjoint (H := H) A) = A :=
  InfoGeometry.Krein.KreinSpace.kreinAdjoint_involutive (H := H) A

end

end InfoGeometry.OperatorAlgebra
