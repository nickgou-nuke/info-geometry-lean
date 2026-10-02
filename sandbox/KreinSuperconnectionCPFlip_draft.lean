import InfoGeometry.Canonical.SuperconnectionZornBianchiBridge
import InfoGeometry.Krein.KreinSpace

open InfoGeometry.Canonical.Superconnection
open InfoGeometry.Krein

variable {H : Type*}
variable [NonUnitalNonAssocRing H] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

def cpFlip (w : NonAssocGradedMaurerCartanForm H) : NonAssocGradedMaurerCartanForm H :=
  { w_n2 := jCLM w.w_p2
  , w_n1 := jCLM w.w_p1
  , w_0  := jCLM w.w_0
  , w_p1 := jCLM w.w_n1
  , w_p2 := jCLM w.w_n2 }

theorem cpFlip_involutive (w : NonAssocGradedMaurerCartanForm H) : cpFlip (cpFlip w) = w := by
  have h_jCLM : ∀ x : H, jCLM (jCLM x) = x := by
    intro x
    show (J : H ≃ₗᵢ[ℝ] H) ((J : H ≃ₗᵢ[ℝ] H) x) = x
    exact KreinSpace.J_invol x
  cases w
  dsimp [cpFlip]
  congr 1 <;> exact h_jCLM _
