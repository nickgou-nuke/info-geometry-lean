import InfoGeometry.Projective.Rays
import InfoGeometry.Krein.KreinSpace

namespace ProjectiveRayBridge

open InfoGeometry.Krein
open InfoGeometry.Projective

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- Krein incidence relation on doubled states. -/
def Incidence (ψ φ : H₂) : Prop :=
  KreinSpace.kreinInner (H := H₂) ψ φ = 0

/-- Incidence is stable under rescaling of the left representative by a nonzero scalar. -/
theorem same_ray_incidence_left {ψ ψ' φ : H₂} (h : same_ray (E := E) ψ ψ') :
    Incidence ψ φ ↔ Incidence ψ' φ := by
  rcases h with ⟨c, hc, rfl⟩
  constructor
  · intro h0
    unfold Incidence at h0 ⊢
    rw [KreinSpace.kreinInner_smul_left, h0]
    ring
  · intro h0
    unfold Incidence at h0 ⊢
    rw [KreinSpace.kreinInner_smul_left] at h0
    exact (mul_eq_zero.mp h0).resolve_left hc

/-- Incidence is stable under rescaling of the right representative by a nonzero scalar. -/
theorem same_ray_incidence_right {ψ φ φ' : H₂} (h : same_ray (E := E) φ φ') :
    Incidence ψ φ ↔ Incidence ψ φ' := by
  rcases h with ⟨c, hc, rfl⟩
  constructor
  · intro h0
    unfold Incidence at h0 ⊢
    rw [KreinSpace.kreinInner_smul_right, h0]
    ring
  · intro h0
    unfold Incidence at h0 ⊢
    rw [KreinSpace.kreinInner_smul_right] at h0
    exact (mul_eq_zero.mp h0).resolve_left hc

end ProjectiveRayBridge
