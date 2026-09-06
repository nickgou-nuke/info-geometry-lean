import InfoGeometry.Tessellation.CantorDiracSeaWalk
import InfoGeometry.Clifford.RealDoubledHestenesAnchor
import InfoGeometry.Krein.DoubledSpace

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Clifford.CantorDiracSeaHestenesBridge

open InfoGeometry.Tessellation
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Krein

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

theorem phaseAxis_sq :
    InfoGeometry.Krein.doubledI (E := E) *
        InfoGeometry.Krein.doubledI (E := E) =
      -(1 : H₂ →L[ℝ] H₂) :=
  InfoGeometry.Krein.doubledI_sq (E := E)

theorem rotor_commutes_phaseAxis
    (rotor : ℝ → H₂ →L[ℝ] H₂)
    (rotor_preserves_phaseAxis :
      ∀ t : ℝ,
        rotor t ∘L InfoGeometry.Krein.doubledI (E := E) =
          InfoGeometry.Krein.doubledI (E := E) ∘L rotor t)
    (t : ℝ) :
    rotor t ∘L InfoGeometry.Krein.doubledI (E := E) =
      InfoGeometry.Krein.doubledI (E := E) ∘L rotor t :=
  rotor_preserves_phaseAxis t

theorem rotor_preserves_null_cone
    (rotor : ℝ → H₂ →L[ℝ] H₂)
    (rotor_preserves_doubledInner :
      ∀ (t : ℝ) (ξ η : H₂),
        ⟪rotor t ξ, rotor t η⟫_ℝ = ⟪ξ, η⟫_ℝ)
    (t : ℝ) {ξ : H₂}
    (h_null : ⟪ξ, ξ⟫_ℝ = 0) :
    ⟪rotor t ξ, rotor t ξ⟫_ℝ = 0 := by
  rw [rotor_preserves_doubledInner t ξ ξ]
  exact h_null

theorem leftHop_realization_square_zero
    (realizeLeftHop : FiniteBinaryWord → H₂ →L[ℝ] H₂)
    (realizeLeftHop_square_zero :
      ∀ w : FiniteBinaryWord,
        realizeLeftHop w ∘L realizeLeftHop w = 0)
    (w : FiniteBinaryWord) :
    realizeLeftHop w ∘L realizeLeftHop w = 0 :=
  realizeLeftHop_square_zero w

theorem rightHop_realization_square_zero
    (realizeRightHop : FiniteBinaryWord → H₂ →L[ℝ] H₂)
    (realizeRightHop_square_zero :
      ∀ w : FiniteBinaryWord,
        realizeRightHop w ∘L realizeRightHop w = 0)
    (w : FiniteBinaryWord) :
    realizeRightHop w ∘L realizeRightHop w = 0 :=
  realizeRightHop_square_zero w

theorem owner_leftHop_square_zero
    {Op Charge : Type*} [Ring Op]
    (walk : Tessellation.CantorDiracSeaWalkDatum Op Charge)
    (leftHop_square_zero :
      ∀ w : List Bool,
        (walk.leftHop w).N * (walk.leftHop w).N = 0)
    (w : List Bool) :
    (walk.leftHop w).N * (walk.leftHop w).N = 0 :=
  leftHop_square_zero w

theorem owner_rightHop_square_zero
    {Op Charge : Type*} [Ring Op]
    (walk : Tessellation.CantorDiracSeaWalkDatum Op Charge)
    (rightHop_square_zero :
      ∀ w : List Bool,
        (walk.rightHop w).N * (walk.rightHop w).N = 0)
    (w : List Bool) :
    (walk.rightHop w).N * (walk.rightHop w).N = 0 :=
  rightHop_square_zero w

theorem doubledIBivector_square_neg :
    (InfoGeometry.Clifford.RealDoubledHestenesAnchor.doubledIBivector
      (E := E)).square_neg =
      InfoGeometry.Krein.doubledI_sq (E := E) := by
  rfl

end InfoGeometry.Clifford.CantorDiracSeaHestenesBridge
