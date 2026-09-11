import InfoGeometry.Krein.HodgeStarOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DrazinHodgeChiralBridge

/-!
# Generic Hodge-star involution on the calibrated Drazin carrier

This is an explicit comparison interface between the minimal generic Hodge-star
owner and the repository's concrete Drazin Hodge/Dirac carrier.  The pointwise
compatibility hypothesis is intentional: the two owners use different
`KreinSpace` structures and cannot be identified from their types alone.
-/

namespace InfoGeometry.Canonical.HodgeStarOperatorDrazinBridge

open InfoGeometry.Krein.HodgeStarOperator
open InfoGeometry.Canonical

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [InfoGeometry.Krein.HodgeStarOperator.KreinSpace E]
variable (B : DrazinHodgeChiralBridge (E := E))

/-- The generic Hodge-star linear map on the Drazin carrier. -/
noncomputable def nativeHodgeStar : E →ₗ[ℝ] E :=
  InfoGeometry.Krein.HodgeStarOperator.hodgeStar E

/-- The explicit comparison datum between the two Hodge-star implementations. -/
def HodgeStarCompatibility : Prop :=
  ∀ x : E, B.hodgeStar x = nativeHodgeStar (E := E) x

theorem nativeHodgeStar_involutive (x : E) :
    nativeHodgeStar (E := E) (nativeHodgeStar (E := E) x) = x := by
  exact InfoGeometry.Krein.HodgeStarOperator.hodge_star_involutive E x

/-- The concrete Drazin Hodge star inherits involutivity from the generic owner
    once the carrier comparison is supplied. -/
theorem drazin_hodgeStar_involutive_of_compatibility
    (hCompat : HodgeStarCompatibility B) (x : E) :
    B.hodgeStar (B.hodgeStar x) = x := by
  rw [hCompat, hCompat]
  exact nativeHodgeStar_involutive (E := E) x

/-- The corresponding continuous operator square is the identity. -/
theorem drazin_hodgeStar_clm_sq_eq_one_of_compatibility
    (hCompat : HodgeStarCompatibility B) :
    B.hodgeStar * B.hodgeStar = (1 : E →L[ℝ] E) := by
  ext x
  change B.hodgeStar (B.hodgeStar x) = x
  exact drazin_hodgeStar_involutive_of_compatibility B hCompat x

/-- The Drazin Dirac square commutes pointwise with the generic Hodge star. -/
theorem drazin_laplacian_commutes_nativeHodgeStar_of_compatibility
    (hCompat : HodgeStarCompatibility B) (x : E) :
    B.hodgeLaplacian (nativeHodgeStar (E := E) x) =
      nativeHodgeStar (E := E) (B.hodgeLaplacian x) := by
  have hComm :
      B.hodgeLaplacian * B.CIK.GammaS =
        B.CIK.GammaS * B.hodgeLaplacian :=
    B.laplacian_commutes_GammaS
  have hPoint := congrArg (fun T : E →L[ℝ] E => T x) hComm
  change B.hodgeLaplacian (B.CIK.GammaS x) =
    B.CIK.GammaS (B.hodgeLaplacian x) at hPoint
  have hStarPoint : nativeHodgeStar (E := E) x = B.CIK.GammaS x := by
    calc
      nativeHodgeStar (E := E) x = B.hodgeStar x := (hCompat x).symm
      _ = B.CIK.GammaS x := by rw [B.hodgeStar_eq_GammaS]
  calc
    B.hodgeLaplacian (nativeHodgeStar (E := E) x) =
        B.hodgeLaplacian (B.CIK.GammaS x) := by rw [hStarPoint]
    _ = B.CIK.GammaS (B.hodgeLaplacian x) := hPoint
    _ = B.hodgeStar (B.hodgeLaplacian x) := by
      rw [B.hodgeStar_eq_GammaS]
    _ = nativeHodgeStar (E := E) (B.hodgeLaplacian x) :=
      hCompat (B.hodgeLaplacian x)

end Core

end InfoGeometry.Canonical.HodgeStarOperatorDrazinBridge
