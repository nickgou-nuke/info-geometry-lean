import InfoGeometry.Quantum.PACKreinEquivalence
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-!
# PAC/Krein bridge to the generic neutral quadratic form

The PAC/Krein owner already proves preservation of its normalized neutral
pairing.  This file identifies that pairing with Mathlib's generic
`V ⊕ V*` bilinear and quadratic forms, including the exact normalization.
-/

namespace InfoGeometry.Quantum.PACKreinNeutralFormBridge

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Quantum.DualFlatKreinGraph
open InfoGeometry.Quantum.PACKreinEquivalence
open ProjectiveAffineConformalClosure55

noncomputable section

theorem pacToKrein_canonicalNeutralBilin_eq_Q44Polar
    (E : Vector 4 ≃ₗ[ℝ] Covector 4)
    (hE : CoordinateCompatible E)
    (X Y : PACSplit44) :
    canonicalNeutralBilin (E := Vector 4)
        (pacToKrein E X) (pacToKrein E Y) =
      2 * pacQ44Polar X Y := by
  calc
    canonicalNeutralBilin (E := Vector 4)
        (pacToKrein E X) (pacToKrein E Y) =
        2 * neutralPair (pacToKrein E X) (pacToKrein E Y) := by
          simp [canonicalNeutralBilin_apply, neutralPair]
          ring
    _ = 2 * pacQ44Polar X Y := by
      rw [pacToKrein_neutralPair_eq_Q44Polar E hE X Y]

theorem pacToKrein_canonicalNeutralFormUnscaled_eq_Q44
    (E : Vector 4 ≃ₗ[ℝ] Covector 4)
    (hE : CoordinateCompatible E)
    (X : PACSplit44) :
    canonicalNeutralFormUnscaled (E := Vector 4) (pacToKrein E X) =
      Q44 X := by
  calc
    canonicalNeutralFormUnscaled (E := Vector 4) (pacToKrein E X) =
        neutralPair (pacToKrein E X) (pacToKrein E X) := by
          simp [canonicalNeutralFormUnscaled_apply, neutralPair]
    _ = Q44 X := pacToKrein_neutralPair_self_eq_Q44 E hE X

end

end InfoGeometry.Quantum.PACKreinNeutralFormBridge
