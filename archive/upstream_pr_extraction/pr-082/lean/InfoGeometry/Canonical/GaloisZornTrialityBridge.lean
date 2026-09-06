import InfoGeometry.Canonical.BostConnesGalois
import InfoGeometry.Canonical.ZornCore
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# Cyclotomic Galois Action on ZornCore Triality

This module records an additive `ZMod 3` cyclic action on the ZornCore carrier.
The cyclotomic unit character takes values in `(ZMod 3)ˣ`; identifying that
multiplicative character with this additive cyclic action is a separate bridge.
-/

namespace InfoGeometry.Canonical.GaloisZornTrialityBridge

open InfoGeometry.Canonical.BostConnesGalois
open InfoGeometry.Canonical.CurrentSugawaraBridge
open Complex

/-- The Galois action on the ZornCore triality, parameterized by the cyclotomic character value. -/
def galoisActionOnTriality (X : ZornCore.Zorn) (χ : ZMod 3) : ZornCore.Zorn :=
  match χ with
  | 0 => X
  | 1 => ZornCore.triality X
  | 2 => ZornCore.triality (ZornCore.triality X)

/-- The Galois action commutes with the ZornCore determinant (norm). -/
theorem galoisActionOnTriality_preserves_det
    (X : ZornCore.Zorn) (χ : ZMod 3) :
    ZornCore.det (galoisActionOnTriality X χ) = ZornCore.det X := by
  fin_cases χ <;>
    simp [galoisActionOnTriality, ZornCore.det_invariant]

/-- The Galois action on triality is a group homomorphism in the character. -/
theorem galoisActionOnTriality_homomorphism
    (X : ZornCore.Zorn) (χ ψ : ZMod 3) :
    galoisActionOnTriality X (χ + ψ) =
      galoisActionOnTriality (galoisActionOnTriality X ψ) χ := by
  fin_cases χ
  · fin_cases ψ
    · rfl
    · rfl
    · rfl
  · fin_cases ψ
    · rfl
    · rfl
    · change X = ZornCore.triality
        (ZornCore.triality (ZornCore.triality X))
      rw [ZornCore.triality_order_3]
  · fin_cases ψ
    · rfl
    · change X = ZornCore.triality
        (ZornCore.triality (ZornCore.triality X))
      rw [ZornCore.triality_order_3]
    · change ZornCore.triality X =
        ZornCore.triality (ZornCore.triality
          (ZornCore.triality (ZornCore.triality X)))
      rw [ZornCore.triality_order_3]

/-- The ZornCore triality has order three. -/
theorem triality_order_3 :
    ∀ (X : ZornCore.Zorn),
      ZornCore.triality (ZornCore.triality (ZornCore.triality X)) = X := by
  intro X
  exact ZornCore.triality_order_3 X

/-- The ZornCore determinant is invariant under triality. -/
theorem det_invariant_under_triality :
    ∀ (X : ZornCore.Zorn),
      ZornCore.det (ZornCore.triality X) = ZornCore.det X := by
  intro X
  exact ZornCore.det_invariant X

end InfoGeometry.Canonical.GaloisZornTrialityBridge
