import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers

/-!
# The certified `Fin 189` flag index

This owner packages the already proved canonical residual-fiber count as a
typed certificate.  It contains no table enumeration and no quotient
representative claims.
-/

namespace InfoGeometry.Algebra.Zorn.G2Fin189Certificate

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers

abbrev FlagFiber := Σ w : G2WeylElement, Fin (weylLength w) → Bool

noncomputable def flagFiberEquivFin189 : FlagFiber ≃ Fin 189 :=
  canonicalBinaryFlagIndexEquiv

@[simp] theorem flagFiberEquivFin189_apply (x : FlagFiber) :
    flagFiberEquivFin189 x = canonicalBinaryFlagIndexEquiv x :=
  rfl

theorem flagFiber_card : Fintype.card FlagFiber = 189 := by
  exact Fintype.card_congr flagFiberEquivFin189

theorem fin189_card : Fintype.card (Fin 189) = 189 := by
  simp

theorem flagFiber_equiv_fin189_surjective :
    Function.Surjective flagFiberEquivFin189 :=
  flagFiberEquivFin189.surjective

theorem flagFiber_equiv_fin189_injective :
    Function.Injective flagFiberEquivFin189 :=
  flagFiberEquivFin189.injective

end InfoGeometry.Algebra.Zorn.G2Fin189Certificate
