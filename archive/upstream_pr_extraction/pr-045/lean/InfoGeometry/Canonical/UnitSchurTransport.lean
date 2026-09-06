import InfoGeometry.Canonical.CartanBerezinianCore
import InfoGeometry.Canonical.RealDoubledBlockOperator

/-! Unit lower-right block packaging for the native Schur transport owner. -/

namespace InfoGeometry.Canonical.UnitSchurTransport

open InfoGeometry.Canonical.CartanBerezinianCore
open InfoGeometry.Canonical.RealDoubledBlockOperator
open InfoGeometry.Krein

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E]

noncomputable def unitSchurAdmissibleTransport
    (A B C : E →L[ℝ] E)
    (S : E ≃L[ℝ] E)
    (hS : A - C.comp B = (S : E →L[ℝ] E)) :
    SchurAdmissibleTransport (E := E) where
  T := realDoubledBlockOperator A B C (ContinuousLinearMap.id ℝ E)
  Dinv := ContinuousLinearEquiv.refl ℝ E
  hD := by
    rw [minusBlockMap_realDoubledBlockOperator]
    rfl
  Schur := S
  hSchur := by
    simpa using hS

omit [CompleteSpace E] in
@[simp] theorem unitSchurAdmissibleTransport_schur
    (A B C : E →L[ℝ] E) (S : E ≃L[ℝ] E)
    (hS : A - C.comp B = (S : E →L[ℝ] E)) :
    (unitSchurAdmissibleTransport A B C S hS).Schur = S := rfl

end
end InfoGeometry.Canonical.UnitSchurTransport
