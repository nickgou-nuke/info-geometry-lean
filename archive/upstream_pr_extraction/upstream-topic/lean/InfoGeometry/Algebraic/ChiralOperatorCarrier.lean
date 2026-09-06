/-
InfoGeometry/Algebraic/ChiralOperatorCarrier.lean

Named readouts for the repository-owned doubled involutive carrier.
The former duplicate carrier structure has been removed: its operators and
projector laws are already owned by `InvolutiveSelfDualCarrier`.
-/

import InfoGeometry.ProjectiveFoundation
import InfoGeometry.Krein.InvolutiveSelfDualCarrier

noncomputable section

namespace InfoGeometry.Algebraic

open InfoGeometry.Krein

namespace ChiralOperatorCarrier

variable {X : InvolutiveSelfDualCarrier}

theorem canonicalChiralOperatorCarrier_eps_eq_uPlus_sub_uMinus :
    X.ε = X.Pplus - X.Pminus := X.ε_eq_Pplus_sub_Pminus

theorem canonicalChiralOperatorCarrier_root_laws :
    X.J = X.J ∧
      X.ε = X.ε ∧
      X.Pplus = X.Pplus ∧
      X.Pminus = X.Pminus ∧
      X.K = X.K ∧
      X.K.comp X.K =
        -(ContinuousLinearMap.id ℝ X.H) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact X.K_sq

end ChiralOperatorCarrier

end InfoGeometry.Algebraic
