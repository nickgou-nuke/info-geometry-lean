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

/-- The modular boost readout. -/
def boost (C : InvolutiveSelfDualCarrier) : C.H →L[ℝ] C.H := C.J

/-- The spectral chirality readout. -/
def eps (C : InvolutiveSelfDualCarrier) : C.H →L[ℝ] C.H := C.ε

/-- The positive chiral projector readout. -/
def uPlus (C : InvolutiveSelfDualCarrier) : C.H →L[ℝ] C.H := C.Pplus

/-- The negative chiral projector readout. -/
def uMinus (C : InvolutiveSelfDualCarrier) : C.H →L[ℝ] C.H := C.Pminus

/-- The conformal phase axis readout, already owned as `X.K`. -/
def conformalOperator (C : InvolutiveSelfDualCarrier) : C.H →L[ℝ] C.H := C.K

/-- Canonical carrier construction is identity transport, not a copied packet. -/
abbrev canonicalChiralOperatorCarrier : InvolutiveSelfDualCarrier := X

@[simp] theorem canonicalChiralOperatorCarrier_boost_eq_modular_j :
    boost (canonicalChiralOperatorCarrier (X := X)) = X.J := rfl

@[simp] theorem canonicalChiralOperatorCarrier_eps_eq_spectral_epsilon :
    eps (canonicalChiralOperatorCarrier (X := X)) = X.ε := rfl

@[simp] theorem canonicalChiralOperatorCarrier_uPlus_eq_Pplus :
    uPlus (canonicalChiralOperatorCarrier (X := X)) = X.Pplus := rfl

@[simp] theorem canonicalChiralOperatorCarrier_uMinus_eq_Pminus :
    uMinus (canonicalChiralOperatorCarrier (X := X)) = X.Pminus := rfl

@[simp] theorem canonicalChiralOperatorCarrier_conformalOperator_eq_K :
    conformalOperator (canonicalChiralOperatorCarrier (X := X)) = X.K := rfl

theorem canonicalChiralOperatorCarrier_eps_eq_uPlus_sub_uMinus :
    eps (canonicalChiralOperatorCarrier (X := X)) =
      uPlus (canonicalChiralOperatorCarrier (X := X)) -
        uMinus (canonicalChiralOperatorCarrier (X := X)) := by
  simpa [eps, uPlus, uMinus] using X.ε_eq_Pplus_sub_Pminus

theorem canonicalChiralOperatorCarrier_root_laws :
    let C := canonicalChiralOperatorCarrier (X := X)
    boost C = X.J ∧
      eps C = X.ε ∧
      uPlus C = X.Pplus ∧
      uMinus C = X.Pminus ∧
      conformalOperator C = X.K ∧
      (conformalOperator C).comp (conformalOperator C) =
        -(ContinuousLinearMap.id ℝ X.H) := by
  dsimp [boost, eps, uPlus, uMinus, conformalOperator]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact X.K_sq

end ChiralOperatorCarrier

end InfoGeometry.Algebraic
