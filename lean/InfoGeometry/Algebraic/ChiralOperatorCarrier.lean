/-
InfoGeometry/Algebraic/ChiralOperatorCarrier.lean

Real chiral operator carrier on the doubled projective substrate.

This file stays in the real/Krein/operator language:
- the base substrate is the projective real carrier;
- `uPlus` and `uMinus` are the chiral lightcone projectors;
- `eps` is the fundamental chirality involution;
- `conformalOperator` is the derived phase axis `J ∘ ε`.
No `U(1)` primitive is introduced here.
-/

import InfoGeometry.ProjectiveFoundation
import InfoGeometry.Krein.InvolutiveSelfDualCarrier

noncomputable section

namespace InfoGeometry.Algebraic

open InfoGeometry.Krein

/--
Chiral operator carrier on a doubled Krein substrate.

The primitive data are real operatorial symmetries:
- `boost` is the swap/boost axis;
- `eps` is the chirality involution;
- `uPlus` and `uMinus` are the lightcone projectors;
- `conformalOperator` is the derived conformal phase axis.
-/
structure ChiralOperatorCarrier (X : InvolutiveSelfDualCarrier) where
  boost : X.H →L[ℝ] X.H
  eps : X.H →L[ℝ] X.H
  uPlus : X.H →L[ℝ] X.H
  uMinus : X.H →L[ℝ] X.H
  boost_sq : boost.comp boost = ContinuousLinearMap.id ℝ X.H
  boost_eps_anticomm : boost.comp eps = -(eps.comp boost)
  eps_sq : eps.comp eps = ContinuousLinearMap.id ℝ X.H
  uPlus_idempotent : uPlus.comp uPlus = uPlus
  uMinus_idempotent : uMinus.comp uMinus = uMinus
  uPlus_add_uMinus : uPlus + uMinus = ContinuousLinearMap.id ℝ X.H
  uPlus_comp_uMinus : uPlus.comp uMinus = 0
  uMinus_comp_uPlus : uMinus.comp uPlus = 0
  conformal_sq_neg_id :
    (boost.comp eps).comp (boost.comp eps) = -(ContinuousLinearMap.id ℝ X.H)

namespace ChiralOperatorCarrier

variable {X : InvolutiveSelfDualCarrier}

/-- The conformal phase axis derived from the primitive boost and chirality maps. -/
def conformalOperator (C : ChiralOperatorCarrier X) : X.H →L[ℝ] X.H :=
  C.boost.comp C.eps

@[simp] theorem conformal_eq (C : ChiralOperatorCarrier X) :
    C.conformalOperator = C.boost.comp C.eps := rfl

/-- The canonical chiral operator carrier built from the repo-owned doubled packet. -/
noncomputable def canonicalChiralOperatorCarrier : ChiralOperatorCarrier X where
  boost := X.J
  eps := X.ε
  uPlus := X.Pplus
  uMinus := X.Pminus
  boost_sq := X.J_sq
  boost_eps_anticomm := X.J_ε_anticomm
  eps_sq := X.ε_sq
  uPlus_idempotent := X.Pplus_idempotent
  uMinus_idempotent := X.Pminus_idempotent
  uPlus_add_uMinus := X.Pplus_add_Pminus
  uPlus_comp_uMinus := X.Pplus_comp_Pminus
  uMinus_comp_uPlus := X.Pminus_comp_Pplus
  conformal_sq_neg_id := X.K_sq

@[simp] theorem canonicalChiralOperatorCarrier_boost_eq_modular_j :
    (canonicalChiralOperatorCarrier (X := X)).boost = X.J := rfl

@[simp] theorem canonicalChiralOperatorCarrier_eps_eq_spectral_epsilon :
    (canonicalChiralOperatorCarrier (X := X)).eps = X.ε := rfl

@[simp] theorem canonicalChiralOperatorCarrier_uPlus_eq_Pplus :
    (canonicalChiralOperatorCarrier (X := X)).uPlus = X.Pplus := rfl

@[simp] theorem canonicalChiralOperatorCarrier_uMinus_eq_Pminus :
    (canonicalChiralOperatorCarrier (X := X)).uMinus = X.Pminus := rfl

@[simp] theorem canonicalChiralOperatorCarrier_conformalOperator_eq_K :
    (canonicalChiralOperatorCarrier (X := X)).conformalOperator = X.K := rfl

theorem canonicalChiralOperatorCarrier_eps_eq_uPlus_sub_uMinus :
    (canonicalChiralOperatorCarrier (X := X)).eps =
      (canonicalChiralOperatorCarrier (X := X)).uPlus -
        (canonicalChiralOperatorCarrier (X := X)).uMinus := by
  simpa [canonicalChiralOperatorCarrier] using X.ε_eq_Pplus_sub_Pminus

theorem canonicalChiralOperatorCarrier_root_laws :
    let C := canonicalChiralOperatorCarrier (X := X)
    C.boost = X.J ∧
      C.eps = X.ε ∧
      C.uPlus = X.Pplus ∧
      C.uMinus = X.Pminus ∧
      C.conformalOperator = X.K ∧
      C.conformalOperator.comp C.conformalOperator =
        -(ContinuousLinearMap.id ℝ X.H) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact X.K_sq

end ChiralOperatorCarrier

end InfoGeometry.Algebraic
