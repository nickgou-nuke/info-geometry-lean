import InfoGeometry.Optics.SheetWittCircularBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic loxodromic modes for two commuting operator involutions

This is the finite algebraic spectral statement behind the hyperbolic/circular
readout.  It uses the already constructed joint projectors and does not use
exponentials, logarithms, diagonal matrices, or a commutative replacement for
the operator algebra.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorLoxodromicModes

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.SheetWittCircularBasis

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

def modeSign (b : Bool) : ℝ :=
  if b then 1 else -1

def modeGenerator (S : CommutingInvolutions Op) (η θ : ℝ) : Op :=
  algebraMap ℝ Op η * S.hyperbolic + algebraMap ℝ Op θ * S.circular

local notation "Hproj " S => CommutingInvolutions.hyperbolicInvolution S
local notation "Cproj " S => CommutingInvolutions.circularInvolution S

private theorem hyperbolic_mul_selected_projector
    (S : CommutingInvolutions Op) (ε : Bool) :
    S.hyperbolic *
        choose ε (Hproj S).Pleft (Hproj S).Pright =
      algebraMap ℝ Op (modeSign ε) *
        choose ε (Hproj S).Pleft (Hproj S).Pright := by
  cases ε
  · change S.hyperbolic * (Hproj S).Pright =
      algebraMap ℝ Op (-1 : ℝ) * (Hproj S).Pright
    have hchi : (Hproj S).Pleft - (Hproj S).Pright = S.hyperbolic :=
      (Hproj S).Pleft_sub_Pright
    rw [← hchi]
    simp only [sub_mul, (Hproj S).Pleft_mul_Pright,
      (Hproj S).Pright_idem]
    simp
  · change S.hyperbolic * (Hproj S).Pleft =
      algebraMap ℝ Op (1 : ℝ) * (Hproj S).Pleft
    have hchi : (Hproj S).Pleft - (Hproj S).Pright = S.hyperbolic :=
      (Hproj S).Pleft_sub_Pright
    rw [← hchi]
    simp only [sub_mul, (Hproj S).Pleft_idem,
      (Hproj S).Pright_mul_Pleft]
    simp

private theorem circular_mul_selected_projector
    (S : CommutingInvolutions Op) (σ : Bool) :
    S.circular *
        choose σ (Cproj S).Pleft (Cproj S).Pright =
      algebraMap ℝ Op (modeSign σ) *
        choose σ (Cproj S).Pleft (Cproj S).Pright := by
  cases σ
  · change S.circular * (Cproj S).Pright =
      algebraMap ℝ Op (-1 : ℝ) * (Cproj S).Pright
    have hchi : (Cproj S).Pleft - (Cproj S).Pright = S.circular :=
      (Cproj S).Pleft_sub_Pright
    rw [← hchi]
    simp only [sub_mul, (Cproj S).Pleft_mul_Pright,
      (Cproj S).Pright_idem]
    simp
  · change S.circular * (Cproj S).Pleft =
      algebraMap ℝ Op (1 : ℝ) * (Cproj S).Pleft
    have hchi : (Cproj S).Pleft - (Cproj S).Pright = S.circular :=
      (Cproj S).Pleft_sub_Pright
    rw [← hchi]
    simp only [sub_mul, (Cproj S).Pleft_idem,
      (Cproj S).Pright_mul_Pleft]
    simp

theorem modeGenerator_mul_jointProjector
    (S : CommutingInvolutions Op) (η θ : ℝ) (ε σ : Bool) :
    modeGenerator S η θ * S.jointProjector ε σ =
      algebraMap ℝ Op (η * modeSign ε + θ * modeSign σ) *
        S.jointProjector ε σ := by
  unfold modeGenerator CommutingInvolutions.jointProjector
  let p : Op := choose ε (Hproj S).Pleft (Hproj S).Pright
  let q : Op := choose σ (Cproj S).Pleft (Cproj S).Pright
  change (algebraMap ℝ Op η * S.hyperbolic +
      algebraMap ℝ Op θ * S.circular) * (p * q) =
    algebraMap ℝ Op (η * modeSign ε + θ * modeSign σ) * (p * q)
  have hh := hyperbolic_mul_selected_projector S ε
  have hc := circular_mul_selected_projector S σ
  have hcomm := S.projector_commute ε σ
  have hcomm' : p * q = q * p := by
    change choose ε (Hproj S).Pleft (Hproj S).Pright *
      choose σ (Cproj S).Pleft (Cproj S).Pright =
        choose σ (Cproj S).Pleft (Cproj S).Pright *
          choose ε (Hproj S).Pleft (Hproj S).Pright
    simpa only [CommutingInvolutions.hyperbolicInvolution,
      CommutingInvolutions.circularInvolution] using hcomm
  change S.hyperbolic * p = algebraMap ℝ Op (modeSign ε) * p at hh
  change S.circular * q = algebraMap ℝ Op (modeSign σ) * q at hc
  calc
    (algebraMap ℝ Op η * S.hyperbolic +
        algebraMap ℝ Op θ * S.circular) * (p * q) =
        algebraMap ℝ Op η * ((S.hyperbolic * p) * q) +
          algebraMap ℝ Op θ * ((S.circular * q) * p) := by
      rw [add_mul]
      congr 1
      · simp only [mul_assoc]
      · rw [hcomm']
        simp only [mul_assoc]
    _ = algebraMap ℝ Op η *
          ((algebraMap ℝ Op (modeSign ε) * p) * q) +
          algebraMap ℝ Op θ *
            ((algebraMap ℝ Op (modeSign σ) * q) * p) := by rw [hh, hc]
    _ = algebraMap ℝ Op (η * modeSign ε) * (p * q) +
          algebraMap ℝ Op (θ * modeSign σ) * (q * p) := by
      congr 1
      · calc
          algebraMap ℝ Op η *
              ((algebraMap ℝ Op (modeSign ε) * p) * q) =
              (algebraMap ℝ Op η * algebraMap ℝ Op (modeSign ε)) *
                (p * q) := by noncomm_ring
          _ = algebraMap ℝ Op (η * modeSign ε) * (p * q) := by
            rw [← map_mul]
      · calc
          algebraMap ℝ Op θ *
              ((algebraMap ℝ Op (modeSign σ) * q) * p) =
              (algebraMap ℝ Op θ * algebraMap ℝ Op (modeSign σ)) *
                (q * p) := by noncomm_ring
          _ = algebraMap ℝ Op (θ * modeSign σ) * (q * p) := by
            rw [← map_mul]
    _ = algebraMap ℝ Op (η * modeSign ε + θ * modeSign σ) * (p * q) := by
      rw [← hcomm', ← add_mul, ← map_add]

theorem modeGenerator_mul_jointProjector_eq_zero_of_weight_zero
    (S : CommutingInvolutions Op) (η θ : ℝ) (ε σ : Bool)
    (hweight : η * modeSign ε + θ * modeSign σ = 0) :
    modeGenerator S η θ * S.jointProjector ε σ = 0 := by
  rw [modeGenerator_mul_jointProjector, hweight]
  simp

end InfoGeometry.Optics.OperatorLoxodromicModes
