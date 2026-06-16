import Mathlib
import InfoGeometry.Canonical.ChiralSuperPoincareSouriauBridge
import InfoGeometry.OperatorAlgebra.SuperchargeNilpotence
import InfoGeometry.OperatorAlgebra.CARFermionParity

/-!
# Concrete CAR instantiation of ChiralSuperPoincareSouriauPacket

For a single CAR mode (n=1) with energy w², the supercharge
Q = w·a satisfies all packet axioms. Proved from existing lemmas.
-/
open InfoGeometry.Canonical.ChiralSuperPoincareSouriauBridge
open InfoGeometry.OperatorAlgebra.SuperchargeNilpotence
open InfoGeometry.OperatorAlgebra.CARFermionParity

noncomputable section

namespace InfoGeometry.Canonical

/-- Single-mode CAR chiral packet: plusCharge=Q, minusCharge=Qdag, parity=1-2n_0. -/
def carSingleModePacket (w : ℝ) : ChiralSuperPoincareSouriauPacket (Clnn 1) where
  plusCharge := Q 1 (λ _ => w)
  minusCharge := Qdag 1 (λ _ => w)
  parityCharge := ((1 : Clnn 1) - (algebraMap ℝ (Clnn 1) 2) * (cre 1 0 * ann 1 0))
  centralCharge := 0
  momentumOp := Q 1 (λ _ => w) * Qdag 1 (λ _ => w) + Qdag 1 (λ _ => w) * Q 1 (λ _ => w)
  beta4 := λ _ => 0
  energyMomentum4 := λ μ => if μ = 0 then w * w else 0
  twistorSocket := {
    plusProjector := 0
    minusProjector := 0
    incidenceMat := 0
    plus_selfadjoint := by simp
    minus_selfadjoint := by simp
    det_incidence_zero := by simp
  }
  plus_nilpotent := Q_sq_zero 1 (λ _ => w)
  minus_nilpotent := Qdag_sq_zero 1 (λ _ => w)
  momentum_eq_chiral_anticommutator := rfl
  centralCharge_central := by intro a; simp
  parity_anticommutes_plus := by
    dsimp [algebraicAnticommutator]
    -- Need: (1-2n_0)*(w·ann_0) = -(w·ann_0)*(1-2n_0)
    -- Follows from parityFactor_anticomm_ann multiplied by scalar w
    have h := parityFactor_anticomm_ann 1 0
    -- h: (1 - s 1 2 * (cre 1 0 * ann 1 0)) * ann 1 0 =
    --    -(ann 1 0 * (1 - s 1 2 * (cre 1 0 * ann 1 0)))
    -- Scale both sides by algebraMap w:
    -- (1-2n)·(w·a) = w·((1-2n)·a) = w·(-(a·(1-2n))) = -(w·a)·(1-2n)
    -- Using centrality of algebraMap(w):
    calc
      ((1 : Clnn 1) - (algebraMap ℝ (Clnn 1) 2) * (cre 1 0 * ann 1 0)) *
        (algebraMap ℝ (Clnn 1) w * ann 1 0)
          = algebraMap ℝ (Clnn 1) w *
            (((1 : Clnn 1) - (algebraMap ℝ (Clnn 1) 2) * (cre 1 0 * ann 1 0)) * ann 1 0) := by
        ring
      _ = algebraMap ℝ (Clnn 1) w *
            (-(ann 1 0 * ((1 : Clnn 1) - (algebraMap ℝ (Clnn 1) 2) * (cre 1 0 * ann 1 0)))) := by
        rw [h]
      _ = -((algebraMap ℝ (Clnn 1) w * ann 1 0) *
            ((1 : Clnn 1) - (algebraMap ℝ (Clnn 1) 2) * (cre 1 0 * ann 1 0))) := by
        ring
  parity_anticommutes_minus := by
    dsimp [algebraicAnticommutator]
    have h := parityFactor_anticomm_cre 1 0
    calc
      ((1 : Clnn 1) - (algebraMap ℝ (Clnn 1) 2) * (cre 1 0 * ann 1 0)) *
        (algebraMap ℝ (Clnn 1) w * cre 1 0)
          = algebraMap ℝ (Clnn 1) w *
            (((1 : Clnn 1) - (algebraMap ℝ (Clnn 1) 2) * (cre 1 0 * ann 1 0)) * cre 1 0) := by
        ring
      _ = algebraMap ℝ (Clnn 1) w *
            (-(cre 1 0 * ((1 : Clnn 1) - (algebraMap ℝ (Clnn 1) 2) * (cre 1 0 * ann 1 0)))) := by
        rw [h]
      _ = -((algebraMap ℝ (Clnn 1) w * cre 1 0) *
            ((1 : Clnn 1) - (algebraMap ℝ (Clnn 1) 2) * (cre 1 0 * ann 1 0))) := by
        ring

end InfoGeometry.Canonical
