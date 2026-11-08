import InfoGeometry.Canonical.ChiralSuperPoincareSouriauBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.TwistorSpace
import InfoGeometry.OperatorAlgebra.SuperchargeNilpotence
import InfoGeometry.OperatorAlgebra.CARFermionParity
import InfoGeometry.OperatorAlgebra.CliffordCAR

/-!
# Concrete CAR instantiation of ChiralSuperPoincareSouriauPacket

For a single CAR mode (n=1) with energy w², the supercharge
Q = w·a satisfies all packet axioms. Proved from existing lemmas.
-/
open InfoGeometry.Canonical.ChiralSuperPoincareSouriauBridge
open InfoGeometry.OperatorAlgebra.SuperchargeNilpotence
open InfoGeometry.OperatorAlgebra.CARFermionParity
open InfoGeometry.OperatorAlgebra.CliffordCAR
open InfoGeometry.Algebra.SupergradedSUSY

noncomputable section

namespace InfoGeometry.Canonical

/-- Single-mode CAR chiral packet: plusCharge=Q, minusCharge=Qdag, parity=1-2n_0. -/
def carSingleModePacket (w : ℝ) : ChiralSuperPoincareSouriauPacket (Clnn 1) where
  plusCharge := InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w)
  minusCharge := InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w)
  parityCharge := ((1 : Clnn 1) - (algebraMap ℝ (Clnn 1) 2) * (cre 1 0 * ann 1 0))
  centralCharge := 0
  momentumOp := InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w) * InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w) + InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w) * InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w)
  beta4 := λ _ => 0
  energyMomentum4 := λ μ => if μ = 0 then w * w else 0
  twistorSocket := {
    nullCone := fun _ =>
      InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w) *
          InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w) = 0 ∧
        InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w) *
          InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w) = 0
    incidence := fun _ _ =>
      InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w) *
          InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w) +
        InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w) *
          InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w) =
        InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w) *
          InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w) +
        InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w) *
          InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w)
    chiralPlus := fun _ =>
      InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w) *
        InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q 1 (λ _ => w) = 0
    chiralMinus := fun _ =>
      InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w) *
        InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag 1 (λ _ => w) = 0
    plus_incidence_null := fun _ _ hplus _ =>
      ⟨hplus, Qdag_sq_zero 1 (λ _ => w)⟩
    minus_incidence_null := fun _ _ hminus _ =>
      ⟨Q_sq_zero 1 (λ _ => w), hminus⟩
  }
  plus_nilpotent := Q_sq_zero 1 (λ _ => w)
  minus_nilpotent := Qdag_sq_zero 1 (λ _ => w)
  momentum_eq_chiral_anticommutator := rfl
  centralCharge_central := by intro a; simp
  parity_anticommutes_plus := by
    dsimp [algebraicAnticommutator, InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Q]
    rw [Fin.sum_univ_one]
    have h := InfoGeometry.OperatorAlgebra.CARFermionParity.parityFactor_anticomm_ann 1 0
    have comm1 : (1 - algebraMap ℝ (Clnn 1) 2 * (cre 1 0 * ann 1 0)) * InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.s 1 w = InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.s 1 w * (1 - algebraMap ℝ (Clnn 1) 2 * (cre 1 0 * ann 1 0)) := by
      dsimp [InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.s]
      exact (Algebra.commutes w _).symm
    rw [← mul_assoc (1 - _), comm1, mul_assoc (InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.s 1 w)]
    rw [mul_assoc (InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.s 1 w)]
    have h_h : (1 - algebraMap ℝ (Clnn 1) 2 * (cre 1 0 * ann 1 0)) * ann 1 0 = -(ann 1 0 * (1 - algebraMap ℝ (Clnn 1) 2 * (cre 1 0 * ann 1 0))) := h
    rw [h_h, mul_neg, neg_add_cancel]
  parity_anticommutes_minus := by
    dsimp [algebraicAnticommutator, InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.Qdag]
    rw [Fin.sum_univ_one]
    have h := InfoGeometry.OperatorAlgebra.CARFermionParity.parityFactor_anticomm_cre 1 0
    have comm1 : (1 - algebraMap ℝ (Clnn 1) 2 * (cre 1 0 * ann 1 0)) * InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.s 1 w = InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.s 1 w * (1 - algebraMap ℝ (Clnn 1) 2 * (cre 1 0 * ann 1 0)) := by
      dsimp [InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.s]
      exact (Algebra.commutes w _).symm
    rw [← mul_assoc (1 - _), comm1, mul_assoc (InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.s 1 w)]
    rw [mul_assoc (InfoGeometry.OperatorAlgebra.SuperchargeNilpotence.s 1 w)]
    have h_h : (1 - algebraMap ℝ (Clnn 1) 2 * (cre 1 0 * ann 1 0)) * cre 1 0 = -(cre 1 0 * (1 - algebraMap ℝ (Clnn 1) 2 * (cre 1 0 * ann 1 0))) := h
    rw [h_h, mul_neg, neg_add_cancel]

end InfoGeometry.Canonical
