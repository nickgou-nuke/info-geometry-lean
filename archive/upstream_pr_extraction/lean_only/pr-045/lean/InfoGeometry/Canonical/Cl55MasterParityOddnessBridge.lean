import Mathlib
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
import InfoGeometry.Canonical.Cl11TensorTowerGlobalParity

/-!
# Native parity readout for the Cl(5,5) master envelope

The master CAR carrier already has the recursive Jordan--Wigner parity
`globalChirality 5`.  This owner only packages its consequences for the
operators exposed by `Cl55MasterWittSpinorEnvelopeBridge`; it introduces no
parallel chirality or Hodge--Dirac operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55MasterParityOddnessBridge

open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Canonical.Cl11TensorTowerGlobalParity

abbrev MasterChirality : Mat32 := globalChirality 5

theorem masterChirality_sq :
    MasterChirality * MasterChirality = 1 := by
  exact globalChirality_sq 5

theorem masterChirality_transpose :
    Matrix.transpose MasterChirality = MasterChirality := by
  exact globalChirality_transpose 5

theorem masterChirality_anticomm_hodge :
    MasterChirality * embeddedSplitOctonionHodgeDirac +
      embeddedSplitOctonionHodgeDirac * MasterChirality = 0 := by
  dsimp [MasterChirality, embeddedSplitOctonionHodgeDirac,
    masterCreation, masterAnnihilation]
  calc
    globalChirality 5 *
          (creation 0 + annihilation 0 + creation 1 + annihilation 1 +
            creation 2 + annihilation 2) +
        (creation 0 + annihilation 0 + creation 1 + annihilation 1 +
            creation 2 + annihilation 2) * globalChirality 5 =
      (globalChirality 5 * creation 0 + creation 0 * globalChirality 5) +
      (globalChirality 5 * annihilation 0 + annihilation 0 * globalChirality 5) +
      (globalChirality 5 * creation 1 + creation 1 * globalChirality 5) +
      (globalChirality 5 * annihilation 1 + annihilation 1 * globalChirality 5) +
      (globalChirality 5 * creation 2 + creation 2 * globalChirality 5) +
      (globalChirality 5 * annihilation 2 + annihilation 2 * globalChirality 5) := by
        simp only [Matrix.mul_add, Matrix.add_mul]
        abel
    _ = 0 := by
      rw [globalChirality_anticomm_jwCreation 5 0,
        globalChirality_anticomm_jwAnnihilation 5 0,
        globalChirality_anticomm_jwCreation 5 1,
        globalChirality_anticomm_jwAnnihilation 5 1,
        globalChirality_anticomm_jwCreation 5 2,
        globalChirality_anticomm_jwAnnihilation 5 2]
      simp

theorem masterChirality_anticomm_supercharge :
    MasterChirality * chiralSuperchargeQ +
      chiralSuperchargeQ * MasterChirality = 0 ∧
    MasterChirality * chiralSuperchargeQBar +
      chiralSuperchargeQBar * MasterChirality = 0 := by
  constructor
  · dsimp [MasterChirality, chiralSuperchargeQ, masterCreation]
    calc
      globalChirality 5 * (creation 3 + creation 4) +
          (creation 3 + creation 4) * globalChirality 5 =
        (globalChirality 5 * creation 3 + creation 3 * globalChirality 5) +
        (globalChirality 5 * creation 4 + creation 4 * globalChirality 5) := by
          simp only [Matrix.mul_add, Matrix.add_mul]
          abel
      _ = 0 := by
        rw [globalChirality_anticomm_jwCreation 5 3,
          globalChirality_anticomm_jwCreation 5 4]
        simp
  · dsimp [MasterChirality, chiralSuperchargeQBar, masterAnnihilation]
    calc
      globalChirality 5 * (annihilation 3 + annihilation 4) +
          (annihilation 3 + annihilation 4) * globalChirality 5 =
        (globalChirality 5 * annihilation 3 + annihilation 3 * globalChirality 5) +
        (globalChirality 5 * annihilation 4 + annihilation 4 * globalChirality 5) := by
          simp only [Matrix.mul_add, Matrix.add_mul]
          abel
      _ = 0 := by
        rw [globalChirality_anticomm_jwAnnihilation 5 3,
          globalChirality_anticomm_jwAnnihilation 5 4]
        simp

theorem masterChirality_commutes_inducedEvenMomentum :
    MasterChirality * inducedEvenMomentum =
      inducedEvenMomentum * MasterChirality := by
  have hQ0 := masterChirality_anticomm_supercharge.1
  have hQBar0 := masterChirality_anticomm_supercharge.2
  have even_of_anticommute {R : Type} [Ring R] (g q r : R)
      (hq : g * q + q * g = 0) (hr : g * r + r * g = 0) :
      g * (q * r + r * q) = (q * r + r * q) * g := by
    have hq' : g * q = -(q * g) := eq_neg_of_add_eq_zero_left hq
    have hr' : g * r = -(r * g) := eq_neg_of_add_eq_zero_left hr
    calc
      g * (q * r + r * q) = (g * q) * r + (g * r) * q := by
        simp only [mul_add, mul_assoc]
      _ = (-(q * g)) * r + (-(r * g)) * q := by rw [hq', hr']
      _ = q * (r * g) + r * (q * g) := by
        rw [neg_mul, neg_mul]
        simp [hr', hq', mul_assoc]
      _ = (q * r + r * q) * g := by
        rw [add_mul]
        simp only [mul_assoc]
  have hinner :
      MasterChirality *
          (chiralSuperchargeQ * chiralSuperchargeQBar +
            chiralSuperchargeQBar * chiralSuperchargeQ) =
        (chiralSuperchargeQ * chiralSuperchargeQBar +
          chiralSuperchargeQBar * chiralSuperchargeQ) * MasterChirality := by
    exact even_of_anticommute MasterChirality chiralSuperchargeQ
      chiralSuperchargeQBar hQ0 hQBar0
  change MasterChirality *
        ((1 / 2 : ℝ) •
          (chiralSuperchargeQ * chiralSuperchargeQBar +
            chiralSuperchargeQBar * chiralSuperchargeQ)) =
      ((1 / 2 : ℝ) •
        (chiralSuperchargeQ * chiralSuperchargeQBar +
          chiralSuperchargeQBar * chiralSuperchargeQ)) * MasterChirality
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact congrArg (fun A : Mat32 => (1 / 2 : ℝ) • A) hinner

end InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
