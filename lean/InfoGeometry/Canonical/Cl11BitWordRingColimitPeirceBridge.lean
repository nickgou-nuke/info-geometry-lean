import InfoGeometry.Canonical.Cl11TwoSheetPeirceCorners
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11HestenesKreinBitWordBridge

/-!
# Peirce corners through the coherent Clifford/BitWord ring colimit

This owner reuses the existing `CliffordBitWordEquivalence` and the existing
Primon/UHF colimit.  It transports the finite two-sheet Peirce blocks and the
sheet-exchange identity to that colimit carrier.  No new colimit carrier and
no Fock/Cuntz identification are introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11BitWordRingColimitPeirceBridge

open InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
open InfoGeometry.Canonical.Cl11HestenesKreinBitWordBridge
open InfoGeometry.Canonical.Cl11TwoSheetPeirceCorners
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Algebra.PrimonColimitAlgebra

abbrev UHFStage (n : ℕ) :=
  InfoGeometry.Canonical.Cl11HestenesKreinBitWordBridge.UHFStage n

abbrev ClStage (n : ℕ) :=
  InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge.Stage n

abbrev UHFCarrier := PrimonUHFAlgebra

def bitWordPeircePlusMinus (n : ℕ) (a : UHFStage n) : UHFStage n :=
  bitWordFPlus n * a * bitWordFMinus n

def bitWordPeirceMinusPlus (n : ℕ) (a : UHFStage n) : UHFStage n :=
  bitWordFMinus n * a * bitWordFPlus n

def bitWordPeircePlusPlus (n : ℕ) (a : UHFStage n) : UHFStage n :=
  bitWordFPlus n * a * bitWordFPlus n

def bitWordPeirceMinusMinus (n : ℕ) (a : UHFStage n) : UHFStage n :=
  bitWordFMinus n * a * bitWordFMinus n

theorem colimit_equiv_eta_stage (n : ℕ) :
    cliffordBitWordColimitEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1) (etaElem n)) =
      toColimit (n + 1) (bitWordEta n) := by
  exact cliffordBitWordColimitEquiv_ofStage (n + 1) (etaElem n)

theorem colimit_equiv_fPlus_stage (n : ℕ) :
    cliffordBitWordColimitEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1) (fPlusElem n)) =
      toColimit (n + 1) (bitWordFPlus n) := by
  exact cliffordBitWordColimitEquiv_ofStage (n + 1) (fPlusElem n)

theorem colimit_equiv_fMinus_stage (n : ℕ) :
    cliffordBitWordColimitEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1) (fMinusElem n)) =
      toColimit (n + 1) (bitWordFMinus n) := by
  exact cliffordBitWordColimitEquiv_ofStage (n + 1) (fMinusElem n)

theorem colimit_equiv_plusMinus_stage (n : ℕ) (a : ClStage n) :
    cliffordBitWordColimitEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1) (plusMinus n a)) =
      toColimit (n + 1)
        (bitWordPeircePlusMinus n (clStageEquiv (n + 1) a)) := by
  rw [cliffordBitWordColimitEquiv_ofStage]
  simp [bitWordPeircePlusMinus, plusMinus, bitWordFPlus, bitWordFMinus,
    map_mul]

theorem colimit_equiv_minusPlus_stage (n : ℕ) (a : ClStage n) :
    cliffordBitWordColimitEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1) (minusPlus n a)) =
      toColimit (n + 1)
        (bitWordPeirceMinusPlus n (clStageEquiv (n + 1) a)) := by
  rw [cliffordBitWordColimitEquiv_ofStage]
  simp [bitWordPeirceMinusPlus, minusPlus, bitWordFPlus, bitWordFMinus,
    map_mul]

theorem colimit_equiv_plusPlus_stage (n : ℕ) (a : ClStage n) :
    cliffordBitWordColimitEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1) (plusPlus n a)) =
      toColimit (n + 1)
        (bitWordPeircePlusPlus n (clStageEquiv (n + 1) a)) := by
  rw [cliffordBitWordColimitEquiv_ofStage]
  simp [bitWordPeircePlusPlus, plusPlus, bitWordFPlus,
    map_mul]

theorem colimit_equiv_minusMinus_stage (n : ℕ) (a : ClStage n) :
    cliffordBitWordColimitEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1) (minusMinus n a)) =
      toColimit (n + 1)
        (bitWordPeirceMinusMinus n (clStageEquiv (n + 1) a)) := by
  rw [cliffordBitWordColimitEquiv_ofStage]
  simp [bitWordPeirceMinusMinus, minusMinus, bitWordFMinus,
    map_mul]

theorem bitWord_eta_conjugates_plusMinus
    (n : ℕ) (a : UHFStage n) :
    bitWordEta n * bitWordPeircePlusMinus n a * bitWordEta n =
      bitWordPeirceMinusPlus n
        (bitWordEta n * a * bitWordEta n) := by
  unfold bitWordPeircePlusMinus bitWordPeirceMinusPlus
  have hη : bitWordEta n * bitWordEta n = 1 := bitWordEta_idempotent n
  have hp := bitWordEta_exchanges_sheets n
  have hm : bitWordEta n * bitWordFMinus n * bitWordEta n =
      bitWordFPlus n := by
    calc
      bitWordEta n * bitWordFMinus n * bitWordEta n =
          bitWordEta n * (bitWordEta n * bitWordFPlus n * bitWordEta n) *
            bitWordEta n := by rw [hp]
      _ = (bitWordEta n * bitWordEta n) * bitWordFPlus n *
          (bitWordEta n * bitWordEta n) := by noncomm_ring
      _ = bitWordFPlus n := by simp [hη]
  calc
    bitWordEta n * (bitWordFPlus n * a * bitWordFMinus n) * bitWordEta n =
        bitWordEta n * bitWordFPlus n * (bitWordEta n * bitWordEta n) *
          a * (bitWordEta n * bitWordEta n) * bitWordFMinus n * bitWordEta n := by
      simp only [hη]
      noncomm_ring
    _ = (bitWordEta n * bitWordFPlus n * bitWordEta n) *
        (bitWordEta n * a * bitWordEta n) *
        (bitWordEta n * bitWordFMinus n * bitWordEta n) := by
      noncomm_ring
    _ = bitWordFMinus n * (bitWordEta n * a * bitWordEta n) *
        bitWordFPlus n := by
      simp only [hp, hm]

theorem colimit_eta_conjugates_plusMinus_stage
    (n : ℕ) (a : UHFStage n) :
    toColimit (n + 1) (bitWordEta n) *
        toColimit (n + 1) (bitWordPeircePlusMinus n a) *
        toColimit (n + 1) (bitWordEta n) =
      toColimit (n + 1)
        (bitWordPeirceMinusPlus n
          (bitWordEta n * a * bitWordEta n)) := by
  rw [← map_mul, ← map_mul, bitWord_eta_conjugates_plusMinus]

theorem bitWordPeircePlusMinus_bond (n : ℕ) (a : UHFStage n) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
        (bitWordPeircePlusMinus n a) =
      bitWordPeircePlusMinus (n + 1)
        (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a) := by
  unfold bitWordPeircePlusMinus
  rw [map_mul, map_mul, bitWordFPlus_bond, bitWordFMinus_bond]

theorem bitWordPeirceMinusPlus_bond (n : ℕ) (a : UHFStage n) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
        (bitWordPeirceMinusPlus n a) =
      bitWordPeirceMinusPlus (n + 1)
        (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a) := by
  unfold bitWordPeirceMinusPlus
  rw [map_mul, map_mul, bitWordFMinus_bond, bitWordFPlus_bond]

theorem bitWordPeircePlusPlus_bond (n : ℕ) (a : UHFStage n) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
        (bitWordPeircePlusPlus n a) =
      bitWordPeircePlusPlus (n + 1)
        (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a) := by
  unfold bitWordPeircePlusPlus
  simp only [map_mul, bitWordFPlus_bond]

theorem bitWordPeirceMinusMinus_bond (n : ℕ) (a : UHFStage n) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
        (bitWordPeirceMinusMinus n a) =
      bitWordPeirceMinusMinus (n + 1)
        (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a) := by
  unfold bitWordPeirceMinusMinus
  simp only [map_mul, bitWordFMinus_bond]

theorem peircePlusMinus_toColimit_bond (n : ℕ) (a : UHFStage n) :
    toColimit (n + 2)
        (bitWordPeircePlusMinus (n + 1)
          (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a)) =
      toColimit (n + 1) (bitWordPeircePlusMinus n a) := by
  rw [← bitWordPeircePlusMinus_bond n a]
  exact toColimit_bond (n + 1) (bitWordPeircePlusMinus n a)

theorem peirceMinusPlus_toColimit_bond (n : ℕ) (a : UHFStage n) :
    toColimit (n + 2)
        (bitWordPeirceMinusPlus (n + 1)
          (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a)) =
      toColimit (n + 1) (bitWordPeirceMinusPlus n a) := by
  rw [← bitWordPeirceMinusPlus_bond n a]
  exact toColimit_bond (n + 1) (bitWordPeirceMinusPlus n a)

theorem peircePlusPlus_toColimit_bond (n : ℕ) (a : UHFStage n) :
    toColimit (n + 2)
        (bitWordPeircePlusPlus (n + 1)
          (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a)) =
      toColimit (n + 1) (bitWordPeircePlusPlus n a) := by
  rw [← bitWordPeircePlusPlus_bond n a]
  exact toColimit_bond (n + 1) (bitWordPeircePlusPlus n a)

theorem peirceMinusMinus_toColimit_bond (n : ℕ) (a : UHFStage n) :
    toColimit (n + 2)
        (bitWordPeirceMinusMinus (n + 1)
          (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a)) =
      toColimit (n + 1) (bitWordPeirceMinusMinus n a) := by
  rw [← bitWordPeirceMinusMinus_bond n a]
  exact toColimit_bond (n + 1) (bitWordPeirceMinusMinus n a)

theorem peirce_toColimit_bond_packet (n : ℕ) (a : UHFStage n) :
    toColimit (n + 2)
        (bitWordPeircePlusMinus (n + 1)
          (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a)) =
      toColimit (n + 1) (bitWordPeircePlusMinus n a) ∧
    toColimit (n + 2)
        (bitWordPeirceMinusPlus (n + 1)
          (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a)) =
      toColimit (n + 1) (bitWordPeirceMinusPlus n a) ∧
    toColimit (n + 2)
        (bitWordPeircePlusPlus (n + 1)
          (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a)) =
      toColimit (n + 1) (bitWordPeircePlusPlus n a) ∧
    toColimit (n + 2)
        (bitWordPeirceMinusMinus (n + 1)
          (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) a)) =
      toColimit (n + 1) (bitWordPeirceMinusMinus n a) :=
  ⟨peircePlusMinus_toColimit_bond n a,
    peirceMinusPlus_toColimit_bond n a,
    peircePlusPlus_toColimit_bond n a,
    peirceMinusMinus_toColimit_bond n a⟩

end InfoGeometry.Canonical.Cl11BitWordRingColimitPeirceBridge
