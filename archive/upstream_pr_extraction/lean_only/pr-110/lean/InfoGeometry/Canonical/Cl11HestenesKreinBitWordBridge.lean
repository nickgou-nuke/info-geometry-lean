import InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
import InfoGeometry.Clifford.CliffordBitWordEquivalence

/-!
# Hestenes/Krein data on the coherent BitWord/UHF presentation

The finite Clifford stages and the BitWord/UHF stages are related by the
existing coherent algebra equivalences.  This file transports the already
proved two-sheet identities across those equivalences; it does not introduce
a second tower or assert a universal Fock/Cuntz identification.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11HestenesKreinBitWordBridge

open InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Algebra.PrimonColimitAlgebra

abbrev UHFStage (n : ℕ) :=
  InfoGeometry.Algebra.CliffordBitWordEquivalence.UHFStage (n + 1)

def bitWordEta (n : ℕ) : UHFStage n := clStageEquiv (n + 1) (etaElem n)

def bitWordFPlus (n : ℕ) : UHFStage n := clStageEquiv (n + 1) (fPlusElem n)

def bitWordFMinus (n : ℕ) : UHFStage n := clStageEquiv (n + 1) (fMinusElem n)

theorem bitWordEta_idempotent (n : ℕ) :
    bitWordEta n * bitWordEta n = 1 := by
  change clStageEquiv (n + 1) (etaElem n) * clStageEquiv (n + 1) (etaElem n) = 1
  rw [← map_mul, etaElem_sq, map_one]

theorem bitWordFPlus_idempotent (n : ℕ) :
    bitWordFPlus n * bitWordFPlus n = bitWordFPlus n := by
  change clStageEquiv (n + 1) (fPlusElem n) * clStageEquiv (n + 1) (fPlusElem n) =
    clStageEquiv (n + 1) (fPlusElem n)
  rw [← map_mul, fPlusElem_idempotent]

theorem bitWordFMinus_idempotent (n : ℕ) :
    bitWordFMinus n * bitWordFMinus n = bitWordFMinus n := by
  change clStageEquiv (n + 1) (fMinusElem n) * clStageEquiv (n + 1) (fMinusElem n) =
    clStageEquiv (n + 1) (fMinusElem n)
  rw [← map_mul, fMinusElem_idempotent]

theorem bitWordFPlus_FMinus_zero (n : ℕ) :
    bitWordFPlus n * bitWordFMinus n = 0 := by
  change clStageEquiv (n + 1) (fPlusElem n) * clStageEquiv (n + 1) (fMinusElem n) = 0
  rw [← map_mul, fPlusElem_fMinusElem_zero, map_zero]

theorem bitWordFMinus_FPlus_zero (n : ℕ) :
    bitWordFMinus n * bitWordFPlus n = 0 := by
  change clStageEquiv (n + 1) (fMinusElem n) * clStageEquiv (n + 1) (fPlusElem n) = 0
  rw [← map_mul, fMinusElem_fPlusElem_zero, map_zero]

theorem bitWordEta_exchanges_sheets (n : ℕ) :
    bitWordEta n * bitWordFPlus n * bitWordEta n = bitWordFMinus n := by
  change clStageEquiv (n + 1) (etaElem n) * clStageEquiv (n + 1) (fPlusElem n) *
      clStageEquiv (n + 1) (etaElem n) = clStageEquiv (n + 1) (fMinusElem n)
  rw [← map_mul, ← map_mul, etaElem_fPlusElem_etaElem]

theorem bitWordEta_exchanges_fMinus (n : ℕ) :
    bitWordEta n * bitWordFMinus n * bitWordEta n = bitWordFPlus n := by
  have hη := bitWordEta_idempotent n
  have hp := bitWordEta_exchanges_sheets n
  calc
    bitWordEta n * bitWordFMinus n * bitWordEta n =
        bitWordEta n * (bitWordEta n * bitWordFPlus n * bitWordEta n) *
          bitWordEta n := by rw [hp]
    _ = (bitWordEta n * bitWordEta n) * bitWordFPlus n *
          (bitWordEta n * bitWordEta n) := by
      simp only [mul_assoc]
    _ = bitWordFPlus n := by
      simp only [hη, one_mul, mul_one]

theorem bitWordEta_bond (n : ℕ) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1) (bitWordEta n) =
      bitWordEta (n + 1) := by
  change InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
      (clStageEquiv (n + 1) (etaElem n)) =
    clStageEquiv (n + 2) (etaElem (n + 1))
  rw [← clStageEquiv_bond (n + 1) (etaElem n)]
  change clStageEquiv (n + 2)
      (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1) (etaElem n)) = _
  have hmap :
      InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1) (etaElem n) =
        etaElem (n + 1) := by
    simpa [etaElem, Function.comp_apply] using
      congrArg (fun φ => φ etaBase)
        (stageMapAlg_succ 0 n (Nat.zero_le n))
  exact congrArg (clStageEquiv (n + 2)) hmap

theorem bitWordFPlus_bond (n : ℕ) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
        (bitWordFPlus n) = bitWordFPlus (n + 1) := by
  change InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
      (clStageEquiv (n + 1) (fPlusElem n)) =
    clStageEquiv (n + 2) (fPlusElem (n + 1))
  rw [← clStageEquiv_bond (n + 1) (fPlusElem n)]
  change clStageEquiv (n + 2)
      (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1) (fPlusElem n)) = _
  have hmap :
      InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1) (fPlusElem n) =
        fPlusElem (n + 1) := by
    simpa [fPlusElem, Function.comp_apply] using
      congrArg (fun φ => φ fPlusBase)
        (stageMapAlg_succ 0 n (Nat.zero_le n))
  exact congrArg (clStageEquiv (n + 2)) hmap

theorem bitWordFMinus_bond (n : ℕ) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
        (bitWordFMinus n) = bitWordFMinus (n + 1) := by
  change InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
      (clStageEquiv (n + 1) (fMinusElem n)) =
    clStageEquiv (n + 2) (fMinusElem (n + 1))
  rw [← clStageEquiv_bond (n + 1) (fMinusElem n)]
  change clStageEquiv (n + 2)
      (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1) (fMinusElem n)) = _
  have hmap :
      InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1) (fMinusElem n) =
        fMinusElem (n + 1) := by
    simpa [fMinusElem, Function.comp_apply] using
      congrArg (fun φ => φ fMinusBase)
        (stageMapAlg_succ 0 n (Nat.zero_le n))
  exact congrArg (clStageEquiv (n + 2)) hmap

/-! The three transported sheet elements form one reusable bonding packet.
This is a concrete conjunction of the already-proved equations; it does not
stand in for a categorical natural-transformation structure. -/
theorem bitWord_sheet_bond_packet (n : ℕ) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
        (bitWordEta n) = bitWordEta (n + 1) ∧
      InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
        (bitWordFPlus n) = bitWordFPlus (n + 1) ∧
      InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond (n + 1)
        (bitWordFMinus n) = bitWordFMinus (n + 1) := by
  exact ⟨bitWordEta_bond n, bitWordFPlus_bond n, bitWordFMinus_bond n⟩

end InfoGeometry.Canonical.Cl11HestenesKreinBitWordBridge
