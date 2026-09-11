import InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.IdempotentTwoSidedSpan
import InfoGeometry.Krein.TwoSheetKreinIdealBridge

/-!
# Four Peirce corners on the native Cl(1,1) stages

This owner records the concrete four-corner decomposition determined by the
two transported sheet projectors.  It deliberately proves only additive and
corner-membership facts; no scalar-corner, Morita, or metric identification is
asserted here.
-/

namespace InfoGeometry.Canonical.Cl11TwoSheetPeirceCorners

noncomputable section

open InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Algebra.IdempotentTwoSidedSpan
open InfoGeometry.Krein

def plusPlus (n : ℕ) (a : Stage n) : Stage n :=
  fPlusElem n * a * fPlusElem n

def plusMinus (n : ℕ) (a : Stage n) : Stage n :=
  fPlusElem n * a * fMinusElem n

def minusPlus (n : ℕ) (a : Stage n) : Stage n :=
  fMinusElem n * a * fPlusElem n

def minusMinus (n : ℕ) (a : Stage n) : Stage n :=
  fMinusElem n * a * fMinusElem n

theorem plusMinus_mem_twoSidedSpan (n : ℕ) (a : Stage n) :
    plusMinus n a ∈ twoSidedSpan (fMinusElem n) := by
  simpa [plusMinus, mul_assoc] using
    generator_mem_twoSidedSpan (fMinusElem n) (fPlusElem n * a) 1

theorem minusPlus_mem_twoSidedSpan (n : ℕ) (a : Stage n) :
    minusPlus n a ∈ twoSidedSpan (fPlusElem n) := by
  simpa [minusPlus, mul_assoc] using
    generator_mem_twoSidedSpan (fPlusElem n) (fMinusElem n * a) 1

theorem etaElem_plusMinus_etaElem (n : ℕ) (a : Stage n) :
    etaElem n * plusMinus n a * etaElem n =
      minusPlus n (etaElem n * a * etaElem n) := by
  have hη := etaElem_sq n
  have hplus := etaElem_fPlusElem_etaElem n
  have hminus := etaElem_fMinusElem_etaElem n
  have hconj3 (x y z : Stage n) :
      etaElem n * (x * y * z) * etaElem n =
        (etaElem n * x * etaElem n) *
          (etaElem n * y * etaElem n) *
          (etaElem n * z * etaElem n) := by
    symm
    calc
      (etaElem n * x * etaElem n) *
          (etaElem n * y * etaElem n) *
          (etaElem n * z * etaElem n) =
          etaElem n * x * (etaElem n * etaElem n) * y *
            (etaElem n * etaElem n) * z * etaElem n := by
              simp only [mul_assoc]
      _ = etaElem n * (x * y * z) * etaElem n := by
        rw [hη]
        simp only [one_mul, mul_one, mul_assoc]
  unfold plusMinus minusPlus
  calc
    etaElem n * (fPlusElem n * a * fMinusElem n) * etaElem n =
        (etaElem n * fPlusElem n * etaElem n) *
          (etaElem n * a * etaElem n) *
          (etaElem n * fMinusElem n * etaElem n) := by
            exact hconj3 (fPlusElem n) a (fMinusElem n)
    _ = fMinusElem n * (etaElem n * a * etaElem n) * fPlusElem n := by
      rw [hplus, hminus]

theorem etaElem_minusPlus_etaElem (n : ℕ) (a : Stage n) :
    etaElem n * minusPlus n a * etaElem n =
      plusMinus n (etaElem n * a * etaElem n) := by
  have hη := etaElem_sq n
  have hplus := etaElem_fPlusElem_etaElem n
  have hminus := etaElem_fMinusElem_etaElem n
  have hconj3 (x y z : Stage n) :
      etaElem n * (x * y * z) * etaElem n =
        (etaElem n * x * etaElem n) *
          (etaElem n * y * etaElem n) *
          (etaElem n * z * etaElem n) := by
    symm
    calc
      (etaElem n * x * etaElem n) *
          (etaElem n * y * etaElem n) *
          (etaElem n * z * etaElem n) =
          etaElem n * x * (etaElem n * etaElem n) * y *
            (etaElem n * etaElem n) * z * etaElem n := by
              simp only [mul_assoc]
      _ = etaElem n * (x * y * z) * etaElem n := by
        rw [hη]
        simp only [one_mul, mul_one, mul_assoc]
  unfold minusPlus plusMinus
  calc
    etaElem n * (fMinusElem n * a * fPlusElem n) * etaElem n =
        (etaElem n * fMinusElem n * etaElem n) *
          (etaElem n * a * etaElem n) *
          (etaElem n * fPlusElem n * etaElem n) := by
            exact hconj3 (fMinusElem n) a (fPlusElem n)
    _ = fPlusElem n * (etaElem n * a * etaElem n) * fMinusElem n := by
      rw [hminus, hplus]

theorem etaElem_plusPlus_etaElem (n : ℕ) (a : Stage n) :
    etaElem n * plusPlus n a * etaElem n =
      minusMinus n (etaElem n * a * etaElem n) := by
  have hη := etaElem_sq n
  have hplus := etaElem_fPlusElem_etaElem n
  have hminus := etaElem_fMinusElem_etaElem n
  have hconj3 (x y z : Stage n) :
      etaElem n * (x * y * z) * etaElem n =
        (etaElem n * x * etaElem n) *
          (etaElem n * y * etaElem n) *
          (etaElem n * z * etaElem n) := by
    symm
    calc
      (etaElem n * x * etaElem n) *
          (etaElem n * y * etaElem n) *
          (etaElem n * z * etaElem n) =
          etaElem n * x * (etaElem n * etaElem n) * y *
            (etaElem n * etaElem n) * z * etaElem n := by
              simp only [mul_assoc]
      _ = etaElem n * (x * y * z) * etaElem n := by
        rw [hη]
        simp only [one_mul, mul_one, mul_assoc]
  unfold plusPlus minusMinus
  calc
    etaElem n * (fPlusElem n * a * fPlusElem n) * etaElem n =
        (etaElem n * fPlusElem n * etaElem n) *
          (etaElem n * a * etaElem n) *
          (etaElem n * fPlusElem n * etaElem n) := by
            exact hconj3 (fPlusElem n) a (fPlusElem n)
    _ = fMinusElem n * (etaElem n * a * etaElem n) * fMinusElem n := by
      rw [hplus]

theorem etaElem_minusMinus_etaElem (n : ℕ) (a : Stage n) :
    etaElem n * minusMinus n a * etaElem n =
      plusPlus n (etaElem n * a * etaElem n) := by
  have hη := etaElem_sq n
  have hminus := etaElem_fMinusElem_etaElem n
  have hconj3 (x y z : Stage n) :
      etaElem n * (x * y * z) * etaElem n =
        (etaElem n * x * etaElem n) *
          (etaElem n * y * etaElem n) *
          (etaElem n * z * etaElem n) := by
    symm
    calc
      (etaElem n * x * etaElem n) *
          (etaElem n * y * etaElem n) *
          (etaElem n * z * etaElem n) =
          etaElem n * x * (etaElem n * etaElem n) * y *
            (etaElem n * etaElem n) * z * etaElem n := by
              simp only [mul_assoc]
      _ = etaElem n * (x * y * z) * etaElem n := by
        rw [hη]
        simp only [one_mul, mul_one, mul_assoc]
  unfold minusMinus plusPlus
  calc
    etaElem n * (fMinusElem n * a * fMinusElem n) * etaElem n =
        (etaElem n * fMinusElem n * etaElem n) *
          (etaElem n * a * etaElem n) *
          (etaElem n * fMinusElem n * etaElem n) := by
            exact hconj3 (fMinusElem n) a (fMinusElem n)
    _ = fPlusElem n * (etaElem n * a * etaElem n) * fPlusElem n := by
      rw [hminus]

theorem stageEmbed_plusPlus (n : ℕ) (a : Stage n) :
    stageMapAlg n (n + 1) (Nat.le_succ n) (plusPlus n a) =
      plusPlus (n + 1) (stageMapAlg n (n + 1) (Nat.le_succ n) a) := by
  unfold plusPlus
  rw [map_mul, map_mul, stageMap_fPlusElem]

theorem stageEmbed_plusMinus (n : ℕ) (a : Stage n) :
    stageMapAlg n (n + 1) (Nat.le_succ n) (plusMinus n a) =
      plusMinus (n + 1) (stageMapAlg n (n + 1) (Nat.le_succ n) a) := by
  unfold plusMinus
  rw [map_mul, map_mul, stageMap_fPlusElem, stageMap_fMinusElem]

theorem stageEmbed_minusPlus (n : ℕ) (a : Stage n) :
    stageMapAlg n (n + 1) (Nat.le_succ n) (minusPlus n a) =
      minusPlus (n + 1) (stageMapAlg n (n + 1) (Nat.le_succ n) a) := by
  unfold minusPlus
  rw [map_mul, map_mul, stageMap_fMinusElem, stageMap_fPlusElem]

theorem stageEmbed_minusMinus (n : ℕ) (a : Stage n) :
    stageMapAlg n (n + 1) (Nat.le_succ n) (minusMinus n a) =
      minusMinus (n + 1) (stageMapAlg n (n + 1) (Nat.le_succ n) a) := by
  unfold minusMinus
  rw [map_mul, map_mul, stageMap_fMinusElem]

theorem plusMinus_mul_minusPlus (n : ℕ) (a b : Stage n) :
    plusMinus n a * minusPlus n b = plusPlus n (a * fMinusElem n * b) := by
  unfold plusMinus minusPlus plusPlus
  calc
    (fPlusElem n * a * fMinusElem n) *
        (fMinusElem n * b * fPlusElem n) =
        fPlusElem n * a * (fMinusElem n * fMinusElem n) *
          b * fPlusElem n := by noncomm_ring
    _ = fPlusElem n * (a * fMinusElem n * b) * fPlusElem n := by
      calc
        fPlusElem n * a * (fMinusElem n * fMinusElem n) *
            b * fPlusElem n =
            fPlusElem n * a * ((fMinusElem n * fMinusElem n) * b) *
              fPlusElem n := by simp [mul_assoc]
        _ = fPlusElem n * a * (fMinusElem n * b) * fPlusElem n := by
          rw [fMinusElem_idempotent]
        _ = fPlusElem n * (a * fMinusElem n * b) * fPlusElem n := by
          simp [mul_assoc]

theorem minusPlus_mul_plusMinus (n : ℕ) (a b : Stage n) :
    minusPlus n a * plusMinus n b = minusMinus n (a * fPlusElem n * b) := by
  unfold minusPlus plusMinus minusMinus
  calc
    (fMinusElem n * a * fPlusElem n) *
        (fPlusElem n * b * fMinusElem n) =
        fMinusElem n * a * (fPlusElem n * fPlusElem n) *
          b * fMinusElem n := by noncomm_ring
    _ = fMinusElem n * (a * fPlusElem n * b) * fMinusElem n := by
      calc
        fMinusElem n * a * (fPlusElem n * fPlusElem n) *
            b * fMinusElem n =
            fMinusElem n * a * ((fPlusElem n * fPlusElem n) * b) *
              fMinusElem n := by simp [mul_assoc]
        _ = fMinusElem n * a * (fPlusElem n * b) * fMinusElem n := by
          rw [fPlusElem_idempotent]
        _ = fMinusElem n * (a * fPlusElem n * b) * fMinusElem n := by
          simp [mul_assoc]

theorem plusPlus_mul_plusMinus (n : ℕ) (a b : Stage n) :
    plusPlus n a * plusMinus n b = plusMinus n (a * fPlusElem n * b) := by
  unfold plusPlus plusMinus
  calc
    (fPlusElem n * a * fPlusElem n) *
        (fPlusElem n * b * fMinusElem n) =
        fPlusElem n * a * (fPlusElem n * fPlusElem n) *
          b * fMinusElem n := by noncomm_ring
    _ = fPlusElem n * (a * fPlusElem n * b) * fMinusElem n := by
      calc
        fPlusElem n * a * (fPlusElem n * fPlusElem n) *
            b * fMinusElem n =
            fPlusElem n * a * ((fPlusElem n * fPlusElem n) * b) *
              fMinusElem n := by simp [mul_assoc]
        _ = fPlusElem n * a * (fPlusElem n * b) * fMinusElem n := by
          rw [fPlusElem_idempotent]
        _ = fPlusElem n * (a * fPlusElem n * b) * fMinusElem n := by
          simp [mul_assoc]

theorem plusMinus_mul_plusMinus_zero (n : ℕ) (a b : Stage n) :
    plusMinus n a * plusMinus n b = 0 := by
  have hzero : fMinusElem n * fPlusElem n = 0 := by
    have h :=
      HestenesKreinFiniteStageCompatibility.Datum.fMinus_fPlus_zero
        finiteStageDatum n
    have h' := congrArg
      (fun T : Module.End ℝ (Stage n) => T (1 : Stage n)) h
    simpa [fPlusNat, fMinusNat, leftMul, ModuleCat.comp_apply,
      Module.End.mul_apply] using h'
  unfold plusMinus
  calc
    (fPlusElem n * a * fMinusElem n) *
        (fPlusElem n * b * fMinusElem n) =
        fPlusElem n * a * (fMinusElem n * fPlusElem n) *
          b * fMinusElem n := by noncomm_ring
    _ = 0 := by
      rw [hzero]
      simp

theorem minusPlus_mul_minusPlus_zero (n : ℕ) (a b : Stage n) :
    minusPlus n a * minusPlus n b = 0 := by
  unfold minusPlus
  calc
    (fMinusElem n * a * fPlusElem n) *
        (fMinusElem n * b * fPlusElem n) =
        fMinusElem n * a * (fPlusElem n * fMinusElem n) *
          b * fPlusElem n := by noncomm_ring
    _ = 0 := by
      rw [fPlusElem_fMinusElem_zero]
      simp

theorem plusMinus_mul_minusMinus (n : ℕ) (a b : Stage n) :
    plusMinus n a * minusMinus n b = plusMinus n (a * fMinusElem n * b) := by
  unfold plusMinus minusMinus
  calc
    (fPlusElem n * a * fMinusElem n) *
        (fMinusElem n * b * fMinusElem n) =
        fPlusElem n * a * (fMinusElem n * fMinusElem n) *
          b * fMinusElem n := by noncomm_ring
    _ = fPlusElem n * (a * fMinusElem n * b) * fMinusElem n := by
      rw [fMinusElem_idempotent]
      simp [mul_assoc]

theorem minusPlus_mul_plusPlus (n : ℕ) (a b : Stage n) :
    minusPlus n a * plusPlus n b = minusPlus n (a * fPlusElem n * b) := by
  unfold minusPlus plusPlus
  calc
    (fMinusElem n * a * fPlusElem n) *
        (fPlusElem n * b * fPlusElem n) =
        fMinusElem n * a * (fPlusElem n * fPlusElem n) *
          b * fPlusElem n := by noncomm_ring
    _ = fMinusElem n * (a * fPlusElem n * b) * fPlusElem n := by
      rw [fPlusElem_idempotent]
      simp [mul_assoc]

theorem plusPlus_mul_minusPlus_zero (n : ℕ) (a b : Stage n) :
    plusPlus n a * minusPlus n b = 0 := by
  unfold plusPlus minusPlus
  calc
    (fPlusElem n * a * fPlusElem n) *
        (fMinusElem n * b * fPlusElem n) =
        fPlusElem n * a * (fPlusElem n * fMinusElem n) *
          b * fPlusElem n := by noncomm_ring
    _ = 0 := by rw [fPlusElem_fMinusElem_zero]; simp

theorem plusPlus_mul_minusMinus_zero (n : ℕ) (a b : Stage n) :
    plusPlus n a * minusMinus n b = 0 := by
  unfold plusPlus minusMinus
  calc
    (fPlusElem n * a * fPlusElem n) *
        (fMinusElem n * b * fMinusElem n) =
        fPlusElem n * a * (fPlusElem n * fMinusElem n) *
          b * fMinusElem n := by noncomm_ring
    _ = 0 := by rw [fPlusElem_fMinusElem_zero]; simp

theorem plusMinus_mul_plusPlus_zero (n : ℕ) (a b : Stage n) :
    plusMinus n a * plusPlus n b = 0 := by
  unfold plusMinus plusPlus
  calc
    (fPlusElem n * a * fMinusElem n) *
        (fPlusElem n * b * fPlusElem n) =
        fPlusElem n * a * (fMinusElem n * fPlusElem n) *
          b * fPlusElem n := by noncomm_ring
    _ = 0 := by rw [fMinusElem_fPlusElem_zero]; simp

theorem minusPlus_mul_minusMinus_zero (n : ℕ) (a b : Stage n) :
    minusPlus n a * minusMinus n b = 0 := by
  unfold minusPlus minusMinus
  calc
    (fMinusElem n * a * fPlusElem n) *
        (fMinusElem n * b * fMinusElem n) =
        fMinusElem n * a * (fPlusElem n * fMinusElem n) *
          b * fMinusElem n := by noncomm_ring
    _ = 0 := by rw [fPlusElem_fMinusElem_zero]; simp

theorem minusMinus_mul_plusPlus_zero (n : ℕ) (a b : Stage n) :
    minusMinus n a * plusPlus n b = 0 := by
  unfold minusMinus plusPlus
  calc
    (fMinusElem n * a * fMinusElem n) *
        (fPlusElem n * b * fPlusElem n) =
        fMinusElem n * a * (fMinusElem n * fPlusElem n) *
          b * fPlusElem n := by noncomm_ring
    _ = 0 := by rw [fMinusElem_fPlusElem_zero]; simp

theorem minusMinus_mul_plusMinus_zero (n : ℕ) (a b : Stage n) :
    minusMinus n a * plusMinus n b = 0 := by
  unfold minusMinus plusMinus
  calc
    (fMinusElem n * a * fMinusElem n) *
        (fPlusElem n * b * fMinusElem n) =
        fMinusElem n * a * (fMinusElem n * fPlusElem n) *
          b * fMinusElem n := by noncomm_ring
    _ = 0 := by rw [fMinusElem_fPlusElem_zero]; simp

theorem minusMinus_mul_minusPlus (n : ℕ) (a b : Stage n) :
    minusMinus n a * minusPlus n b = minusPlus n (a * fMinusElem n * b) := by
  unfold minusMinus minusPlus
  calc
    (fMinusElem n * a * fMinusElem n) *
        (fMinusElem n * b * fPlusElem n) =
        fMinusElem n * a * (fMinusElem n * fMinusElem n) *
          b * fPlusElem n := by noncomm_ring
    _ = fMinusElem n * (a * fMinusElem n * b) * fPlusElem n := by
      calc
        fMinusElem n * a * (fMinusElem n * fMinusElem n) *
            b * fPlusElem n =
            fMinusElem n * a * ((fMinusElem n * fMinusElem n) * b) *
              fPlusElem n := by simp [mul_assoc]
        _ = fMinusElem n * a * (fMinusElem n * b) * fPlusElem n := by
          rw [fMinusElem_idempotent]
        _ = fMinusElem n * (a * fMinusElem n * b) * fPlusElem n := by
          simp [mul_assoc]

theorem plusPlus_mul_plusPlus (n : ℕ) (a b : Stage n) :
    plusPlus n a * plusPlus n b = plusPlus n (a * fPlusElem n * b) := by
  unfold plusPlus
  calc
    (fPlusElem n * a * fPlusElem n) *
        (fPlusElem n * b * fPlusElem n) =
        fPlusElem n * a * (fPlusElem n * fPlusElem n) *
          b * fPlusElem n := by noncomm_ring
    _ = fPlusElem n * (a * fPlusElem n * b) * fPlusElem n := by
      calc
        fPlusElem n * a * (fPlusElem n * fPlusElem n) *
            b * fPlusElem n =
            fPlusElem n * a * ((fPlusElem n * fPlusElem n) * b) *
              fPlusElem n := by simp [mul_assoc]
        _ = fPlusElem n * a * (fPlusElem n * b) * fPlusElem n := by
          rw [fPlusElem_idempotent]
        _ = fPlusElem n * (a * fPlusElem n * b) * fPlusElem n := by
          simp [mul_assoc]

theorem minusMinus_mul_minusMinus (n : ℕ) (a b : Stage n) :
    minusMinus n a * minusMinus n b = minusMinus n (a * fMinusElem n * b) := by
  unfold minusMinus
  calc
    (fMinusElem n * a * fMinusElem n) *
        (fMinusElem n * b * fMinusElem n) =
        fMinusElem n * a * (fMinusElem n * fMinusElem n) *
          b * fMinusElem n := by noncomm_ring
    _ = fMinusElem n * (a * fMinusElem n * b) * fMinusElem n := by
      calc
        fMinusElem n * a * (fMinusElem n * fMinusElem n) *
            b * fMinusElem n =
            fMinusElem n * a * ((fMinusElem n * fMinusElem n) * b) *
              fMinusElem n := by simp [mul_assoc]
        _ = fMinusElem n * a * (fMinusElem n * b) * fMinusElem n := by
          rw [fMinusElem_idempotent]
        _ = fMinusElem n * (a * fMinusElem n * b) * fMinusElem n := by
          simp [mul_assoc]

theorem peirce_decomposition (n : ℕ) (a : Stage n) :
    a = plusPlus n a + plusMinus n a + minusPlus n a + minusMinus n a := by
  simpa [plusPlus, plusMinus, minusPlus, minusMinus] using
    finite_peirce_decomposition n a

theorem peirce_blocks_mem (n : ℕ) (a : Stage n) :
    plusPlus n a ∈ peirceCorner (fPlusElem n) (fPlusElem n) ∧
    plusMinus n a ∈ peirceCorner (fPlusElem n) (fMinusElem n) ∧
    minusPlus n a ∈ peirceCorner (fMinusElem n) (fPlusElem n) ∧
    minusMinus n a ∈ peirceCorner (fMinusElem n) (fMinusElem n) := by
  simpa [plusPlus, plusMinus, minusPlus, minusMinus] using
    peirce_block_mem (fPlusElem n) (fMinusElem n) a
      (fPlusElem_idempotent n) (fMinusElem_idempotent n)

theorem krein_conjugates_peirce_blocks (n : ℕ) (a : Stage n) :
    kreinConjugate (etaElem n) (plusPlus n a) =
        minusMinus n (kreinConjugate (etaElem n) a) ∧
    kreinConjugate (etaElem n) (plusMinus n a) =
        minusPlus n (kreinConjugate (etaElem n) a) ∧
    kreinConjugate (etaElem n) (minusPlus n a) =
        plusMinus n (kreinConjugate (etaElem n) a) ∧
    kreinConjugate (etaElem n) (minusMinus n a) =
        plusPlus n (kreinConjugate (etaElem n) a) := by
  constructor
  · change kreinConjugate (etaElem n)
      ((fPlusElem n * a) * fPlusElem n) =
        fMinusElem n * kreinConjugate (etaElem n) a * fMinusElem n
    calc
      kreinConjugate (etaElem n) ((fPlusElem n * a) * fPlusElem n) =
          kreinConjugate (etaElem n) (fPlusElem n * a) *
            kreinConjugate (etaElem n) (fPlusElem n) :=
        kreinConjugate_mul (etaElem n) (etaElem_sq n)
          (fPlusElem n * a) (fPlusElem n)
      _ = (kreinConjugate (etaElem n) (fPlusElem n) *
            kreinConjugate (etaElem n) a) *
            kreinConjugate (etaElem n) (fPlusElem n) := by
        rw [kreinConjugate_mul (etaElem n) (etaElem_sq n)
          (fPlusElem n) a]
      _ = fMinusElem n * kreinConjugate (etaElem n) a * fMinusElem n := by
        simp [kreinConjugate, etaElem_fPlusElem_etaElem]
  constructor
  · change kreinConjugate (etaElem n)
      ((fPlusElem n * a) * fMinusElem n) =
        fMinusElem n * kreinConjugate (etaElem n) a * fPlusElem n
    calc
      kreinConjugate (etaElem n) ((fPlusElem n * a) * fMinusElem n) =
          kreinConjugate (etaElem n) (fPlusElem n * a) *
            kreinConjugate (etaElem n) (fMinusElem n) :=
        kreinConjugate_mul (etaElem n) (etaElem_sq n)
          (fPlusElem n * a) (fMinusElem n)
      _ = (kreinConjugate (etaElem n) (fPlusElem n) *
            kreinConjugate (etaElem n) a) *
            kreinConjugate (etaElem n) (fMinusElem n) := by
        rw [kreinConjugate_mul (etaElem n) (etaElem_sq n)
          (fPlusElem n) a]
      _ = fMinusElem n * kreinConjugate (etaElem n) a * fPlusElem n := by
        simp [kreinConjugate, etaElem_fPlusElem_etaElem,
          etaElem_fMinusElem_etaElem]
  constructor
  · change kreinConjugate (etaElem n)
      ((fMinusElem n * a) * fPlusElem n) =
        fPlusElem n * kreinConjugate (etaElem n) a * fMinusElem n
    calc
      kreinConjugate (etaElem n) ((fMinusElem n * a) * fPlusElem n) =
          kreinConjugate (etaElem n) (fMinusElem n * a) *
            kreinConjugate (etaElem n) (fPlusElem n) :=
        kreinConjugate_mul (etaElem n) (etaElem_sq n)
          (fMinusElem n * a) (fPlusElem n)
      _ = (kreinConjugate (etaElem n) (fMinusElem n) *
            kreinConjugate (etaElem n) a) *
            kreinConjugate (etaElem n) (fPlusElem n) := by
        rw [kreinConjugate_mul (etaElem n) (etaElem_sq n)
          (fMinusElem n) a]
      _ = fPlusElem n * kreinConjugate (etaElem n) a * fMinusElem n := by
        simp [kreinConjugate, etaElem_fPlusElem_etaElem,
          etaElem_fMinusElem_etaElem]
  · change kreinConjugate (etaElem n)
      ((fMinusElem n * a) * fMinusElem n) =
        fPlusElem n * kreinConjugate (etaElem n) a * fPlusElem n
    calc
      kreinConjugate (etaElem n) ((fMinusElem n * a) * fMinusElem n) =
          kreinConjugate (etaElem n) (fMinusElem n * a) *
            kreinConjugate (etaElem n) (fMinusElem n) :=
        kreinConjugate_mul (etaElem n) (etaElem_sq n)
          (fMinusElem n * a) (fMinusElem n)
      _ = (kreinConjugate (etaElem n) (fMinusElem n) *
            kreinConjugate (etaElem n) a) *
            kreinConjugate (etaElem n) (fMinusElem n) := by
        rw [kreinConjugate_mul (etaElem n) (etaElem_sq n)
          (fMinusElem n) a]
      _ = fPlusElem n * kreinConjugate (etaElem n) a * fPlusElem n := by
        simp [kreinConjugate, etaElem_fMinusElem_etaElem]

theorem krein_conjugate_plusMinus_mem_peirceCorner (n : ℕ) (a : Stage n) :
    kreinConjugate (etaElem n) (plusMinus n a) ∈
      peirceCorner (fMinusElem n) (fPlusElem n) := by
  rw [(krein_conjugates_peirce_blocks n a).2.1]
  exact (peirce_blocks_mem n (kreinConjugate (etaElem n) a)).2.2.1

theorem krein_conjugate_minusPlus_mem_peirceCorner (n : ℕ) (a : Stage n) :
    kreinConjugate (etaElem n) (minusPlus n a) ∈
      peirceCorner (fPlusElem n) (fMinusElem n) := by
  rw [(krein_conjugates_peirce_blocks n a).2.2.1]
  exact (peirce_blocks_mem n (kreinConjugate (etaElem n) a)).2.1

end

end InfoGeometry.Canonical.Cl11TwoSheetPeirceCorners
