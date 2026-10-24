/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteRealFockStageIsometry

/-! # Positive real pairing on the existing algebraic Fock direct limit

Two applications of the native universal property descend the finite pairing.
No new quotient, metric instance, or completed carrier is introduced.
-/
noncomputable section
namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

/-- Evaluate two finite vectors at their common stage. -/
def fockCommonInner (m n : ℕ) (x : FockStage m) (y : FockStage n) : ℝ :=
  inner ℝ (fockStageMap m (max m n) (le_max_left m n) x)
    (fockStageMap n (max m n) (le_max_right m n) y)

/-- Every common upper stage gives the same pairing. -/
theorem fockCommonInner_eq_at (m n k : ℕ) (hmk : m ≤ k) (hnk : n ≤ k)
    (x : FockStage m) (y : FockStage n) :
    fockCommonInner m n x y =
      inner ℝ (fockStageMap m k hmk x) (fockStageMap n k hnk y) := by
  have h := fockStageMap_inner (max m n) k (max_le hmk hnk)
    (fockStageMap m (max m n) (le_max_left m n) x)
    (fockStageMap n (max m n) (le_max_right m n) y)
  rw [← fockStageMap_apply_trans, ← fockStageMap_apply_trans] at h
  exact h.symm

/-- Symmetry uses the real finite metric at one common stage. -/
theorem fockCommonInner_symm (m n : ℕ) (x : FockStage m) (y : FockStage n) :
    fockCommonInner m n x y = fockCommonInner n m y x := by
  rw [fockCommonInner_eq_at m n (max m n) (le_max_left m n) (le_max_right m n),
    fockCommonInner_eq_at n m (max m n) (le_max_right m n) (le_max_left m n)]
  exact real_inner_comm _ _

/-- Compatibility in the second variable is derived from transition composition. -/
theorem fockCommonInner_map_right (m n k : ℕ) (hnk : n ≤ k)
    (x : FockStage m) (y : FockStage n) :
    fockCommonInner m k x (fockStageMap n k hnk y) = fockCommonInner m n x y := by
  rw [fockCommonInner_eq_at m k (max m k) (le_max_left m k) (le_max_right m k),
    fockCommonInner_eq_at m n (max m k) (le_max_left m k)
      (hnk.trans (le_max_right m k)), ← fockStageMap_apply_trans]

/-- Compatibility in the first variable follows from symmetry. -/
theorem fockCommonInner_map_left (m n k : ℕ) (hmn : m ≤ n)
    (x : FockStage m) (y : FockStage k) :
    fockCommonInner n k (fockStageMap m n hmn x) y = fockCommonInner m k x y := by
  rw [fockCommonInner_symm n k, fockCommonInner_map_right,
    fockCommonInner_symm k m]

/-- The finite functional in the second variable. -/
def fockPairingRightAtStage (m : ℕ) (x : FockStage m) (n : ℕ) :
    FockStage n →ₗ[ℝ] ℝ where
  toFun := fockCommonInner m n x
  map_add' y z := by simp only [fockCommonInner, map_add, inner_add_right]
  map_smul' r y := by
    simp only [fockCommonInner, map_smul, real_inner_smul_right,
      RingHom.id_apply, smul_eq_mul]

/-- First descent, against a fixed finite vector. -/
def fockPairStageAgainstInfinity (m : ℕ) (x : FockStage m) :
    FockInfinity →ₗ[ℝ] ℝ :=
  DirectLimit.Module.lift ℝ ℕ FockStage (fun i j h => fockStageMap i j h)
    (fockPairingRightAtStage m x)
    (fun i j hij y => fockCommonInner_map_right m i j hij x y)

/-- The descended functional varies linearly in its finite first argument. -/
def fockPairingLeftAtStage (m : ℕ) :
    FockStage m →ₗ[ℝ] (FockInfinity →ₗ[ℝ] ℝ) where
  toFun := fockPairStageAgainstInfinity m
  map_add' x y := by
    apply DirectLimit.Module.hom_ext
    intro n
    ext z
    change fockCommonInner m n (x + y) z =
      fockCommonInner m n x z + fockCommonInner m n y z
    simp only [fockCommonInner, map_add, inner_add_left]
  map_smul' r x := by
    apply DirectLimit.Module.hom_ext
    intro n
    ext z
    change fockCommonInner m n (r • x) z = r • fockCommonInner m n x z
    simp only [fockCommonInner, map_smul, real_inner_smul_left, smul_eq_mul]

/-- The actual bilinear pairing on the existing root direct limit. -/
def fockInfinityPairing : FockInfinity →ₗ[ℝ] (FockInfinity →ₗ[ℝ] ℝ) :=
  DirectLimit.Module.lift ℝ ℕ FockStage (fun i j h => fockStageMap i j h)
    fockPairingLeftAtStage (by
      intro i j hij x
      apply DirectLimit.Module.hom_ext
      intro k
      ext y
      exact fockCommonInner_map_left i j k hij x y)

/-- Readback computes on the actual native injections. -/
theorem fockInfinityPairing_stage (m n : ℕ) (x : FockStage m) (y : FockStage n) :
    fockInfinityPairing (fockToInfinity m x) (fockToInfinity n y) =
      fockCommonInner m n x y := rfl

/-- Same-stage readback recovers the accepted finite metric. -/
theorem fockInfinityPairing_same_stage (n : ℕ) (x y : FockStage n) :
    fockInfinityPairing (fockToInfinity n x) (fockToInfinity n y) = inner ℝ x y := by
  rw [fockInfinityPairing_stage, fockCommonInner_eq_at n n n le_rfl le_rfl]
  simp only [fockStageMap_refl, LinearMap.id_apply]

/-- Symmetry holds on every algebraic Fock vector. -/
theorem fockInfinityPairing_symm (x y : FockInfinity) :
    fockInfinityPairing x y = fockInfinityPairing y x := by
  obtain ⟨m, a, ha⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) x
  obtain ⟨n, b, hb⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) y
  have ha' : x = fockToInfinity m a := ha
  have hb' : y = fockToInfinity n b := hb
  rw [ha', hb', fockInfinityPairing_stage, fockInfinityPairing_stage]
  exact fockCommonInner_symm m n a b

/-- Positivity is inherited from the finite metric. -/
theorem fockInfinityPairing_self_nonneg (x : FockInfinity) :
    0 ≤ fockInfinityPairing x x := by
  obtain ⟨n, a, ha⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) x
  have ha' : x = fockToInfinity n a := ha
  rw [ha', fockInfinityPairing_same_stage, real_inner_self_eq_norm_sq]
  exact sq_nonneg _

/-- Definiteness is proved from a finite representative, not assumed on the quotient. -/
theorem fockInfinityPairing_self_eq_zero (x : FockInfinity) :
    fockInfinityPairing x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨n, a, ha⟩ := DirectLimit.exists_eq_mk
      (f := fun i j h => fockStageMap i j h) x
    have ha' : x = fockToInfinity n a := ha
    rw [ha', fockInfinityPairing_same_stage] at hx
    have hz : a = 0 := inner_self_eq_zero.mp hx
    rw [ha', hz]
    exact map_zero (DirectLimit.Module.of ℝ ℕ FockStage
      (fun i j h => fockStageMap i j h) n)
  · rintro rfl
    simp only [map_zero, LinearMap.zero_apply]

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
