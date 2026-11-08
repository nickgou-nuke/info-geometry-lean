/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

noncomputable section

namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

/-- The positive chiral projector on the algebraic Fock colimit induced by
Mathlib's native Clifford grade involution. -/
def fockInfinityProjectorPlus (ψ : FockInfinity) : FockInfinity :=
  (1 / 2 : ℝ) • (ψ + fockInfinityInvolute ψ)

/-- The negative chiral projector on the algebraic Fock colimit induced by
Mathlib's native Clifford grade involution. -/
def fockInfinityProjectorMinus (ψ : FockInfinity) : FockInfinity :=
  (1 / 2 : ℝ) • (ψ - fockInfinityInvolute ψ)

/-- Zero-head Fock bonding maps transport the finite-stage positive chiral
projector exactly. -/
theorem fockStageMap_projectorPlus
    (m n : ℕ) (h : m ≤ n) (ψ : FockStage m) :
    fockStageMap m n h
        ((1 / 2 : ℝ) • (ψ + CliffordAlgebra.involute ψ)) =
      (1 / 2 : ℝ) •
        (fockStageMap m n h ψ +
          CliffordAlgebra.involute (fockStageMap m n h ψ)) := by
  rw [map_smul, map_add, fockStageMap_involute]

/-- Zero-head Fock bonding maps transport the finite-stage negative chiral
projector exactly. -/
theorem fockStageMap_projectorMinus
    (m n : ℕ) (h : m ≤ n) (ψ : FockStage m) :
    fockStageMap m n h
        ((1 / 2 : ℝ) • (ψ - CliffordAlgebra.involute ψ)) =
      (1 / 2 : ℝ) •
        (fockStageMap m n h ψ -
          CliffordAlgebra.involute (fockStageMap m n h ψ)) := by
  rw [map_smul, map_sub, fockStageMap_involute]

/-- The two induced chiral projectors partition every Fock-colimit vector. -/
theorem fockInfinityProjectorPlus_add_minus (ψ : FockInfinity) :
    fockInfinityProjectorPlus ψ + fockInfinityProjectorMinus ψ = ψ := by
  dsimp [fockInfinityProjectorPlus, fockInfinityProjectorMinus]
  rw [← smul_add]
  have hsum : (ψ + fockInfinityInvolute ψ) +
      (ψ - fockInfinityInvolute ψ) = (2 : ℝ) • ψ := by
    rw [show (ψ + fockInfinityInvolute ψ) +
        (ψ - fockInfinityInvolute ψ) = ψ + ψ by abel]
    exact (two_smul ℝ ψ).symm
  rw [hsum, ← mul_smul]
  norm_num

/-- The difference of the induced chiral projectors is the Fock-colimit
parity involution. -/
theorem fockInfinityProjectorPlus_sub_minus (ψ : FockInfinity) :
    fockInfinityProjectorPlus ψ - fockInfinityProjectorMinus ψ =
      fockInfinityInvolute ψ := by
  dsimp [fockInfinityProjectorPlus, fockInfinityProjectorMinus]
  rw [← smul_sub]
  have hdiff : (ψ + fockInfinityInvolute ψ) -
      (ψ - fockInfinityInvolute ψ) =
      (2 : ℝ) • fockInfinityInvolute ψ := by
    rw [show (ψ + fockInfinityInvolute ψ) -
        (ψ - fockInfinityInvolute ψ) =
        fockInfinityInvolute ψ + fockInfinityInvolute ψ by abel]
    exact (two_smul ℝ (fockInfinityInvolute ψ)).symm
  rw [hdiff, ← mul_smul]
  norm_num

/-- Each induced chiral projector is idempotent. -/
theorem fockInfinityProjectorPlus_idempotent (ψ : FockInfinity) :
    fockInfinityProjectorPlus (fockInfinityProjectorPlus ψ) =
      fockInfinityProjectorPlus ψ := by
  dsimp [fockInfinityProjectorPlus]
  rw [map_smul, map_add]
  rw [fockInfinityInvolute_involutive]
  module

/-- Each induced chiral projector is idempotent. -/
theorem fockInfinityProjectorMinus_idempotent (ψ : FockInfinity) :
    fockInfinityProjectorMinus (fockInfinityProjectorMinus ψ) =
      fockInfinityProjectorMinus ψ := by
  dsimp [fockInfinityProjectorMinus]
  rw [map_smul, map_sub]
  rw [fockInfinityInvolute_involutive]
  module

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
