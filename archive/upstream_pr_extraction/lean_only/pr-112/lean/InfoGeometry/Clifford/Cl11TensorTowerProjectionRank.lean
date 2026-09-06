import InfoGeometry.Canonical.RealProjectionRank
import InfoGeometry.Clifford.Cl11TensorTower

/-!
# Finite-stage projection-rank data for the real Clifford tower

This owner records only facts proved from the existing native `MatStage` and
`stageEmbed` APIs.  In particular, it does not identify a projection rank
system with `K₀` or `KO₀`, and it keeps the missing Kronecker rank theorem
explicit rather than replacing it with a wrapper assertion.
-/

namespace InfoGeometry.Clifford.Cl11TensorTower

open InfoGeometry.Canonical

theorem matStage_index_card (n : ℕ) :
    Fintype.card (TowerMatrix.Idx n) = 2 ^ n :=
  TowerMatrix.idx_card_pow_two n

theorem matStage_finrank (n : ℕ) :
    Module.finrank ℝ (MatStage n) = 4 ^ n := by
  simp [MatStage, InfoGeometry.Clifford.TowerMatrix.Mat,
    Module.finrank_matrix, TowerMatrix.idx_card_pow_two]
  calc
    (2 ^ n) * (2 ^ n) = (2 ^ n) ^ 2 := by ring
    _ = 2 ^ (n * 2) := (pow_mul 2 n 2).symm
    _ = 2 ^ (2 * n) := by rw [Nat.mul_comm]
    _ = (2 ^ 2) ^ n := pow_mul 2 2 n
    _ = 4 ^ n := by norm_num

theorem matStageEmbed_idempotent
    {n : ℕ} {p : MatStage n} (hp : p * p = p) :
    stageEmbed n p * stageEmbed n p = stageEmbed n p := by
  simpa only [map_mul] using congrArg (stageEmbed n) hp

/- Rank of the linear operator represented by a square matrix.  This uses
   Mathlib's native linear-map range, rather than the unavailable `Matrix.rank`
   name from older drafts. -/
noncomputable def matrixRangeRank
    (n : ℕ) (A : MatStage n) : ℕ :=
  Module.finrank ℝ (LinearMap.range (Matrix.toLin' A))

noncomputable def normalizedMatrixRank
    (n : ℕ) (A : MatStage n) : ℚ :=
  (matrixRangeRank n A : ℚ) / (2 : ℚ) ^ n

theorem normalizedMatrixRank_embed_of_rank_transition
    (n : ℕ) (A : MatStage n)
    (h_rank : matrixRangeRank (n + 1) (stageEmbed n A) =
      2 * matrixRangeRank n A) :
    normalizedMatrixRank (n + 1) (stageEmbed n A) =
      normalizedMatrixRank n A := by
  unfold normalizedMatrixRank
  rw [h_rank]
  field_simp
  norm_num [Nat.cast_mul]
  ring

end InfoGeometry.Clifford.Cl11TensorTower
