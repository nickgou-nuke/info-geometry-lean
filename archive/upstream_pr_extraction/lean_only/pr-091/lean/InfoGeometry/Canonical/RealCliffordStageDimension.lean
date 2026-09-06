import InfoGeometry.Clifford.Cl11TensorTower

/-!
# Dimension of the real `Cl(1,1)` matrix stages

The executable real tensor tower has stage carrier `MatStage n`, a matrix
algebra indexed by the binary tensor index `Idx n`.  This owner records the
finite-dimensional dimension law only.  It does not identify a completion
with a UHF algebra and does not assert a `K₀` or `KO₀` theorem.
-/

namespace InfoGeometry.Canonical.RealCliffordStageDimension

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix

theorem matStage_finrank (n : ℕ) :
    Module.finrank ℝ (MatStage n) = 4 ^ n := by
  rw [(matEquivFinPowTwo n).toLinearEquiv.finrank_eq]
  rw [Module.finrank_matrix]
  simp only [Fintype.card_fin, Module.finrank_self, mul_one]
  calc
    2 ^ n * 2 ^ n = 2 ^ (n * 2) := by
      rw [← pow_add]
      congr 1 <;> omega
    _ = 2 ^ (2 * n) := by rw [Nat.mul_comm]
    _ = (2 ^ 2) ^ n := by rw [pow_mul]
    _ = 4 ^ n := by norm_num

theorem matStage_finrank_succ (n : ℕ) :
    Module.finrank ℝ (MatStage (n + 1)) =
      4 * Module.finrank ℝ (MatStage n) := by
  rw [matStage_finrank, matStage_finrank]
  rw [pow_succ]
  ring

end InfoGeometry.Canonical.RealCliffordStageDimension
