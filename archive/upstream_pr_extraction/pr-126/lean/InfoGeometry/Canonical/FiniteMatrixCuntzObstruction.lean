import InfoGeometry.Canonical.Cuntz2Isometries
import InfoGeometry.Clifford.Cl11TensorTower
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Finite-dimensional obstruction for Cuntz O₂ generators

The normalized matrix trace tower is a genuine noncommutative UHF tower, but
it cannot itself be a stagewise `Cuntz2Isometries` tower: two isometries with
orthogonal ranges would force `2 * dim = dim`.  This theorem records that
trace obstruction explicitly, preventing an invalid concrete Cuntz
instantiation at finite matrix stages.
-/

namespace InfoGeometry.Canonical.FiniteMatrixCuntzObstruction

open CuntzAlgebra

theorem no_cuntz2_matrix {n : ℕ} (hn : 0 < n)
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra
      (N := 2) (Matrix (Fin n) (Fin n) ℂ)) : False := by
  have h₁ : Matrix.trace (CuntzAlgebra.S1 C * star (CuntzAlgebra.S1 C)) = (n : ℂ) := by
    rw [Matrix.trace_mul_comm, CuntzAlgebra.h_isometry1 C, Matrix.trace_one]
    simp
  have h₂ : Matrix.trace (CuntzAlgebra.S2 C * star (CuntzAlgebra.S2 C)) = (n : ℂ) := by
    rw [Matrix.trace_mul_comm, CuntzAlgebra.h_isometry2 C, Matrix.trace_one]
    simp
  have hsum := congrArg Matrix.trace (CuntzAlgebra.h_range_sum C)
  rw [Matrix.trace_add, h₁, h₂, Matrix.trace_one] at hsum
  have hnat' : n + n = Fintype.card (Fin n) := by
    exact_mod_cast hsum
  have hnat : n + n = n := by
    simpa using hnat'
  omega

theorem no_cuntz2_real_cl11_stage (n : ℕ)
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra
      (N := 2) (InfoGeometry.Clifford.Cl11TensorTower.MatStage n)) : False := by
  have h₁ : Matrix.trace (CuntzAlgebra.S1 C * star (CuntzAlgebra.S1 C)) =
      ((2 ^ n : ℕ) : ℝ) := by
    rw [Matrix.trace_mul_comm, CuntzAlgebra.h_isometry1 C, Matrix.trace_one]
    simpa only [InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two]
  have h₂ : Matrix.trace (CuntzAlgebra.S2 C * star (CuntzAlgebra.S2 C)) =
      ((2 ^ n : ℕ) : ℝ) := by
    rw [Matrix.trace_mul_comm, CuntzAlgebra.h_isometry2 C, Matrix.trace_one]
    simpa only [InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two]
  have hsum := congrArg Matrix.trace (CuntzAlgebra.h_range_sum C)
  rw [Matrix.trace_add, h₁, h₂, Matrix.trace_one,
    InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two] at hsum
  have hnat : 2 ^ n + 2 ^ n = 2 ^ n := by
    apply Nat.cast_injective (R := ℝ)
    simpa [Nat.cast_add] using hsum
  have hpos : 0 < 2 ^ n := pow_pos (by decide) n
  omega

end InfoGeometry.Canonical.FiniteMatrixCuntzObstruction
