import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite-stage obstruction for the Cuntz relation

The binary Cuntz relations require two isometries with orthogonal ranges whose
range projections sum to the identity.  This cannot happen in a finite matrix
algebra.  The obstruction is a trace identity, and records why the concrete
Cantor-boundary realization cannot be replaced by a single finite Clifford
tower stage.
-/

namespace InfoGeometry.Canonical.CuntzFiniteStageObstruction

open scoped Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix

theorem no_binary_cuntz_family_at_finite_stage (n : ℕ)
    (S T : MatStage n)
    (hS : Sᵀ * S = 1)
    (hT : Tᵀ * T = 1)
    (hPartition : S * Sᵀ + T * Tᵀ = 1) :
    False := by
  have hS_trace : Matrix.trace (S * Sᵀ) = Matrix.trace (1 : MatStage n) := by
    calc
      Matrix.trace (S * Sᵀ) = Matrix.trace (Sᵀ * S) := by
        exact Matrix.trace_mul_comm S Sᵀ
      _ = Matrix.trace (1 : MatStage n) := congrArg Matrix.trace hS
  have hT_trace : Matrix.trace (T * Tᵀ) = Matrix.trace (1 : MatStage n) := by
    calc
      Matrix.trace (T * Tᵀ) = Matrix.trace (Tᵀ * T) := by
        exact Matrix.trace_mul_comm T Tᵀ
      _ = Matrix.trace (1 : MatStage n) := congrArg Matrix.trace hT
  have hTrace := congrArg Matrix.trace hPartition
  rw [Matrix.trace_add, hS_trace, hT_trace, Matrix.trace_one] at hTrace
  have hCard : 0 < Fintype.card (Idx n) := Fintype.card_pos
  have hCardReal : (0 : ℝ) < Fintype.card (Idx n) := by
    exact_mod_cast hCard
  linarith

/-- At a finite matrix stage, each isometry contributes one full stage
dimension to the trace of its range projection. This exact count is the
positive invariant behind the Cuntz partition obstruction. -/
theorem trace_sum_range_projections_of_isometries
    {m n : ℕ} (S : Fin m → MatStage n)
    (hS : ∀ i, (S i)ᵀ * S i = 1) :
    Matrix.trace (∑ i : Fin m, S i * (S i)ᵀ) =
      (m : ℝ) * Fintype.card (Idx n) := by
  rw [Matrix.trace_sum]
  have hEach : ∀ i : Fin m,
      Matrix.trace (S i * (S i)ᵀ) = Fintype.card (Idx n) := by
    intro i
    calc
      Matrix.trace (S i * (S i)ᵀ) = Matrix.trace ((S i)ᵀ * S i) := by
        exact Matrix.trace_mul_comm (S i) (S i)ᵀ
      _ = Matrix.trace (1 : MatStage n) := congrArg Matrix.trace (hS i)
      _ = Fintype.card (Idx n) := Matrix.trace_one
  simp_rw [hEach]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

/-- Exact finite-stage boundary: if a finite family of isometries has range
projections summing to the identity, then the family has exactly one member.
This is the positive cardinality characterization underlying the obstruction,
without assuming in advance that the family has at least two members. -/
theorem isometry_range_partition_implies_card_eq_one
    {m n : ℕ} (S : Fin m → MatStage n)
    (hS : ∀ i, (S i)ᵀ * S i = 1)
    (hPartition : ∑ i : Fin m, S i * (S i)ᵀ = 1) :
    m = 1 := by
  have hTrace := congrArg Matrix.trace hPartition
  rw [trace_sum_range_projections_of_isometries S hS, Matrix.trace_one] at hTrace
  have hCard : 0 < Fintype.card (Idx n) := Fintype.card_pos
  have hCardReal : (0 : ℝ) < Fintype.card (Idx n) := by
    exact_mod_cast hCard
  have hmReal : (m : ℝ) = 1 := by
    nlinarith
  exact_mod_cast hmReal

/-- The same trace obstruction holds for every finite family with at least two
isometries whose range projections partition the identity. -/
theorem no_finite_cuntz_family_at_finite_stage
    {m n : ℕ} (hm : 2 ≤ m)
    (S : Fin m → MatStage n)
    (hS : ∀ i, (S i)ᵀ * S i = 1)
    (hPartition : ∑ i : Fin m, S i * (S i)ᵀ = 1) :
    False := by
  have hTrace := congrArg Matrix.trace hPartition
  rw [trace_sum_range_projections_of_isometries S hS] at hTrace
  rw [Matrix.trace_one] at hTrace
  have hCard : 0 < Fintype.card (Idx n) := Fintype.card_pos
  have hCardReal : (0 : ℝ) < Fintype.card (Idx n) := by
    exact_mod_cast hCard
  have hTrace' : (m : ℝ) * Fintype.card (Idx n) = Fintype.card (Idx n) := by
    simpa using hTrace
  have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmOne : (1 : ℝ) < m := lt_of_lt_of_le (by norm_num) hmReal
  have hmul : Fintype.card (Idx n) <
      (m : ℝ) * Fintype.card (Idx n) := by
    have hmul' := mul_lt_mul_of_pos_right hmOne hCardReal
    simpa using hmul'
  linarith [hTrace', hmul]

end InfoGeometry.Canonical.CuntzFiniteStageObstruction
