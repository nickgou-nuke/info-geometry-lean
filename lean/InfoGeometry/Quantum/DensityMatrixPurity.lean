import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.DensityMatrixPurity

open Matrix Complex

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def densityMatrix (S1 S2 S3 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![((1 + S3 : ℝ) / 2 : ℂ), ((S1 : ℝ) - Complex.I * (S2 : ℝ)) / 2],
    ![((S1 : ℝ) + Complex.I * (S2 : ℝ)) / 2, ((1 - S3 : ℝ) / 2 : ℂ)]]

theorem densityMatrix_trace (S1 S2 S3 : ℝ) :
    Matrix.trace (densityMatrix S1 S2 S3) = 1 := by
  unfold densityMatrix Matrix.trace
  simp [Fin.sum_univ_two]
  ring

def purity (S1 S2 S3 : ℝ) : ℝ :=
  (1 + S1 ^ 2 + S2 ^ 2 + S3 ^ 2) / 2

theorem densityMatrix_purity_eq (S1 S2 S3 : ℝ) :
    (Matrix.trace (densityMatrix S1 S2 S3 * densityMatrix S1 S2 S3)).re = purity S1 S2 S3 := by
  unfold densityMatrix purity Matrix.trace
  simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
  ring

theorem purity_le_one (S1 S2 S3 : ℝ) (h_bloch : S1 ^ 2 + S2 ^ 2 + S3 ^ 2 ≤ 1) :
    purity S1 S2 S3 ≤ 1 := by
  unfold purity
  linarith

theorem purity_eq_one_iff (S1 S2 S3 : ℝ) :
    purity S1 S2 S3 = 1 ↔ S1 ^ 2 + S2 ^ 2 + S3 ^ 2 = 1 := by
  unfold purity
  constructor <;> intro h <;> linarith

theorem densityMatrix_pure_equator_confinement (S1 S2 : ℝ)
    (h_pure : purity S1 S2 0 = 1) :
    S1 ^ 2 + S2 ^ 2 = 1 := by
  have h := (purity_eq_one_iff S1 S2 0).mp h_pure
  linarith
