import InfoGeometry.Clifford.LogCftMonodromy
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section

namespace InfoGeometry.Canonical.LogJordanKreinCore

open Matrix
open Matrix.Norms.Frobenius

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The existing rank-two nilpotent Jordan shear. -/
abbrev N : M2R :=
  InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent

/-- The existing equal-diagonal Jordan cell. -/
abbrev L0 (delta : ℝ) : M2R :=
  InfoGeometry.Clifford.LogCftMonodromy.virasoroL0Cell delta

/-- The split symmetric form on the rank-two carrier. -/
def kreinG : M2R :=
  !![0, 1; 1, 0]

/-- The standard parity operator on the rank-two carrier. -/
def parity : M2R :=
  !![1, 0; 0, -1]

/-- The columns `(1,1)` and `(1,-1)` diagonalize the split form by congruence. -/
def signatureChange : M2R :=
  !![1, 1; 1, -1]

theorem jordanNilpotent_sq :
    N * N = 0 :=
  InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent_sq

theorem jordanNilpotent_ne_zero :
    N ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [N, InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent] at h01

/-- The Jordan cell is self-adjoint for the split symmetric form. -/
theorem jordanCell_krein_selfAdjoint (delta : ℝ) :
    (L0 delta).transpose * kreinG = kreinG * L0 delta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L0, InfoGeometry.Clifford.LogCftMonodromy.virasoroL0Cell,
      InfoGeometry.Clifford.LogCftMonodromy.upperJordan, kreinG,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem signatureChange_det :
    signatureChange.det = -2 := by
  norm_num [signatureChange, Matrix.det_fin_two]

theorem signatureChange_det_ne_zero :
    signatureChange.det ≠ 0 := by
  rw [signatureChange_det]
  norm_num

/--
Explicit signature `(1,1)` certificate:
an invertible real congruence carries `kreinG` to `diag(2,-2)`.
-/
theorem kreinG_congr_diagonal :
    signatureChange.transpose * kreinG * signatureChange =
      Matrix.diagonal ![(2 : ℝ), -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signatureChange, kreinG, Matrix.mul_apply, Fin.sum_univ_two]

/--
Concrete diagonalizability contract: the columns of an invertible matrix form
an eigenbasis, encoded by `A P = P (diagonal eigenvalues)`.
-/
def HasRealEigenbasis (A : M2R) : Prop :=
  ∃ P : M2Rˣ, ∃ eigenvalues : Fin 2 → ℝ,
    A * (P : M2R) = (P : M2R) * Matrix.diagonal eigenvalues

/-- Every real eigenvector of the Jordan cell has zero second coordinate. -/
theorem jordanCell_eigenvector_second_eq_zero
    (delta mu : ℝ) (v : Fin 2 → ℝ)
    (h : Matrix.toLin' (L0 delta) v = mu • v) :
    v 1 = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [L0, InfoGeometry.Clifford.LogCftMonodromy.virasoroL0Cell,
    InfoGeometry.Clifford.LogCftMonodromy.upperJordan,
    Matrix.toLin'_apply, dotProduct, Fin.sum_univ_two] at h0 h1
  rcases h1 with hdelta | hv
  · rw [hdelta] at h0
    linarith
  · exact hv

private theorem column_is_eigenvector
    {A P : M2R} {eigenvalues : Fin 2 → ℝ}
    (h : A * P = P * Matrix.diagonal eigenvalues) (j : Fin 2) :
    Matrix.toLin' A (fun i => P i j) =
      eigenvalues j • (fun i => P i j) := by
  ext i
  have hij := congrFun (congrFun h i) j
  simpa [Matrix.toLin'_apply, Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_two, Matrix.diagonal_apply, mul_comm] using hij

/-- The nontrivial Jordan cell has no real eigenbasis. -/
theorem jordanCell_not_diagonalizable (delta : ℝ) :
    ¬ HasRealEigenbasis (L0 delta) := by
  rintro ⟨P, eigenvalues, hP⟩
  have hrow : ∀ j : Fin 2, (P : M2R) 1 j = 0 := by
    intro j
    exact jordanCell_eigenvector_second_eq_zero delta (eigenvalues j) _
      (column_is_eigenvector hP j)
  have hinv : (P : M2R) * (↑P⁻¹ : M2R) = 1 := Units.mul_inv P
  have h11 := congrFun (congrFun hinv 1) 1
  simp [Matrix.mul_apply, hrow] at h11

private theorem exp_smul_nilpotent (t : ℝ) :
    NormedSpace.exp (t • N) = (1 : M2R) + t • N := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  change (∑' n : ℕ, ((Nat.factorial n : ℕ) : ℝ)⁻¹ • (t • N) ^ n) = _
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, pow_zero, pow_one]
  · intro n hn
    have h2n : 2 ≤ n := by
      simpa using hn
    have hpow2 : (t • N) ^ 2 = 0 := by
      rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul,
        jordanNilpotent_sq, smul_zero]
    rw [pow_eq_zero_of_le h2n hpow2, smul_zero]

private theorem exp_smul_one (s : ℝ) :
    NormedSpace.exp (s • (1 : M2R)) =
      Real.exp s • (1 : M2R) := by
  have hs : s • (1 : M2R) = Matrix.diagonal (fun _ : Fin 2 => s) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [hs, Matrix.exp_diagonal]
  ext i j
  by_cases h : i = j <;> simp [h, Real.exp_eq_exp_ℝ]

/-- Exact exponential of the rank-two Jordan cell. -/
theorem exp_jordanCell (t delta : ℝ) :
    NormedSpace.exp (t • L0 delta) =
      Real.exp (t * delta) • ((1 : M2R) + t • N) := by
  have hdecomp :
      t • L0 delta = (t * delta) • (1 : M2R) + t • N := by
    change
      t • InfoGeometry.Clifford.LogCftMonodromy.virasoroL0Cell delta =
        (t * delta) • (1 : M2R) +
          t • InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent
    rw [InfoGeometry.Clifford.LogCftMonodromy.l0_cell_decomposition]
    module
  rw [hdecomp, NormedSpace.exp_add_of_commute]
  · rw [exp_smul_one, exp_smul_nilpotent]
    simp
  · exact (Commute.one_left (t • N)).smul_left (t * delta)

/-- The ordinary trace does not detect the nilpotent coefficient. -/
theorem trace_exp_jordanCell (t delta : ℝ) :
    Matrix.trace (NormedSpace.exp (t • L0 delta)) =
      2 * Real.exp (t * delta) := by
  rw [exp_jordanCell]
  simp [Matrix.trace, N,
    InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent,
    Fin.sum_univ_two]
  ring

/-- Insertion of `Nᵀ` extracts the linear Jordan coefficient. -/
theorem detector_trace_jordanCell (t delta : ℝ) :
    Matrix.trace (N.transpose * NormedSpace.exp (t • L0 delta)) =
      t * Real.exp (t * delta) := by
  rw [exp_jordanCell]
  simp [Matrix.trace, N,
    InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The parity insertion vanishes and does not recover the Jordan coefficient. -/
theorem parity_trace_jordanCell (t delta : ℝ) :
    Matrix.trace (parity * NormedSpace.exp (t • L0 delta)) = 0 := by
  rw [exp_jordanCell]
  simp [Matrix.trace, parity, N,
    InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent,
    Matrix.vecMul, dotProduct, Fin.sum_univ_two]

end InfoGeometry.Canonical.LogJordanKreinCore
