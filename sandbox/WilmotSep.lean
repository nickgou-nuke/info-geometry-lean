import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Algebra.Zorn.G2KillingCartanMatrix

noncomputable section
namespace ScratchWilmot

open Matrix
open InfoGeometry.Algebra.Zorn.G2KillingCartanMatrix

noncomputable def bryantGen (m : Fin 14) : Matrix (Fin 7) (Fin 7) ℝ :=
  match m with
  | 0  => (1/2 : ℝ) • (skewGen 1 2 - skewGen 3 4)
  | 1  => (1/2 : ℝ) • (- skewGen 0 2 - skewGen 3 5)
  | 2  => (1/2 : ℝ) • (skewGen 0 1 + skewGen 3 6)
  | 3  => (1/2 : ℝ) • (skewGen 0 4 + skewGen 1 5)
  | 4  => (1/2 : ℝ) • (skewGen 0 3 - skewGen 1 6)
  | 5  => (1/2 : ℝ) • (skewGen 0 6 + skewGen 1 3)
  | 6  => (1/2 : ℝ) • (- skewGen 0 5 - skewGen 1 4)
  | 7  => (1/2 : ℝ) • (skewGen 3 4 - skewGen 5 6)
  | 8  => (1/2 : ℝ) • (skewGen 3 5 + skewGen 4 6)
  | 9  => (1/2 : ℝ) • (- skewGen 3 6 + skewGen 4 5)
  | 10 => (1/2 : ℝ) • (- skewGen 1 5 - skewGen 2 6)
  | 11 => (1/2 : ℝ) • (- skewGen 1 6 + skewGen 2 5)
  | 12 => (1/2 : ℝ) • (- skewGen 0 6 + skewGen 2 4)
  | 13 => (1/2 : ℝ) • (skewGen 1 4 - skewGen 2 3)

/-- Separating row coordinate. -/
def sr : Fin 14 → Fin 7 :=
  fun i => match i with
  | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0
  | 7 => 5 | 8 => 4 | 9 => 4 | 10 => 2 | 11 => 2 | 12 => 2 | 13 => 2

/-- Separating column coordinate. -/
def ss : Fin 14 → Fin 7 :=
  fun i => match i with
  | 0 => 2 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
  | 7 => 6 | 8 => 6 | 9 => 5 | 10 => 6 | 11 => 5 | 12 => 4 | 13 => 3

theorem bryantGen_diag_ne_zero (i : Fin 14) :
    bryantGen i (sr i) (ss i) ≠ 0 := by
  fin_cases i <;> simp [bryantGen, sr, ss, skewGen] <;> norm_num

set_option maxHeartbeats 2000000 in
theorem bryantGen_cross_zero (j i : Fin 14) (h : j ≠ i) :
    bryantGen j (sr i) (ss i) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [bryantGen, sr, ss, skewGen, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply]
    <;> norm_num
    <;> first
      | rfl
      | (exfalso; simp only [ne_eq, not_not] at h; exact h (by decide))
      | (exfalso; simp only [ne_eq, not_not] at h; exact h (by
          simp only [Fin.val_inj, ne_eq]
          fin_cases i <;> fin_cases j <;> decide))

theorem bryantGen_linearIndependent :
    LinearIndependent ℝ bryantGen := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℝ => M (sr i) (ss i)) hg
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_apply] at h
  rw [Finset.sum_eq_single i, mul_eq_zero] at h
  · exact h.resolve_left (bryantGen_diag_ne_zero i)
  · intro j _ hj
    rw [bryantGen_cross_zero j i hj]
  · simp

end ScratchWilmot
