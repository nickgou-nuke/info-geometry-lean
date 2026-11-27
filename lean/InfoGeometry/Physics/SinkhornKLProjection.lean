/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.AmariSinkhornAlternatingProjections
import InfoGeometry.Prequantum.JaynesKLPotential
import InfoGeometry.PositiveMeasure

/-!
# The actual finite Sinkhorn KL projection identity

The existing rectangular updates and scalar generalized KL divergence are reused.
Competitors may have zero entries. Positivity is required of the reference matrix
and of a diagonally scaled candidate. The Pythagorean identity proves the
variational meaning and uniqueness of a balanced scaling; existence and actual
iteration convergence are supplied by the downstream convergence owner.
-/
noncomputable section
open scoped BigOperators
namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections
open InfoGeometry.Prequantum.JaynesKLPotential
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Generalized KL with a nonnegative first argument and positive reference. -/
def matrixKL (P Q : TransportPlan I J) : ℝ :=
  ∑ i, ∑ j, scalarKLDivergence (P i j) (Q i j)

theorem scalarKLDivergence_nonneg_left {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    0 ≤ scalarKLDivergence x y := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    simpa [scalarKLDivergence] using hy.le
  · exact scalarKLDivergence_nonneg x y h hy

theorem scalarKLDivergence_eq_zero_iff_nonneg {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) :
    scalarKLDivergence x y = 0 ↔ x = y := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    simp [scalarKLDivergence, hy.ne', hy.ne]
  · simpa [scalarKLDivergence, InfoGeometry.PositiveMeasure.gklTerm] using
      InfoGeometry.PositiveMeasure.gklTerm_eq_zero_iff x y h hy

theorem matrixKL_nonneg (P Q : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j) (hQ : ∀ i j, 0 < Q i j) :
    0 ≤ matrixKL P Q := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    scalarKLDivergence_nonneg_left (hP i j) (hQ i j)

theorem matrixKL_eq_zero_iff (P Q : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j) (hQ : ∀ i j, 0 < Q i j) :
    matrixKL P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
        Finset.sum_nonneg fun j _ =>
          scalarKLDivergence_nonneg_left (hP i j) (hQ i j))).1 h
    funext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset J)) =>
        scalarKLDivergence_nonneg_left (hP i j) (hQ i j))).1
      (hi i (Finset.mem_univ i))
    exact (scalarKLDivergence_eq_zero_iff_nonneg (hP i j) (hQ i j)).1
      (hj j (Finset.mem_univ j))
  · rintro rfl
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      scalarKLDivergence_self_zero _ (hQ i j)

/-- The first argument may vanish in this exact three-point identity. -/
theorem scalarKLDivergence_three_point (x y z : ℝ) (hy : 0 < y) (hz : 0 < z) :
    scalarKLDivergence x z = scalarKLDivergence x y +
      scalarKLDivergence y z + (x - y) * Real.log (y / z) := by
  by_cases hx : x = 0
  · subst x
    simp [scalarKLDivergence]
    ring
  · simp only [scalarKLDivergence, Real.log_div hx hy.ne',
      Real.log_div hx hz.ne', Real.log_div hy.ne' hz.ne']
    ring

/-- The marginal constraint annihilates a row-plus-column potential. -/
theorem marginal_potential_pairing_zero (P Q : TransportPlan I J)
    (a : I → ℝ) (b : J → ℝ)
    (hr : ∀ i, rowMass P i = rowMass Q i)
    (hc : ∀ j, colMass P j = colMass Q j) :
    (∑ i, ∑ j, (P i j - Q i j) * (a i + b j)) = 0 := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hrow : (∑ i, ∑ j, (P i j - Q i j) * a i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    change (rowMass P i - rowMass Q i) * a i = 0
    rw [hr i, sub_self, zero_mul]
  have hcol : (∑ i, ∑ j, (P i j - Q i j) * b j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    change (colMass P j - colMass Q j) * b j = 0
    rw [hc j, sub_self, zero_mul]
  rw [hrow, hcol, add_zero]

theorem matrixKL_pythagorean_of_logRatio (P Q K : TransportPlan I J)
    (hQ : ∀ i j, 0 < Q i j) (hK : ∀ i j, 0 < K i j)
    (a : I → ℝ) (b : J → ℝ)
    (hlog : ∀ i j, Real.log (Q i j / K i j) = a i + b j)
    (hr : ∀ i, rowMass P i = rowMass Q i)
    (hc : ∀ j, colMass P j = colMass Q j) :
    matrixKL P K = matrixKL P Q + matrixKL Q K := by
  have hpoint : ∀ i j, scalarKLDivergence (P i j) (K i j) =
      scalarKLDivergence (P i j) (Q i j) +
      scalarKLDivergence (Q i j) (K i j) +
      (P i j - Q i j) * (a i + b j) := by
    intro i j
    rw [← hlog i j]
    exact scalarKLDivergence_three_point _ _ _ (hQ i j) (hK i j)
  unfold matrixKL
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [marginal_potential_pairing_zero P Q a b hr hc, add_zero]

theorem logRatio_of_diagonal_scaling (K : TransportPlan I J)
    (u : I → ℝ) (v : J → ℝ)
    (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (i : I) (j : J) :
    Real.log (u i * K i j * v j / K i j) = Real.log (u i) + Real.log (v j) := by
  have hcancel : u i * K i j * v j / K i j = u i * v j := by
    field_simp [(hK i j).ne'] <;> ring
  rw [hcancel, Real.log_mul (hu i).ne' (hv j).ne']

theorem matrixKL_pythagorean_of_scaling (P K : TransportPlan I J)
    (u : I → ℝ) (v : J → ℝ)
    (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hr : ∀ i, rowMass P i = rowMass (fun i j => u i * K i j * v j) i)
    (hc : ∀ j, colMass P j = colMass (fun i j => u i * K i j * v j) j) :
    matrixKL P K = matrixKL P (fun i j => u i * K i j * v j) +
      matrixKL (fun i j => u i * K i j * v j) K := by
  apply matrixKL_pythagorean_of_logRatio P _ K
    (fun i j => mul_pos (mul_pos (hu i) (hK i j)) (hv j)) hK
    (fun i => Real.log (u i)) (fun j => Real.log (v j))
    (logRatio_of_diagonal_scaling K u v hK hu hv) hr hc

/-- A positive balanced scaling minimizes KL over nonnegative feasible competitors. -/
theorem matrixKL_scaling_minimizes (P K : TransportPlan I J)
    (u : I → ℝ) (v : J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hK : ∀ i j, 0 < K i j)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hr : ∀ i, rowMass P i = rowMass (fun i j => u i * K i j * v j) i)
    (hc : ∀ j, colMass P j = colMass (fun i j => u i * K i j * v j) j) :
    matrixKL (fun i j => u i * K i j * v j) K ≤ matrixKL P K := by
  rw [matrixKL_pythagorean_of_scaling P K u v hK hu hv hr hc]
  exact le_add_of_nonneg_left (matrixKL_nonneg P _ hP
    (fun i j => mul_pos (mul_pos (hu i) (hK i j)) (hv j)))

theorem matrixKL_scaling_eq_iff (P K : TransportPlan I J)
    (u : I → ℝ) (v : J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hK : ∀ i j, 0 < K i j)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hr : ∀ i, rowMass P i = rowMass (fun i j => u i * K i j * v j) i)
    (hc : ∀ j, colMass P j = colMass (fun i j => u i * K i j * v j) j) :
    matrixKL P K = matrixKL (fun i j => u i * K i j * v j) K ↔
      P = (fun i j => u i * K i j * v j) := by
  rw [matrixKL_pythagorean_of_scaling P K u v hK hu hv hr hc, add_eq_right]
  exact matrixKL_eq_zero_iff P _ hP
    (fun i j => mul_pos (mul_pos (hu i) (hK i j)) (hv j))

theorem diagonal_scaling_unique (K : TransportPlan I J)
    (u u' : I → ℝ) (v v' : J → ℝ)
    (hK : ∀ i j, 0 < K i j)
    (hu : ∀ i, 0 < u i) (hu' : ∀ i, 0 < u' i)
    (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j)
    (hr : ∀ i, rowMass (fun i j => u i * K i j * v j) i =
      rowMass (fun i j => u' i * K i j * v' j) i)
    (hc : ∀ j, colMass (fun i j => u i * K i j * v j) j =
      colMass (fun i j => u' i * K i j * v' j) j) :
    (fun i j => u i * K i j * v j) = (fun i j => u' i * K i j * v' j) := by
  have hpos : ∀ i j, 0 < u i * K i j * v j :=
    fun i j => mul_pos (mul_pos (hu i) (hK i j)) (hv j)
  have hpos' : ∀ i j, 0 < u' i * K i j * v' j :=
    fun i j => mul_pos (mul_pos (hu' i) (hK i j)) (hv' j)
  apply (matrixKL_scaling_eq_iff _ K u' v' (fun i j => (hpos i j).le)
    hK hu' hv' hr hc).1
  exact le_antisymm
    (matrixKL_scaling_minimizes _ K u v (fun i j => (hpos' i j).le)
      hK hu hv (fun i => (hr i).symm) (fun j => (hc j).symm))
    (matrixKL_scaling_minimizes _ K u' v' (fun i j => (hpos i j).le)
      hK hu' hv' hr hc)

end InfoGeometry.Physics.AmariSinkhornAlternatingProjections
