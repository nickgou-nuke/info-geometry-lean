import InfoGeometry.Exceptional.CyclotomicKreinG2

noncomputable section

namespace InfoGeometry.Chronometry.MatrixClock

open InfoGeometry.Exceptional.CyclotomicIntegerClock

def M_clock : Matrix (Fin 4) (Fin 4) ℝ :=
  ((Int.castRingHom ℝ).mapMatrix clock).transpose

theorem M_clock_entries :
    M_clock = !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 1, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [M_clock, clock]

theorem M_clock_annihilated_by_phi12 : M_clock ^ 4 - M_clock ^ 2 + 1 = 0 := by
  have mapped := congrArg ((Int.castRingHom ℝ).mapMatrix (m := Fin 4)) clock_quartic
  simp only [map_add, map_sub, map_pow, map_one, map_zero] at mapped
  have transposed := congrArg Matrix.transpose mapped
  simpa only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_pow,
    Matrix.transpose_one, Matrix.transpose_zero, M_clock] using transposed

theorem M_clock_half_period : M_clock ^ 6 = -1 :=
  pow_six_of_quartic M_clock M_clock_annihilated_by_phi12

theorem M_clock_order_12 : M_clock ^ 12 = 1 :=
  pow_twelve_of_quartic M_clock M_clock_annihilated_by_phi12

theorem M_clock_exact_order : orderOf M_clock = 12 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) M_clock_order_12
  intro prime prime_is_prime divides
  have bound : prime ≤ 12 := Nat.le_of_dvd (by decide) divides
  have possibilities : prime = 2 ∨ prime = 3 := by
    interval_cases prime <;> norm_num at *
  rcases possibilities with rfl | rfl
  · rw [show 12 / 2 = 6 by norm_num, M_clock_half_period]
    intro impossible
    have entry := congrArg (fun matrix : Matrix (Fin 4) (Fin 4) ℝ => matrix 0 0) impossible
    norm_num at entry
  · intro impossible
    have entry := congrArg (fun matrix : Matrix (Fin 4) (Fin 4) ℝ => matrix 0 2) impossible
    rw [M_clock_entries] at entry
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] at entry
    change (1 : ℝ) = 0 at entry
    norm_num at entry

theorem trace_one_half_period (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (determinant : matrix.det = 1) (trace : Matrix.trace matrix = 1) :
    matrix ^ 3 = -1 := by
  have determinant_entries : matrix 0 0 * matrix 1 1 - matrix 0 1 * matrix 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using determinant
  have trace_entries : matrix 0 0 + matrix 1 1 = 1 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using trace
  have diagonal : matrix 1 1 = 1 - matrix 0 0 := by linarith
  rw [diagonal] at determinant_entries
  have quadratic : matrix ^ 2 - matrix + 1 = 0 := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, diagonal] <;> nlinarith
  have factorization : (matrix ^ 2 - matrix + 1) * (matrix + 1) = matrix ^ 3 + 1 := by
    noncomm_ring
  apply eq_neg_of_add_eq_zero_left
  rw [← factorization, quadratic, zero_mul]

theorem trace_one_period_six (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (determinant : matrix.det = 1) (trace : Matrix.trace matrix = 1) :
    matrix ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by norm_num, pow_mul, trace_one_half_period matrix determinant trace]
  simp

theorem trace_one_not_order_twelve (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (determinant : matrix.det = 1) (trace : Matrix.trace matrix = 1) :
    orderOf matrix ≠ 12 := by
  intro exact_order
  have divides := orderOf_dvd_of_pow_eq_one (trace_one_period_six matrix determinant trace)
  rw [exact_order] at divides
  norm_num at divides

end InfoGeometry.Chronometry.MatrixClock
