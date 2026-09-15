import InfoGeometry.Chronometry.MatrixClock

open InfoGeometry.Chronometry.MatrixClock

example : orderOf M_clock = 12 ∧ M_clock ^ 6 = -1 ∧ M_clock ^ 12 = 1 :=
  ⟨M_clock_exact_order, M_clock_half_period, M_clock_order_12⟩

example (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (determinant : matrix.det = 1) (trace : Matrix.trace matrix = 1) :
    matrix ^ 6 = 1 ∧ orderOf matrix ≠ 12 :=
  ⟨trace_one_period_six matrix determinant trace,
    trace_one_not_order_twelve matrix determinant trace⟩

#print axioms M_clock_entries
#print axioms M_clock_annihilated_by_phi12
#print axioms M_clock_half_period
#print axioms M_clock_order_12
#print axioms M_clock_exact_order
#print axioms trace_one_half_period
#print axioms trace_one_period_six
#print axioms trace_one_not_order_twelve
