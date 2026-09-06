import proofs.SO55RationalDiagonalization

/-! # Congruence from the hyperbolic metric to the diagonal `(5,5)` metric -/

noncomputable section
set_option maxHeartbeats 1500000
namespace SO55MetricCongruence

open SplitOctonionTKK55
open SplitOctonionTKK55Blocks
open HIndexFin10Reindex
open SO55RationalDiagonalization

/-- Reindexing places the hyperbolic endpoint pair in coordinates `0,9` and
leaves the diagonal `(4,4)` middle block in coordinates `1,...,8`. -/
theorem hyperbolicMetric10_eq_sparse :
    hyperbolicMetric10 = hyperbolicMetricSparse := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperbolicMetric10, reindexHMatrix, fin10ToHIndex,
      metric55, hyperbolicMetricSparse, eta55, Matrix.single] <;>
    simp_all +decide

/-- The first half of the congruence calculation.  Naming this sparse
intermediate avoids nested finite sums in the kernel proof. -/
def metricTimesBasis : M10 :=
  eta55 + Matrix.single 0 0 (-1 / 2 : ℝ) +
    Matrix.single 0 9 (-1 / 2 : ℝ) + Matrix.single 9 0 1 +
    Matrix.single 9 9 2

theorem hyperbolicMetricSparse_mul_basisChange :
    hyperbolicMetricSparse * basisChange = metricTimesBasis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisChange, hyperbolicMetricSparse, metricTimesBasis,
      eta55, Matrix.single, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    simp_all +decide <;> norm_num

theorem basisChange_transpose_mul_metricTimesBasis :
    basisChange.transpose * metricTimesBasis = eta55 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisChange, metricTimesBasis, eta55, Matrix.single,
      Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    simp_all +decide <;> norm_num

/-- The rational endpoint basis change diagonalizes the hyperbolic plane and
produces the standard diagonal metric of signature `(5,5)`. -/
theorem basisChange_metric_congruence :
    basisChange.transpose * hyperbolicMetric10 * basisChange = eta55 := by
  rw [hyperbolicMetric10_eq_sparse]
  rw [Matrix.mul_assoc, hyperbolicMetricSparse_mul_basisChange,
    basisChange_transpose_mul_metricTimesBasis]

end SO55MetricCongruence
end noncomputable section
