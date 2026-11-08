import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CliffordNilpotentInterference

/-! Native specialization of the generic opposite-square nilpotence lemma. -/

namespace InfoGeometry.Clifford.Cl55NativeNilpotentInterference

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
open InfoGeometry.OperatorAlgebra.CliffordNilpotentInterference

/-- The native elliptic/split axis pair produces a square-zero sum. -/
theorem elliptic_split_axis_sum_sq_zero (i : Fin 5) :
    (ellipticAxis55 i + hyperbolicAxis55 i) *
        (ellipticAxis55 i + hyperbolicAxis55 i) = 0 := by
  have hanti : ellipticAxis55 i * hyperbolicAxis55 i =
      -(hyperbolicAxis55 i * ellipticAxis55 i) := by
    have h := hyperbolicAxis55_ellipticAxis55_anticommute i
    have h' : ellipticAxis55 i * hyperbolicAxis55 i +
        hyperbolicAxis55 i * ellipticAxis55 i = 0 := by
      simpa [add_comm] using h
    exact eq_neg_of_add_eq_zero_left h'
  exact add_sq_zero_of_opposite_squares
    (ellipticAxis55 i) (hyperbolicAxis55 i)
    (ellipticAxis55_sq i) (hyperbolicAxis55_sq i) hanti

/-- The opposite native axis combination is square-zero as well. -/
theorem elliptic_split_axis_sub_sq_zero (i : Fin 5) :
    (ellipticAxis55 i - hyperbolicAxis55 i) *
        (ellipticAxis55 i - hyperbolicAxis55 i) = 0 := by
  have hanti : ellipticAxis55 i * hyperbolicAxis55 i =
      -(hyperbolicAxis55 i * ellipticAxis55 i) := by
    have h := hyperbolicAxis55_ellipticAxis55_anticommute i
    have h' : ellipticAxis55 i * hyperbolicAxis55 i +
        hyperbolicAxis55 i * ellipticAxis55 i = 0 := by
      simpa [add_comm] using h
    exact eq_neg_of_add_eq_zero_left h'
  exact sub_sq_zero_of_opposite_squares
    (ellipticAxis55 i) (hyperbolicAxis55 i)
    (ellipticAxis55_sq i) (hyperbolicAxis55_sq i) hanti

end InfoGeometry.Clifford.Cl55NativeNilpotentInterference
