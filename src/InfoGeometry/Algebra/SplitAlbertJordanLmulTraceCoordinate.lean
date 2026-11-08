import InfoGeometry.Algebra.SplitAlbertDerivationOperatorTrace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.H3ZornCarrierBasis
import Mathlib.LinearAlgebra.Trace

namespace InfoGeometry.Algebra

open H3Zorn

/-!
This owner records the coordinate form of the remaining scalar/operator-trace
frontier.  The basis reduction is proved here without asserting the desired
27-dimensional evaluation by fiat; the final finite coordinate calculation is
left as the next local theorem target.
-/

theorem h3Zorn_jordanLmul_operatorTrace_eq_basis_sum (x : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul (R := ℝ) x) =
      ∑ i : Fin 27,
        (LinearMap.toMatrix h3ZornBasis h3ZornBasis
          (jordanLmul (R := ℝ) x)) i i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ h3ZornBasis]
  rfl

theorem h3Zorn_jordanLmul_operatorTrace_eq_coordinate_sum (x : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul (R := ℝ) x) =
      ∑ i : Fin 27,
        (LinearMap.toMatrix h3ZornBasis h3ZornBasis
          (jordanLmul (R := ℝ) x)) i i :=
  h3Zorn_jordanLmul_operatorTrace_eq_basis_sum x

theorem h3Zorn_linearTrace_jordanMul (x y : H3Zorn ℝ) :
    linearTrace (x * y) = traceBilin x y := by
  change linearTrace (candidateJordanMul x y) = traceBilin x y
  rw [candidateJordanMul_trace_formula]
  simp only [linearTrace_add, linearTrace_smul, sub_eq_add_neg,
    neg_smul, traceBilin_one]
  rw [linearTrace_crossProduct]
  have h1 : linearTrace (1 : H3Zorn ℝ) = 3 := by
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  have hneg (z : H3Zorn ℝ) : linearTrace (-z) = -linearTrace z := by
    rw [show -z = (-1 : ℝ) • z by module, linearTrace_smul]
    ring
  simp only [linearTrace_add, linearTrace_smul, sub_eq_add_neg, hneg, h1]
  ring

end InfoGeometry.Algebra
