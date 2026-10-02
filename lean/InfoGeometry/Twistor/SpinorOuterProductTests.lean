import InfoGeometry.Twistor.SpinorOuterProduct
import InfoGeometry.Twistor.SpinorOuterProductDependencies
import Mathlib.Analysis.RCLike.Basic

namespace InfoGeometry.Twistor.SpinorOuterProduct

open Matrix
open scoped ComplexOrder

example (left right : Fin 2 → ℂ) : (vecMulVec left (star right)).det = 0 :=
  Matrix.det_vecMulVec left (star right)

example (spinor : Fin 2 → ℂ) : (vecMulVec spinor (star spinor)).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star spinor

example (spinor : Fin 2 → ℂ) :
    vecMulVec (Complex.I • spinor) (star (Complex.I • spinor)) =
      vecMulVec spinor (star spinor) := by
  apply outer_phase_invariant
  simp

example :
    (vecMulVec (![1, 0] : Fin 2 → ℂ) (star ![1, 0]) +
      vecMulVec (![0, 1] : Fin 2 → ℂ) (star ![0, 1])).det = 1 := by
  rw [det_sum_self_outer]
  norm_num

example : ¬ (vecMulVec (![1, 0] : Fin 2 → ℂ) (star ![0, 1])).IsHermitian := by
  intro hermitian
  have entry := hermitian.apply 0 1
  norm_num [vecMulVec] at entry

example (left right : Fin 2 → ℂ) :
    (vecMulVec left (star left) + vecMulVec right (star right)).det = 0 ↔
      left 0 * right 1 = left 1 * right 0 :=
  det_sum_self_outer_eq_zero_iff left right

#print axioms bilinear_scaling
#print axioms hermitian_outer_scaling
#print axioms outer_phase_invariant
#print axioms self_outer_hermitian
#print axioms mixed_outer_hermitian_iff
#print axioms det_sum_self_outer
#print axioms det_sum_self_outer_eq_zero_iff
#print axioms complex_outer_scaling
#print axioms ProofDependency.no_cycle
#print axioms ProofDependency.nullity_and_phase_incomparable

end InfoGeometry.Twistor.SpinorOuterProduct
