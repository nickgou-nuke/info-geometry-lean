/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteFockSignedBasisActions
import InfoGeometry.Clifford.FiniteRealFockMetric

/-!
# Real coordinate creation/contraction adjointness

Uses the existing real carrier and locally activated induced metric.
-/
noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

/-- The real inner coefficient of a signed exterior basis vector. -/
theorem fock_signed_basis_inner_left (n : ℕ) (s : ℤˣ) (S T : Finset (Fin n)) :
    inner ℝ (s • (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S)
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra T) =
    ((s : ℤ) : ℝ) * (if S = T then 1 else 0) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ,
    real_inner_smul_left, fock_exteriorBasis_inner]

/-- The same real sign appears when the signed vector is in the second slot. -/
theorem fock_signed_basis_inner_right (n : ℕ) (s : ℤˣ) (S T : Finset (Fin n)) :
    inner ℝ ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S)
      (s • (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra T) =
    ((s : ℤ) : ℝ) * (if S = T then 1 else 0) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ,
    real_inner_smul_right, fock_exteriorBasis_inner]

/-- Coordinate creation and native left contraction have matching basis coefficients. -/
theorem fock_extAction_intAction_inner_basis (n : ℕ) (i : Fin n)
    (S T : Finset (Fin n)) :
    inner ℝ (extAction ((Pi.basisFun ℝ (Fin n)) i)
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S))
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra T) =
    inner ℝ ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S)
      (intAction (LinearMap.proj i : Module.Dual ℝ (Vector n))
        ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra T)) := by
  by_cases hS : i ∈ S
  · rw [fock_extAction_basis_of_mem n i S hS, inner_zero_left]
    by_cases hT : i ∈ T
    · rw [fock_intAction_basis_erase n i T hT, fock_signed_basis_inner_right]
      have hne : S ≠ T.erase i := by
        intro h
        apply Finset.notMem_erase i T
        rw [← h]
        exact hS
      simp only [hne, ite_false, mul_zero]
    · rw [fock_intAction_basis_of_not_mem n i T hT, inner_zero_right]
  · rw [fock_extAction_basis_insert n i S hS, fock_signed_basis_inner_left]
    by_cases hT : i ∈ T
    · rw [fock_intAction_basis_erase n i T hT, fock_signed_basis_inner_right]
      by_cases hST : S = T.erase i
      · subst S
        simp only [Finset.insert_erase hT, ite_true, mul_one]
      · have hins : insert i S ≠ T := by
          intro h
          apply hST
          simpa [hS] using congrArg (fun U : Finset (Fin n) => U.erase i) h
        simp only [hins, hST, ite_false, mul_zero]
    · rw [fock_intAction_basis_of_not_mem n i T hT, inner_zero_right]
      have hins : insert i S ≠ T := by
        intro h
        exact hT (h ▸ Finset.mem_insert_self i S)
      simp only [hins, ite_false, mul_zero]

/-- Coordinate creation is adjoint to coordinate contraction for the actual
induced finite real Fock metric, expressed directly as the inner-product identity. -/
theorem fock_extAction_intAction_inner (n : ℕ) (i : Fin n)
    (x y : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    inner ℝ (extAction ((Pi.basisFun ℝ (Fin n)) i) x) y =
      inner ℝ x (intAction (LinearMap.proj i : Module.Dual ℝ (Vector n)) y) := by
  let b := (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [b, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, fock_extAction_intAction_inner_basis]

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
