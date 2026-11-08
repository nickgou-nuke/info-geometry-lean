/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities

/-!
# Ordered products and inner action of two square-zero matrices

The two matrices are independently square-zero. Their symmetric product is
retained as a matrix coefficient throughout; no inverse relation or scalar
normalization is assumed. Commutation conclusions concern the displayed
generated elements, not the whole matrix algebra.
-/

namespace InfoGeometry.OperatorAlgebra.MatrixSquareZeroPairs

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {U V : Matrix n n ℂ}

/-- The ordered difference-sum product recovers the native commutator. -/
theorem sub_mul_add_eq_lie (hU : U * U = 0) (hV : V * V = 0) :
    (U - V) * (U + V) = ⁅U, V⁆ := by
  change (U - V) * (U + V) = U * V - V * U
  noncomm_ring [hU, hV]

/-- Reversing that ordered product reverses its sign. -/
theorem add_mul_sub_eq_neg_lie (hU : U * U = 0) (hV : V * V = 0) :
    (U + V) * (U - V) = -⁅U, V⁆ := by
  change (U + V) * (U - V) = -(U * V - V * U)
  noncomm_ring [hU, hV]

/-- The symmetric product commutes with the sum of the two generators. -/
theorem commute_jordan_add (hU : U * U = 0) (hV : V * V = 0) :
    Commute (U * V + V * U) (U + V) := by
  have hsq : (U + V) * (U + V) = U * V + V * U := by
    noncomm_ring [hU, hV]
  change (U * V + V * U) * (U + V) = (U + V) * (U * V + V * U)
  simpa only [hsq] using mul_assoc (U + V) (U + V) (U + V)

/-- The symmetric product also commutes with the difference. -/
theorem commute_jordan_sub (hU : U * U = 0) (hV : V * V = 0) :
    Commute (U * V + V * U) (U - V) := by
  have hsq : (U - V) * (U - V) = -(U * V + V * U) := by
    noncomm_ring [hU, hV]
  have h := mul_assoc (U - V) (U - V) (U - V)
  simp only [hsq, neg_mul, mul_neg] at h
  change (U * V + V * U) * (U - V) = (U - V) * (U * V + V * U)
  exact neg_inj.mp h

/-- Closure under ordered multiplication gives commutation with the commutator. -/
theorem commute_jordan_lie (hU : U * U = 0) (hV : V * V = 0) :
    Commute (U * V + V * U) ⁅U, V⁆ := by
  rw [← sub_mul_add_eq_lie hU hV]
  exact (commute_jordan_sub hU hV).mul_right (commute_jordan_add hU hV)

/-- Left multiplication by the commutator exchanges sum and difference with
the full symmetric matrix product as coefficient. -/
theorem lie_mul_add_eq_jordan_mul_sub (hU : U * U = 0) (hV : V * V = 0) :
    ⁅U, V⁆ * (U + V) = (U * V + V * U) * (U - V) := by
  have hsq : (U + V) * (U + V) = U * V + V * U := by
    noncomm_ring [hU, hV]
  calc
    ⁅U, V⁆ * (U + V) = ((U - V) * (U + V)) * (U + V) := by
      rw [sub_mul_add_eq_lie hU hV]
    _ = (U - V) * ((U + V) * (U + V)) := mul_assoc _ _ _
    _ = (U - V) * (U * V + V * U) := by rw [hsq]
    _ = (U * V + V * U) * (U - V) := (commute_jordan_sub hU hV).eq.symm

/-- Right multiplication has the opposite sign on the sum. -/
theorem add_mul_lie_eq_neg_jordan_mul_sub (hU : U * U = 0) (hV : V * V = 0) :
    (U + V) * ⁅U, V⁆ = -((U * V + V * U) * (U - V)) := by
  calc
    (U + V) * ⁅U, V⁆ = (U + V) * ((U - V) * (U + V)) := by
      rw [sub_mul_add_eq_lie hU hV]
    _ = ((U + V) * (U - V)) * (U + V) := (mul_assoc _ _ _).symm
    _ = -(⁅U, V⁆ * (U + V)) := by
      rw [add_mul_sub_eq_neg_lie hU hV, neg_mul]
    _ = -((U * V + V * U) * (U - V)) := by
      rw [lie_mul_add_eq_jordan_mul_sub hU hV]

/-- Left multiplication exchanges the difference back into the sum. -/
theorem lie_mul_sub_eq_jordan_mul_add (hU : U * U = 0) (hV : V * V = 0) :
    ⁅U, V⁆ * (U - V) = (U * V + V * U) * (U + V) := by
  have hsq : (U - V) * (U - V) = -(U * V + V * U) := by
    noncomm_ring [hU, hV]
  calc
    ⁅U, V⁆ * (U - V) = -(((U + V) * (U - V)) * (U - V)) := by
      rw [add_mul_sub_eq_neg_lie hU hV, neg_mul, neg_neg]
    _ = -((U + V) * ((U - V) * (U - V))) := by rw [mul_assoc]
    _ = (U + V) * (U * V + V * U) := by rw [hsq, mul_neg, neg_neg]
    _ = (U * V + V * U) * (U + V) := (commute_jordan_add hU hV).eq.symm

/-- Right multiplication has the opposite sign on the difference. -/
theorem sub_mul_lie_eq_neg_jordan_mul_add (hU : U * U = 0) (hV : V * V = 0) :
    (U - V) * ⁅U, V⁆ = -((U * V + V * U) * (U + V)) := by
  have hsq : (U - V) * (U - V) = -(U * V + V * U) := by
    noncomm_ring [hU, hV]
  calc
    (U - V) * ⁅U, V⁆ = (U - V) * ((U - V) * (U + V)) := by
      rw [sub_mul_add_eq_lie hU hV]
    _ = ((U - V) * (U - V)) * (U + V) := (mul_assoc _ _ _).symm
    _ = -((U * V + V * U) * (U + V)) := by rw [hsq, neg_mul]

/-- The commutator square equals the square of the symmetric product. -/
theorem lie_mul_lie_eq_jordan_mul_jordan (hU : U * U = 0) (hV : V * V = 0) :
    ⁅U, V⁆ * ⁅U, V⁆ = (U * V + V * U) * (U * V + V * U) := by
  have hsq : (U + V) * (U + V) = U * V + V * U := by
    noncomm_ring [hU, hV]
  calc
    ⁅U, V⁆ * ⁅U, V⁆ = ⁅U, V⁆ * ((U - V) * (U + V)) := by
      rw [sub_mul_add_eq_lie hU hV]
    _ = (⁅U, V⁆ * (U - V)) * (U + V) := (mul_assoc _ _ _).symm
    _ = ((U * V + V * U) * (U + V)) * (U + V) := by
      rw [lie_mul_sub_eq_jordan_mul_add hU hV]
    _ = (U * V + V * U) * (U * V + V * U) := by rw [mul_assoc, hsq]

/-- Inner action on the sum retains twice the full symmetric matrix coefficient. -/
theorem lie_lie_add (hU : U * U = 0) (hV : V * V = 0) :
    ⁅⁅U, V⁆, U + V⁆ = (2 : ℂ) • ((U * V + V * U) * (U - V)) := by
  change ⁅U, V⁆ * (U + V) - (U + V) * ⁅U, V⁆ = _
  rw [lie_mul_add_eq_jordan_mul_sub hU hV,
    add_mul_lie_eq_neg_jordan_mul_sub hU hV, two_smul]
  abel

/-- Inner action on the difference exchanges it with the sum. -/
theorem lie_lie_sub (hU : U * U = 0) (hV : V * V = 0) :
    ⁅⁅U, V⁆, U - V⁆ = (2 : ℂ) • ((U * V + V * U) * (U + V)) := by
  change ⁅U, V⁆ * (U - V) - (U - V) * ⁅U, V⁆ = _
  rw [lie_mul_sub_eq_jordan_mul_add hU hV,
    sub_mul_lie_eq_neg_jordan_mul_add hU hV, two_smul]
  abel

/-- The iterated inner action on the sum has the squared matrix coefficient. -/
theorem lie_lie_lie_add (hU : U * U = 0) (hV : V * V = 0) :
    ⁅⁅U, V⁆, ⁅⁅U, V⁆, U + V⁆⁆ =
      (4 : ℂ) • ((U * V + V * U) * (U * V + V * U) * (U + V)) := by
  have hLQ : ⁅⁅U, V⁆, U * V + V * U⁆ = 0 := by
    change ⁅U, V⁆ * (U * V + V * U) - (U * V + V * U) * ⁅U, V⁆ = 0
    exact sub_eq_zero.mpr (commute_jordan_lie hU hV).eq.symm
  rw [lie_lie_add hU hV, lie_smul,
    InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities.lie_mul,
    hLQ, zero_mul, zero_add, lie_lie_sub hU hV]
  norm_num [mul_smul_comm, smul_smul, mul_assoc]

/-- The same squared coefficient governs the iterated action on the difference. -/
theorem lie_lie_lie_sub (hU : U * U = 0) (hV : V * V = 0) :
    ⁅⁅U, V⁆, ⁅⁅U, V⁆, U - V⁆⁆ =
      (4 : ℂ) • ((U * V + V * U) * (U * V + V * U) * (U - V)) := by
  have hLQ : ⁅⁅U, V⁆, U * V + V * U⁆ = 0 := by
    change ⁅U, V⁆ * (U * V + V * U) - (U * V + V * U) * ⁅U, V⁆ = 0
    exact sub_eq_zero.mpr (commute_jordan_lie hU hV).eq.symm
  rw [lie_lie_sub hU hV, lie_smul,
    InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities.lie_mul,
    hLQ, zero_mul, zero_add, lie_lie_add hU hV]
  norm_num [mul_smul_comm, smul_smul, mul_assoc]

end InfoGeometry.OperatorAlgebra.MatrixSquareZeroPairs
