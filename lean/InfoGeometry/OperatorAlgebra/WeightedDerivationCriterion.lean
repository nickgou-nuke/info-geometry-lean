/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra

/-! # When left weighting preserves a noncommutative derivation

The exact condition is annihilation of the derivation's image by commutators.
A right-invertible value of the derivation makes centrality necessary as well
as sufficient. No commutativity of the ambient algebra is assumed.
-/

namespace InfoGeometry.OperatorAlgebra.ExteriorAlgebra.OpDerivation

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Exact Leibniz criterion for weighting by an element of the ambient algebra. -/
theorem left_weight_leibniz_iff (D : OpDerivation R A) (K : A) :
    (∀ x y, K * D (x * y) = (K * D x) * y + x * (K * D y)) ↔
      ∀ x y, (K * x - x * K) * D y = 0 := by
  have defect (x y : A) :
      K * D (x * y) - ((K * D x) * y + x * (K * D y)) =
        (K * x - x * K) * D y := by
    rw [D.leibniz]
    noncomm_ring
  constructor
  · intro h x y
    rw [← defect, h x y, sub_self]
  · intro h x y
    apply sub_eq_zero.mp
    rw [defect, h x y]

/-- A right-invertible value detects every commutator of the weight. -/
theorem left_weight_leibniz_iff_central (D : OpDerivation R A) (K y z : A)
    (hyz : D y * z = 1) :
    (∀ x w, K * D (x * w) = (K * D x) * w + x * (K * D w)) ↔
      ∀ x, Commute K x := by
  rw [left_weight_leibniz_iff]
  constructor
  · intro h x
    have hz := congrArg (fun a : A => a * z) (h x y)
    rw [mul_assoc, hyz, mul_one, zero_mul] at hz
    exact sub_eq_zero.mp hz
  · intro h x w
    rw [(h x).eq, sub_self, zero_mul]

/-- Bundle the weighted linear map using the exact image-annihilation condition. -/
def leftWeighted (D : OpDerivation R A) (K : A)
    (h : ∀ x y, (K * x - x * K) * D y = 0) : OpDerivation R A where
  toLinearMap :=
    { toFun := fun x => K * D x
      map_add' := by intro x y; rw [D.map_add, mul_add]
      map_smul' := by
        intro c x
        simp only [RingHom.id_apply, D.map_smul, Algebra.mul_smul_comm] }
  leibniz' := (left_weight_leibniz_iff D K).2 h

@[simp] theorem leftWeighted_apply (D : OpDerivation R A) (K : A)
    (h : ∀ x y, (K * x - x * K) * D y = 0) (x : A) :
    leftWeighted D K h x = K * D x := rfl

end InfoGeometry.OperatorAlgebra.ExteriorAlgebra.OpDerivation
