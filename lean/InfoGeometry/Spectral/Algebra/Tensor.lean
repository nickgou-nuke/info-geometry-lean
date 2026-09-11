import Mathlib.LinearAlgebra.TensorProduct.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Tensor products for the spectral algebra port

This is the Lean 4 replacement for the old group/module tensor interface.  It
reuses Mathlib's universal tensor product rather than introducing a second
quotient carrier.
-/

namespace InfoGeometry.Spectral.Algebra.Tensor

open TensorProduct

universe u v w

variable (R : Type u) (M : Type v) (N : Type w)
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

abbrev Carrier := TensorProduct R M N

@[simp]
theorem pure_add (m₁ m₂ : M) (n : N) :
    (tmul R (m₁ + m₂) n : Carrier R M N) = tmul R m₁ n + tmul R m₂ n := by
  rw [TensorProduct.add_tmul]

@[simp]
theorem pure_smul (r : R) (m : M) (n : N) :
    (tmul R (r • m) n : Carrier R M N) = (r • (tmul R m n)) := by
  exact (TensorProduct.smul_tmul' r m n).symm

@[simp]
theorem pure_add_right (m : M) (n₁ n₂ : N) :
    (tmul R m (n₁ + n₂) : Carrier R M N) = tmul R m n₁ + tmul R m n₂ := by
  rw [TensorProduct.tmul_add]

@[simp]
theorem pure_smul_right (r : R) (m : M) (n : N) :
    (tmul R m (r • n) : Carrier R M N) = (r • (tmul R m n)) := by
  exact TensorProduct.tmul_smul r m n

theorem induction_on {P : Carrier R M N → Prop}
    (h_add : ∀ x y, P x → P y → P (x + y))
    (h_zero : P 0)
    (h_pure : ∀ m n, P (tmul R m n)) :
    ∀ x : Carrier R M N, P x := by
  intro x
  induction x using TensorProduct.induction_on with
  | add x y hx hy => exact h_add x y hx hy
  | tmul m n => exact h_pure m n
  | zero => exact h_zero

end InfoGeometry.Spectral.Algebra.Tensor
