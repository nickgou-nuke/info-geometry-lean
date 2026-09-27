import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.Algebra.Basic

variable (R : Type*) [CommRing R]
variable (V : Type*) [AddCommGroup V] [Module R V]

open ExteriorAlgebra

/-- A derivation of a possibly non-commutative R-algebra A. -/
structure Derivation (R A : Type*) [CommRing R] [Ring A] [Algebra R A] extends A →ₗ[R] A where
  leibniz' (a b : A) : toLinearMap (a * b) = a * toLinearMap b + toLinearMap a * b

def commutatorDerivation (B : ExteriorAlgebra R V) : Derivation R (ExteriorAlgebra R V) where
  toFun X := B * X - X * B
  map_add' X Y := by
    simp only [mul_add, add_mul]
    abel
  map_smul' r X := by
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub, RingHom.id_apply]
  leibniz' X Y := by
    calc
      B * (X * Y) - (X * Y) * B = B * X * Y - X * Y * B := by simp [mul_assoc]
      _ = X * (B * Y - Y * B) + (B * X - X * B) * Y := by
        simp only [mul_assoc, mul_sub, sub_mul]
        abel
