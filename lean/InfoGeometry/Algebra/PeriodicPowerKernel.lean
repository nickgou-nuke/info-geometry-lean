import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic periodic-power kernel

This owner records only the semigroup consequence of a periodic power
relation. Fourier, Mellin, Laplace, and KAN readouts remain separate.
-/

namespace InfoGeometry.Algebra.PeriodicPowerKernel

variable {A : Type*} [Monoid A]

structure Datum where
  element : A
  exponent : ℕ
  periodic : element ^ exponent = element

theorem power_shift (D : Datum (A := A)) (k : ℕ) :
    D.element ^ (D.exponent + k) = D.element ^ (k + 1) := by
  rw [pow_add, D.periodic, pow_succ]
  exact (Commute.self_pow D.element k).eq

theorem power_shift_left (D : Datum (A := A)) (k : ℕ) :
    D.element ^ (k + D.exponent) = D.element ^ (k + 1) := by
  rw [Nat.add_comm k D.exponent]
  exact power_shift D k

end InfoGeometry.Algebra.PeriodicPowerKernel
