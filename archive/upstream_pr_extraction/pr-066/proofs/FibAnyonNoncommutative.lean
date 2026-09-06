import Mathlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace FibAnyonNoncommutative

structure FibonacciFusionOperator
(R A : Type*)
[CommSemiring R]
[AddCommMonoid A]
[Module R A] where
  tauEnd : Module.End R A
  fusion :
    tauEnd * tauEnd = 1 + tauEnd

variable {R A : Type*}
variable [CommSemiring R] [AddCommMonoid A] [Module R A]

lemma fusion_reduction
  (F : FibonacciFusionOperator R A) (n : ℕ) :
  F.tauEnd ^ (n + 2) = F.tauEnd ^ (n + 1) + F.tauEnd ^ n := by
  have h := F.fusion
  calc
    F.tauEnd ^ (n + 2) = F.tauEnd ^ n * F.tauEnd ^ 2 := by rw [pow_add]
    _ = F.tauEnd ^ n * (F.tauEnd * F.tauEnd) := by rw [pow_two]
    _ = F.tauEnd ^ n * (1 + F.tauEnd) := by rw [h]
    _ = F.tauEnd ^ n * 1 + F.tauEnd ^ n * F.tauEnd := by rw [mul_add]
    _ = F.tauEnd ^ n + F.tauEnd ^ (n + 1) := by simp only [mul_one, pow_add, pow_one]
    _ = F.tauEnd ^ (n + 1) + F.tauEnd ^ n := by rw [add_comm]

lemma fusion_normal_form
  (F : FibonacciFusionOperator R A) (n : ℕ) :
  F.tauEnd ^ (n + 1) =
  (Nat.fib n : Module.End R A) + (Nat.fib (n + 1) : Module.End R A) * F.tauEnd := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    calc
      F.tauEnd ^ (n + 2) = F.tauEnd ^ (n + 1) * F.tauEnd := by rw [pow_succ]
      _ = ((Nat.fib n : Module.End R A) + (Nat.fib (n + 1) : Module.End R A) * F.tauEnd) * F.tauEnd := by rw [ih]
      _ = (Nat.fib n : Module.End R A) * F.tauEnd + (Nat.fib (n + 1) : Module.End R A) * (F.tauEnd * F.tauEnd) := by
        rw [add_mul, mul_assoc]
      _ = (Nat.fib n : Module.End R A) * F.tauEnd + (Nat.fib (n + 1) : Module.End R A) * (1 + F.tauEnd) := by
        rw [F.fusion]
      _ = (Nat.fib n : Module.End R A) * F.tauEnd + ((Nat.fib (n + 1) : Module.End R A) + (Nat.fib (n + 1) : Module.End R A) * F.tauEnd) := by
        rw [mul_add, mul_one]
      _ = (Nat.fib (n + 1) : Module.End R A) + ((Nat.fib (n + 1) : Module.End R A) * F.tauEnd + (Nat.fib n : Module.End R A) * F.tauEnd) := by
        simp only [add_comm, add_left_comm]
      _ = (Nat.fib (n + 1) : Module.End R A) + ((Nat.fib (n + 1) : Module.End R A) + (Nat.fib n : Module.End R A)) * F.tauEnd := by
        rw [add_mul]
      _ = (Nat.fib (n + 1) : Module.End R A) + (Nat.fib (n + 2) : Module.End R A) * F.tauEnd := by
        rw [← Nat.cast_add, Nat.fib_add_two, add_comm (Nat.fib n) (Nat.fib (n + 1))]

open Polynomial

lemma fusion_aeval_eq
  (F : FibonacciFusionOperator R A) :
  aeval F.tauEnd (X ^ 2 : R[X]) = aeval F.tauEnd (X + 1 : R[X]) := by
  simp only [map_pow, aeval_X, map_add, aeval_one]
  rw [pow_two, add_comm, F.fusion]

section Ring
variable {R_ring A_group : Type*} [CommRing R_ring] [AddCommGroup A_group] [Module R_ring A_group]

lemma fusion_polynomial_ideal
  (F : FibonacciFusionOperator R_ring A_group) :
  aeval F.tauEnd (X ^ 2 - X - 1 : R_ring[X]) = 0 := by
  simp only [map_sub, map_pow, aeval_X, aeval_one]
  have h := F.fusion
  calc
    F.tauEnd ^ 2 - F.tauEnd - 1 = F.tauEnd * F.tauEnd - F.tauEnd - 1 := by rw [pow_two]
    _ = (1 + F.tauEnd) - F.tauEnd - 1 := by rw [h]
    _ = 1 + F.tauEnd - F.tauEnd - 1 := rfl
    _ = 0 := by abel

end Ring

end FibAnyonNoncommutative
