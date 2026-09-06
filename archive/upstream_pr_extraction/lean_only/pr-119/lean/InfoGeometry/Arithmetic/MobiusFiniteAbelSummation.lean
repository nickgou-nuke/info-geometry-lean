import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import InfoGeometry.Arithmetic.MobiusMertensRHEquivalence

/-!
# Finite Abel summation

This owner is purely finite.  It proves summation by parts for a sequence and
its finite prefix sums, then specializes the result to the arithmetic Möbius
function.  No limiting, asymptotic, or Riemann-hypothesis statement is used.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.MobiusFiniteAbelSummation

def prefixSum {R : Type*} [AddCommMonoid R]
    (a : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), a k

theorem finite_summation_by_parts {R : Type*} [CommRing R]
    (a f : ℕ → R) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n * f n) =
      prefixSum a N * f N +
        ∑ n ∈ Finset.range N, prefixSum a n * (f n - f (n + 1)) := by
  induction N with
  | zero =>
      simp [prefixSum]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : prefixSum a (N + 1) = prefixSum a N + a (N + 1) := by
        unfold prefixSum
        rw [Finset.sum_range_succ]
      rw [hp, Finset.sum_range_succ]
      ring

theorem mobius_sum_eq_mertens_summation_by_parts
    (f : ℕ → ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
        (ArithmeticFunction.moebius n : ℤ) * f n) =
      (MobiusMertensRHEquivalence.mertensFunction N) * f N +
        ∑ n ∈ Finset.range N,
          (MobiusMertensRHEquivalence.mertensFunction n) *
            (f n - f (n + 1)) := by
  simpa [prefixSum,
    MobiusMertensRHEquivalence.mertensFunction] using
    (finite_summation_by_parts
      (a := fun n => (ArithmeticFunction.moebius n : ℤ)) f N)

theorem mobius_sum_eq_mertens_summation_by_parts_complex
    (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
        (ArithmeticFunction.moebius n : ℂ) * f n) =
      (MobiusMertensRHEquivalence.mertensFunction N : ℂ) * f N +
        ∑ n ∈ Finset.range N,
          (MobiusMertensRHEquivalence.mertensFunction n : ℂ) *
            (f n - f (n + 1)) := by
  have h := finite_summation_by_parts
    (R := ℂ) (a := fun n => (ArithmeticFunction.moebius n : ℂ)) f N
  simpa [prefixSum, MobiusMertensRHEquivalence.mertensFunction] using h

theorem mobius_sum_range_eq_Icc_complex (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
        (ArithmeticFunction.moebius n : ℂ) * f n) =
      ∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius n : ℂ) * f n := by
  have hzero : (ArithmeticFunction.moebius 0 : ℂ) * f 0 = 0 := by
    simp
  have herase := Finset.sum_erase
    (s := Finset.range (N + 1))
    (f := fun n => (ArithmeticFunction.moebius n : ℂ) * f n)
    (a := 0) hzero
  have hset : (Finset.range (N + 1)).erase 0 = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc,
      Nat.lt_succ_iff]
    omega
  rw [← hset, ← herase]

end InfoGeometry.Arithmetic.MobiusFiniteAbelSummation
