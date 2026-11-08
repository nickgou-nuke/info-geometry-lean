import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Fibonacci full twist and a rank-two Jordan monodromy

This is a finite matrix intertwining statement.  It does not identify a
Tomita--Takesaki flow or a KMS state.
-/

namespace InfoGeometry.Canonical

noncomputable section

open Matrix
open InfoGeometry.Canonical.YangBaxterProof
open InfoGeometry.Clifford.LogCftMonodromy

/-- Square-zero perturbations in an associative algebra. -/
def isJordanNilpotent {B : Type*} [MulZeroOneClass B] (N : B) : Prop :=
  N * N = 0

/-- A central scalar times a unipotent square-zero Jordan block. -/
def hadjiivanovMonodromyMatrix
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (lambda : R) (N : B) : B :=
  lambda • (1 + N)

/--
The binomial law for a central scalar and a square-zero perturbation.

The coefficient ring `R` is commutative and acts through an `Algebra R B`;
the carrier `B` itself may be noncommutative.  This is the precise generic
form of the logarithmic Jordan power law.
-/
theorem scalar_jordan_power
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (lambda : R) (N : B) (h_nil : isJordanNilpotent N) (n : ℕ) :
    hadjiivanovMonodromyMatrix lambda N ^ n =
      lambda ^ n • (1 + (n : R) • N) := by
  change (lambda • (1 + N)) ^ n =
    lambda ^ n • (1 + (n : R) • N)
  have hN : N * N = 0 := h_nil
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      have hmul :
          (1 + (n : R) • N) * (1 + N) =
            1 + ((n + 1 : ℕ) : R) • N := by
        simp only [add_mul, mul_add, one_mul, mul_one]
        simp [hN]
        module
      change (lambda ^ n • (1 + (n : R) • N)) *
        (lambda • (1 + N)) = _
      rw [mul_smul_comm, Algebra.smul_mul_assoc, hmul]
      simp only [smul_smul]
      congr 1
      rw [pow_succ]
      ring

theorem scalar_jordan_power_of_eq
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (lambda : R) (N : B) (h_nil : isJordanNilpotent N) (n : ℕ)
    (T : B) (hT : T = hadjiivanovMonodromyMatrix lambda N) :
    T ^ n = lambda ^ n • (1 + (n : R) • N) := by
  rw [hT]
  exact scalar_jordan_power lambda N h_nil n

def fullBraidTwist (R B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (R * B * R) * (R * B * R)

def hadjiivanovMonodromy (lambda : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  upperJordan lambda lambda

theorem hadjiivanovMonodromy_power (lambda : ℂ) (n : ℕ) :
    hadjiivanovMonodromy lambda ^ n =
      upperJordan (lambda ^ n) ((n : ℂ) * lambda ^ n) := by
  rw [show hadjiivanovMonodromy lambda = upperJordan lambda lambda by rfl]
  rw [upperJordan_pow]
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hsub : n - 1 + 1 = n := by omega
    have hpow : lambda ^ (n - 1) * lambda = lambda ^ n := by
      rw [← pow_succ, hsub]
    have hcoef : (n : ℂ) * lambda * lambda ^ (n - 1) =
        (n : ℂ) * lambda ^ n := by
      calc
        (n : ℂ) * lambda * lambda ^ (n - 1) =
            (n : ℂ) * (lambda ^ (n - 1) * lambda) := by ring
        _ = (n : ℂ) * lambda ^ n := by rw [hpow]
        _ = (n : ℂ) * lambda ^ n := by ring
    change upperJordan (lambda ^ n)
      ((n : ℂ) * lambda * lambda ^ (n - 1)) =
      upperJordan (lambda ^ n) ((n : ℂ) * lambda ^ n)
    congr 1

theorem fibonacci_hadjiivanov_intertwiner
    (lambda : ℂ)
    (h_twist : fullBraidTwist R B = hadjiivanovMonodromy lambda) :
    ∀ n : ℕ,
      fullBraidTwist R B ^ n =
        upperJordan (lambda ^ n) ((n : ℂ) * lambda ^ n) := by
  intro n
  rw [h_twist, hadjiivanovMonodromy_power]

/-! The same bridge stated with an explicit square-zero matrix datum. -/

def matrixJordanNilpotent (N : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  isJordanNilpotent N

def matrixHadjiivanovMonodromy
    (lambda : ℂ) (N : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  hadjiivanovMonodromyMatrix lambda N

theorem fibonacci_hadjiivanov_intertwiner_theorem
    (R B N : Matrix (Fin 2) (Fin 2) ℂ) (lambda : ℂ)
    (h_nil : matrixJordanNilpotent N)
    (h_twist : fullBraidTwist R B = matrixHadjiivanovMonodromy lambda N) :
    ∀ n : ℕ,
      fullBraidTwist R B ^ n =
        lambda ^ n • (1 + (n : ℂ) • N) := by
  intro n
  exact scalar_jordan_power_of_eq lambda N h_nil n
    (fullBraidTwist R B) h_twist

end
end InfoGeometry.Canonical
