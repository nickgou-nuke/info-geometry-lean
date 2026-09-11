import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.FiniteDirichletShiftOperator

/-!
# Finite Möbius shift operator

This is the finite Möbius-weighted companion of the Dirichlet shift operator.
It records the coefficient-level shadow of `1 / ζ(∂)` on exponential test
functions, without asserting an infinite inverse or any functional calculus.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.FiniteMobiusShiftOperator

open scoped BigOperators
open InfoGeometry.Arithmetic.FiniteDirichletShiftOperator

def finiteMobiusShift (N : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℂ) *
      logScaleTranslation (Real.log (n : ℝ)) f t

theorem finiteMobiusShift_exponentialTest (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteMobiusShift N (exponentialTest s) t =
      (∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius n : ℂ) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ))) *
        exponentialTest s t := by
  unfold finiteMobiusShift
  simp_rw [logScaleTranslation_exponentialTest]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The finite Möbius shift has the expected complex-power readout on the
exponential test family.  This is only a finite identity; it does not assert
an inverse for an infinite Dirichlet operator. -/
theorem finiteMobiusShift_exponentialTest_cpow (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteMobiusShift N (exponentialTest s) t =
      (∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
        exponentialTest s t := by
  rw [finiteMobiusShift_exponentialTest]
  apply congrArg (fun a : ℂ => a * exponentialTest s t)
  apply Finset.sum_congr rfl
  intro n hn
  have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn_pos)
  have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (le_of_lt hn_pos_real)).symm
  rw [hlog]
  ring_nf

/-- The finite Möbius shift commutes with log-scale time translations. -/
theorem finiteMobiusShift_comm_translation (N : ℕ) (h : ℝ) (f : ℝ → ℂ) :
    finiteMobiusShift N (logScaleTranslation h f) =
      logScaleTranslation h (finiteMobiusShift N f) := by
  ext t
  dsimp [finiteMobiusShift, logScaleTranslation]
  apply Finset.sum_congr rfl
  intro n hn
  have : t - Real.log (n : ℝ) - h = t - h - Real.log (n : ℝ) := by ring
  rw [this]

theorem finiteDirichletShift_smul_exponentialTest (N : ℕ) (c : ℂ) (s : ℂ) (t : ℝ) :
    finiteDirichletShift N (fun x => c * exponentialTest s x) t =
      c * (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) * exponentialTest s t := by
  dsimp [finiteDirichletShift, logScaleTranslation]
  simp_rw [exponentialTest]
  have hsum : (∑ n ∈ Finset.Icc 1 N, c * Complex.exp (s * ((t - Real.log (n : ℝ) : ℝ) : ℂ))) =
      c * (∑ n ∈ Finset.Icc 1 N, Complex.exp (s * ((t - Real.log (n : ℝ) : ℝ) : ℂ))) := by
    rw [Finset.mul_sum]
  rw [hsum]
  have hdir := finiteDirichletShift_exponentialTest_cpow N s t
  dsimp [finiteDirichletShift, logScaleTranslation, exponentialTest] at hdir
  rw [hdir]
  ring

theorem finiteMobiusShift_smul_exponentialTest (N : ℕ) (c : ℂ) (s : ℂ) (t : ℝ) :
    finiteMobiusShift N (fun x => c * exponentialTest s x) t =
      c * (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
        exponentialTest s t := by
  dsimp [finiteMobiusShift, logScaleTranslation]
  simp_rw [exponentialTest]
  have hsum : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) * (c * Complex.exp (s * ((t - Real.log (n : ℝ) : ℝ) : ℂ)))) =
      c * (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) * Complex.exp (s * ((t - Real.log (n : ℝ) : ℝ) : ℂ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hsum]
  have hmob := finiteMobiusShift_exponentialTest_cpow N s t
  dsimp [finiteMobiusShift, logScaleTranslation, exponentialTest] at hmob
  rw [hmob]
  ring

/-- Composition of Dirichlet and Möbius shifts on the exponential test family. -/
theorem finiteDirichlet_finiteMobius_exponentialTest (N M : ℕ) (s : ℂ) (t : ℝ) :
    finiteDirichletShift N (finiteMobiusShift M (exponentialTest s)) t =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) *
        (∑ m ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)) *
          exponentialTest s t := by
  have hmob_fn : finiteMobiusShift M (exponentialTest s) =
      fun x => (∑ m ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)) *
        exponentialTest s x := by
    ext x
    exact finiteMobiusShift_exponentialTest_cpow M s x
  rw [hmob_fn]
  rw [finiteDirichletShift_smul_exponentialTest]
  ring

theorem finiteMobius_finiteDirichlet_exponentialTest (M N : ℕ) (s : ℂ) (t : ℝ) :
    finiteMobiusShift M (finiteDirichletShift N (exponentialTest s)) t =
      (∑ m ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)) *
        (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) *
          exponentialTest s t := by
  have hdir_fn : finiteDirichletShift N (exponentialTest s) =
      fun x => (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) * exponentialTest s x := by
    ext x
    exact finiteDirichletShift_exponentialTest_cpow N s x
  rw [hdir_fn]
  rw [finiteMobiusShift_smul_exponentialTest]
  ring

/-- The Dirichlet and Möbius shifts commute on the exponential test family. -/
theorem finiteDirichlet_finiteMobius_commutes_on_exponentialTest (N M : ℕ) (s : ℂ) :
    finiteDirichletShift N (finiteMobiusShift M (exponentialTest s)) =
      finiteMobiusShift M (finiteDirichletShift N (exponentialTest s)) := by
  ext t
  rw [finiteDirichlet_finiteMobius_exponentialTest, finiteMobius_finiteDirichlet_exponentialTest]
  ring

end InfoGeometry.Arithmetic.FiniteMobiusShiftOperator
