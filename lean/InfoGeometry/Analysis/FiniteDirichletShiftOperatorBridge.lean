import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Finite logarithmic translation operators

This is the bounded algebraic shadow of the logarithmic-scale translation
operator used in spectral-operator constructions.  It proves only the shift
semigroup law and the readout on exponential test functions; no unbounded
operator, functional calculus, spectrum, or zeta statement is made.
-/

noncomputable section

namespace InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

open scoped BigOperators

abbrev ScaleFunctions := ℝ → ℂ
abbrev ScaleEnd := ScaleFunctions →ₗ[ℂ] ScaleFunctions

/-- Translation by a logarithmic scale increment. -/
def translationShift (u : ℝ) : ScaleEnd where
  toFun f t := f (t - u)
  map_add' f g := by
    ext t
    simp
  map_smul' c f := by
    ext t
    simp

@[simp] theorem translationShift_apply (u : ℝ) (f : ScaleFunctions) (t : ℝ) :
    translationShift u f t = f (t - u) := rfl

theorem translationShift_zero : translationShift 0 = 1 := by
  ext f t
  simp [translationShift]

theorem translationShift_add (u v : ℝ) :
    translationShift u * translationShift v = translationShift (u + v) := by
  ext f t
  simp [translationShift, sub_eq_add_neg, add_assoc, add_comm]

/-- Exponential test family in logarithmic coordinates. -/
def exponentialTest (s : ℂ) : ScaleFunctions :=
  fun t => Complex.exp (s * (t : ℂ))

theorem translationShift_exponentialTest (s : ℂ) (u t : ℝ) :
    translationShift u (exponentialTest s) t =
      Complex.exp (-s * (u : ℂ)) * exponentialTest s t := by
  rw [translationShift_apply]
  unfold exponentialTest
  rw [show s * ((t - u : ℝ) : ℂ) = (-s * (u : ℂ)) + s * (t : ℂ) by
    push_cast
    ring]
  rw [Complex.exp_add]

/-- The finite Dirichlet shift operator, indexed by `1 ≤ n ≤ N + 1`. -/
def finiteDirichletShift (N : ℕ) : ScaleEnd :=
  Finset.sum (Finset.range (N + 1))
    (fun n => translationShift (Real.log (Nat.succ n : ℕ)))

theorem finiteDirichletShift_apply (N : ℕ) (f : ScaleFunctions) (t : ℝ) :
    finiteDirichletShift N f t =
      Finset.sum (Finset.range (N + 1))
        (fun n => translationShift (Real.log (Nat.succ n : ℕ)) f t) := by
  simp [finiteDirichletShift]

theorem finiteDirichletShift_exponentialTest (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteDirichletShift N (exponentialTest s) t =
      Finset.sum (Finset.range (N + 1))
        (fun n => Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ))) *
        exponentialTest s t := by
  rw [finiteDirichletShift_apply]
  simp_rw [translationShift_exponentialTest]
  rw [Finset.sum_mul]

/-- The finite Möbius-weighted logarithmic shift operator. -/
def finiteMobiusShift (N : ℕ) : ScaleEnd :=
  Finset.sum (Finset.range (N + 1))
    (fun n =>
      ((ArithmeticFunction.moebius (Nat.succ n) : ℤ) : ℂ) •
        translationShift (Real.log (Nat.succ n : ℕ)))

theorem finiteMobiusShift_exponentialTest (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteMobiusShift N (exponentialTest s) t =
      Finset.sum (Finset.range (N + 1))
        (fun n =>
          ((ArithmeticFunction.moebius (Nat.succ n) : ℤ) : ℂ) *
            Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ))) *
        exponentialTest s t := by
  unfold finiteMobiusShift
  change
    (Finset.sum (Finset.range (N + 1))
      (fun n =>
        ((ArithmeticFunction.moebius (Nat.succ n) : ℤ) : ℂ) •
          translationShift (Real.log (Nat.succ n : ℕ))))
      (exponentialTest s) t = _
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  change
    ((ArithmeticFunction.moebius (Nat.succ n) : ℤ) : ℂ) *
        translationShift (Real.log (Nat.succ n : ℕ)) (exponentialTest s) t =
      (((ArithmeticFunction.moebius (Nat.succ n) : ℤ) : ℂ) *
          Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ))) *
        exponentialTest s t
  rw [translationShift_exponentialTest]
  ring

/-- A finite Dirichlet operator with arbitrary complex coefficients. -/
def dirichletOperator (N : ℕ) (a : ℕ → ℂ) : ScaleEnd :=
  Finset.sum (Finset.range (N + 1))
    (fun n => a (Nat.succ n) • translationShift (Real.log (Nat.succ n : ℕ)))

theorem dirichletOperator_exponentialTest
    (N : ℕ) (a : ℕ → ℂ) (s : ℂ) (t : ℝ) :
    dirichletOperator N a (exponentialTest s) t =
      Finset.sum (Finset.range (N + 1))
        (fun n => a (Nat.succ n) *
          Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ))) *
        exponentialTest s t := by
  unfold dirichletOperator
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [translationShift_exponentialTest]
  ring

def zetaCoefficients : ℕ → ℂ := fun _ => 1

def mobiusCoefficients : ℕ → ℂ :=
  fun n => (ArithmeticFunction.moebius n : ℤ)

theorem finiteDirichletShift_eq_zetaCoefficients (N : ℕ) :
    finiteDirichletShift N = dirichletOperator N zetaCoefficients := by
  ext f t
  simp [finiteDirichletShift, dirichletOperator, zetaCoefficients]

theorem finiteMobiusShift_eq_mobiusCoefficients (N : ℕ) :
    finiteMobiusShift N = dirichletOperator N mobiusCoefficients := by
  ext f t
  simp [finiteMobiusShift, dirichletOperator, mobiusCoefficients]


end InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

end noncomputable section
