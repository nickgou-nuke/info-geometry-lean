import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative

/-!
# Finite split-Cartan action on chiral block supercharges

The diagonal matrix with entries `exp t` and `exp (-t)` acts by conjugation on
the existing off-diagonal `qPlus`/`qMinus` matrices.  This is a concrete
finite matrix action.  It is not identified here with a Banach-algebra
exponential or with native Clifford chirality.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralSplitCartanActionBridge

open InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative

abbrev Two := Fin 2

def splitCartanDiagonal {A : Type*} [Ring A] [Algebra ℝ A] (t : ℝ) :
    Matrix Two Two A :=
  !![algebraMap ℝ A (Real.exp t), 0;
     0, algebraMap ℝ A (Real.exp (-t))]

def splitCartanConjugation {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) (X : Matrix Two Two A) : Matrix Two Two A :=
  splitCartanDiagonal t * X * splitCartanDiagonal (-t)

private theorem algebraMap_exp_twice_mul
    {A : Type*} [Ring A] [Algebra ℝ A] (t : ℝ) (x : A) :
    algebraMap ℝ A (Real.exp t) * x * algebraMap ℝ A (Real.exp t) =
      algebraMap ℝ A (Real.exp (2 * t)) * x := by
  calc
    algebraMap ℝ A (Real.exp t) * x * algebraMap ℝ A (Real.exp t) =
        algebraMap ℝ A (Real.exp t) *
          (x * algebraMap ℝ A (Real.exp t)) := by
            rw [mul_assoc]
    _ = algebraMap ℝ A (Real.exp t) *
          (algebraMap ℝ A (Real.exp t) * x) := by
            rw [← Algebra.commutes (Real.exp t) x]
    _ = algebraMap ℝ A (Real.exp t) * algebraMap ℝ A (Real.exp t) * x := by
          simp only [mul_assoc]
    _ = algebraMap ℝ A (Real.exp t * Real.exp t) * x := by
          rw [map_mul]
    _ = algebraMap ℝ A (Real.exp (2 * t)) * x := by
          rw [← Real.exp_add]
          congr 2
          ring_nf

private theorem algebraMap_exp_neg_mul
    {A : Type*} [Ring A] [Algebra ℝ A] (t : ℝ) (x : A) :
    algebraMap ℝ A (Real.exp t) * x * algebraMap ℝ A (Real.exp (-t)) = x := by
  calc
    algebraMap ℝ A (Real.exp t) * x * algebraMap ℝ A (Real.exp (-t)) =
        algebraMap ℝ A (Real.exp t) *
          (x * algebraMap ℝ A (Real.exp (-t))) := by
            simp only [mul_assoc]
    _ = algebraMap ℝ A (Real.exp t) *
          (algebraMap ℝ A (Real.exp (-t)) * x) := by
            rw [← Algebra.commutes (Real.exp (-t)) x]
    _ = algebraMap ℝ A (Real.exp t) * algebraMap ℝ A (Real.exp (-t)) * x := by
          simp only [mul_assoc]
    _ = algebraMap ℝ A (Real.exp t * Real.exp (-t)) * x := by
          rw [map_mul]
    _ = x := by
          rw [← Real.exp_add]
          simp

theorem splitCartanConjugation_qPlus {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) (a : A) :
    splitCartanConjugation t (qPlus a) =
      qPlus (algebraMap ℝ A (Real.exp (2 * t)) * a) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [splitCartanConjugation, splitCartanDiagonal, qPlus,
      Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]
  · simp only [splitCartanConjugation, splitCartanDiagonal, qPlus,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    simpa [splitCartanConjugation, splitCartanDiagonal, qPlus,
      Matrix.mul_apply, Fin.sum_univ_two] using
        algebraMap_exp_twice_mul t a
  · simp [splitCartanConjugation, splitCartanDiagonal, qPlus,
      Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]
  · simp [splitCartanConjugation, splitCartanDiagonal, qPlus,
      Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]

theorem splitCartanConjugation_qMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) (b : A) :
    splitCartanConjugation t (qMinus b) =
      qMinus (algebraMap ℝ A (Real.exp (-2 * t)) * b) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [splitCartanConjugation, splitCartanDiagonal, qMinus,
      Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]
  · simp [splitCartanConjugation, splitCartanDiagonal, qMinus,
      Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]
  · simp only [splitCartanConjugation, splitCartanDiagonal, qMinus,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have h := algebraMap_exp_twice_mul (-t) b
    simpa [splitCartanConjugation, splitCartanDiagonal, qMinus,
      Matrix.mul_apply, Fin.sum_univ_two, neg_mul, neg_neg] using h
  · simp [splitCartanConjugation, splitCartanDiagonal, qMinus,
      Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]

theorem splitCartanConjugation_qAnticomm {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) (a b : A) :
    splitCartanConjugation t (qAnticomm a b) = qAnticomm a b := by
  rw [qAnticomm_eq_partnerHamiltonian]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [splitCartanConjugation, splitCartanDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    simpa [splitCartanConjugation, splitCartanDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two] using
        algebraMap_exp_neg_mul t (a * b)
  · simp [splitCartanConjugation, splitCartanDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp [splitCartanConjugation, splitCartanDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp only [splitCartanConjugation, splitCartanDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    simpa [splitCartanConjugation, splitCartanDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two] using
        algebraMap_exp_neg_mul (-t) (b * a)

/-! ## Public coefficient-transport Cartan API -/

/-- The split-Cartan adjoint action has weight `+2` on the upper chiral block. -/
theorem cartanConj_qPlus {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) (a : A) :
    splitCartanConjugation t (qPlus a) =
      qPlus (algebraMap ℝ A (Real.exp (2 * t)) * a) :=
  splitCartanConjugation_qPlus t a

/-- The split-Cartan adjoint action has weight `-2` on the lower chiral block. -/
theorem cartanConj_qMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) (b : A) :
    splitCartanConjugation t (qMinus b) =
      qMinus (algebraMap ℝ A (Real.exp (-2 * t)) * b) :=
  splitCartanConjugation_qMinus t b

/-- The even partner channel is invariant under the split-Cartan action. -/
theorem cartanConj_qAnticomm {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) (a b : A) :
    splitCartanConjugation t (qAnticomm a b) = qAnticomm a b :=
  splitCartanConjugation_qAnticomm t a b

/-- The SUSY Hamiltonian/anticommutator is the Cartan-invariant even channel. -/
theorem cartanConj_susyHamiltonian {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) (a b : A) :
    splitCartanConjugation t (qAnticomm a b) = qAnticomm a b :=
  cartanConj_qAnticomm t a b

end InfoGeometry.OperatorAlgebra.ChiralSplitCartanActionBridge
