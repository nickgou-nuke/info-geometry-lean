import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.FourierOperatorPolynomial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {R : Type*} [CommRing R]

def IsFourierFourthRoot (X : R) : Prop := X ^ 4 = 1

def VacuumExtendedPolynomial (X : R) : R := X ^ 5 - X

def TripartiteFactorization (X : R) : R := X * (X ^ 2 - 1) * (X ^ 2 + 1)

def GeneralTripartiteFactorization (X : R) (k : ℕ) : R := X * (X ^ (2 * k) - 1) * (X ^ (2 * k) + 1)

theorem tripartite_factorization_eq_quintic (X : R) :
    X * (X ^ 2 - 1) * (X ^ 2 + 1) = X ^ 5 - X := by
  ring

theorem general_tripartite_factorization (X : R) (k : ℕ) :
    X * (X ^ (2 * k) - 1) * (X ^ (2 * k) + 1) = X ^ (4 * k + 1) - X := by
  have h_sq : (X ^ (2 * k) - 1) * (X ^ (2 * k) + 1) = X ^ (4 * k) - 1 := by
    calc (X ^ (2 * k) - 1) * (X ^ (2 * k) + 1)
      _ = (X ^ (2 * k)) ^ 2 - 1 ^ 2 := by ring
      _ = X ^ (2 * k * 2) - 1 := by rw [← pow_mul, one_pow]
      _ = X ^ (4 * k) - 1 := by
        have : 2 * k * 2 = 4 * k := by ring
        rw [this]
  calc X * (X ^ (2 * k) - 1) * (X ^ (2 * k) + 1)
    _ = X * ((X ^ (2 * k) - 1) * (X ^ (2 * k) + 1)) := by rw [mul_assoc]
    _ = X * (X ^ (4 * k) - 1) := by rw [h_sq]
    _ = X * X ^ (4 * k) - X * 1 := by rw [mul_sub]
    _ = X ^ (4 * k + 1) - X := by
      have : X * X ^ (4 * k) = X ^ (4 * k + 1) := by
        have h_p : X ^ (4 * k + 1) = X ^ (4 * k) * X := by rw [pow_succ]
        rw [h_p, mul_comm]
      rw [this, mul_one]

theorem fourier_fourth_root_annihilates_quintic (X : R) (hX : IsFourierFourthRoot X) :
    X ^ 5 - X = 0 := by
  unfold IsFourierFourthRoot at hX
  have h_split : X ^ 5 = X * X ^ 4 := by
    have : 5 = 1 + 4 := by norm_num
    rw [this, pow_add, pow_one]
  rw [h_split, hX, mul_one, sub_self]

theorem fourier_tripartite_annihilation (X : R) (hX : IsFourierFourthRoot X) :
    X * (X ^ 2 - 1) * (X ^ 2 + 1) = 0 := by
  rw [tripartite_factorization_eq_quintic, fourier_fourth_root_annihilates_quintic X hX]

end InfoGeometry.Quantum.FourierOperatorPolynomial
