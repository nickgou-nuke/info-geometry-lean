import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- Четният сектор (The Operator Algebra) -/
abbrev ClPlus := evenOdd Q 0

/-- Нечетният сектор (The Spacetime Bimodule) -/
abbrev ClMinus := evenOdd Q 1

/-- ТЕОРЕМА 1: Четен * Четен = Четен (Subalgebra Closure) -/
theorem clPlus_mul_clPlus (a b : CliffordAlgebra Q)
    (ha : a ∈ ClPlus Q) (hb : b ∈ ClPlus Q) :
    a * b ∈ ClPlus Q := by
  have h_mul := Submodule.mul_mem_mul ha hb
  have h_le := evenOdd_mul_le Q 0 0 h_mul
  rwa [add_zero] at h_le

/-- ТЕОРЕМА 2: Четен * Нечетен = Нечетен (Left Module Action) -/
theorem clPlus_mul_clMinus (a b : CliffordAlgebra Q)
    (ha : a ∈ ClPlus Q) (hb : b ∈ ClMinus Q) :
    a * b ∈ ClMinus Q := by
  have h_mul := Submodule.mul_mem_mul ha hb
  have h_le := evenOdd_mul_le Q 0 1 h_mul
  rwa [zero_add] at h_le

/-- ТЕОРЕМА 3: Нечетен * Четен = Нечетен (Right Module Action) -/
theorem clMinus_mul_clPlus (a b : CliffordAlgebra Q)
    (ha : a ∈ ClMinus Q) (hb : b ∈ ClPlus Q) :
    a * b ∈ ClMinus Q := by
  have h_mul := Submodule.mul_mem_mul ha hb
  have h_le := evenOdd_mul_le Q 1 0 h_mul
  rwa [add_zero] at h_le

/-- ТЕОРЕМА 4: Нечетен * Нечетен = Четен (The Vector Inner Product returns to operators) -/
theorem clMinus_mul_clMinus (a b : CliffordAlgebra Q)
    (ha : a ∈ ClMinus Q) (hb : b ∈ ClMinus Q) :
    a * b ∈ ClPlus Q := by
  have h_mul := Submodule.mul_mem_mul ha hb
  have h_le := evenOdd_mul_le Q 1 1 h_mul
  have h_add : (1 : ZMod 2) + (1 : ZMod 2) = 0 := by decide
  rwa [h_add] at h_le

end InfoGeometry.Clifford.Hestenes
