import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Inner Pauli and outer Nambu shell

The inner `2 × 2` matrices are Pauli-soldered chiral rails.  The outer
`2 × 2` matrix is the Nambu carrier.  Both products are ordinary associative
matrix products; no split-octonion multiplication is introduced.
-/

namespace InfoGeometry.Physics.PauliNambuShell

open Matrix

variable {A : Type*} [Ring A] [Algebra ℂ A]

abbrev WeylMatrix (A : Type*) := Matrix (Fin 2) (Fin 2) A
abbrev NambuMatrix (A : Type*) := Matrix (Fin 2) (Fin 2) (WeylMatrix A)

def pauliSoldering (u q₁ q₂ q₃ : A) : WeylMatrix A :=
  !![u + q₃, q₁ - Complex.I • q₂;
     q₁ + Complex.I • q₂, u - q₃]

def nambuDirac (plus minus : WeylMatrix A) : NambuMatrix A :=
  !![0, plus; minus, 0]

@[simp] theorem pauliSoldering_apply (u q₁ q₂ q₃ : A) :
    pauliSoldering u q₁ q₂ q₃ =
      !![u + q₃, q₁ - Complex.I • q₂;
         q₁ + Complex.I • q₂, u - q₃] := rfl

@[simp] theorem nambuDirac_square (plus minus : WeylMatrix A) :
    nambuDirac plus minus * nambuDirac plus minus =
      !![plus * minus, 0; 0, minus * plus] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nambuDirac, Matrix.mul_apply, Fin.sum_univ_two]

theorem nambuDirac_square_even (plus minus : WeylMatrix A) :
    nambuDirac plus minus * nambuDirac plus minus =
      !![plus * minus, 0; 0, minus * plus] :=
  nambuDirac_square plus minus

end InfoGeometry.Physics.PauliNambuShell
