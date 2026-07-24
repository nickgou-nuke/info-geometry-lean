import InfoGeometry.Dynamics.KmsBoundary
import Mathlib.Tactic

noncomputable section

/-!
# TomitaTakesaki

Finite `2 × 2` matrix shadow of the Tomita--Takesaki modular data associated
with the diagonal Rindler model from `KmsBoundary`.

The genuine Tomita conjugation is anti-linear in Hilbert-space standard form.
Here we record the matrix-level algebra used by this repository: the Pauli-X
reflection `J`, the diagonal modular operator `Δ`, and the induced complexified
diagonal flow.
-/

namespace InfoGeometry.Dynamics.TomitaTakesaki

open Matrix
open InfoGeometry.Dynamics.KmsBoundary

/-- Modular operator `Δ = exp(-H)` in the finite diagonal model. -/
def modularOperator : Mat2C :=
  imaginaryTimeEvolution 1

/-- Positive square-root profile `Δ^{1/2} = exp(-H / 2)`. -/
def modularOperatorSqrt : Mat2C :=
  imaginaryTimeEvolution (1 / 2)

/--
Matrix part of the modular conjugation in this two-wedge toy model.

This is the Pauli-X reflection exchanging the two diagonal eigenspaces.
-/
def modularConjugation : Mat2C :=
  !![0, (1 : ℂ);
     1, 0]

/-- The finite matrix representative of `S = J Δ^{1/2}`. -/
def tomitaOperator : Mat2C :=
  modularConjugation * modularOperatorSqrt

/-- The matrix reflection `J` is an involution. -/
@[simp] theorem modularConjugation_is_involution :
    modularConjugation * modularConjugation = (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modularConjugation, Matrix.mul_apply]

/-- The matrix reflection `J` is self-adjoint. -/
@[simp] theorem modularConjugation_conjTranspose :
    modularConjugationᴴ = modularConjugation := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modularConjugation]

/--
`J` flips the sign of the diagonal boost Hamiltonian.
-/
theorem modularConjugation_reflects_hamiltonian :
    modularConjugation * KmsBoundary.modularHamiltonian * modularConjugation =
      -KmsBoundary.modularHamiltonian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularConjugation, KmsBoundary.modularHamiltonian, Matrix.mul_apply]

/--
Conjugating a diagonal boost generator by `J` sends it to the reflected
diagonal generator.
-/
theorem tomita_commutant_reflection (lam : ℂ) :
    let A : Mat2C := !![lam, 0; 0, -lam]
    modularConjugation * A * modularConjugation = !![-lam, 0; 0, lam] := by
  intro A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, modularConjugation, Matrix.mul_apply]

/-- Complexified modular flow `Δ^{it}` in this diagonal model. -/
def finiteTomitaFlow (t : ℝ) : Mat2C :=
  imaginaryTimeEvolution (-(Complex.I * (t : ℂ)))

/--
The finite modular flow is exactly the diagonal complex boost with phases
`exp(± i t)`.
-/
theorem tomita_flow_matches_diagonal_boost (t : ℝ) :
    finiteTomitaFlow t =
      !![Complex.exp (Complex.I * (t : ℂ)), 0;
         0, Complex.exp (-(Complex.I * (t : ℂ)))] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteTomitaFlow, imaginaryTimeEvolution]

/-- The finite modular flow starts at the identity. -/
@[simp] theorem finiteTomitaFlow_zero :
    finiteTomitaFlow 0 = (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteTomitaFlow, imaginaryTimeEvolution]

/-- The diagonal finite modular flow composes additively in its time parameter. -/
theorem finiteTomitaFlow_add (s t : ℝ) :
    finiteTomitaFlow s * finiteTomitaFlow t = finiteTomitaFlow (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteTomitaFlow, imaginaryTimeEvolution, Matrix.mul_apply,
      ← Complex.exp_add, mul_add]
  all_goals ring_nf

end InfoGeometry.Dynamics.TomitaTakesaki
