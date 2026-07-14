import InfoGeometry.Dynamics.RindlerWedge
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section

/-!
# KmsBoundary

Finite `2 × 2` matrix identities for the imaginary-time boundary of the
diagonal Rindler modular flow.

This file deliberately proves the algebraic shadow used by the surrounding
finite model: a diagonal Gibbs weight, the corresponding imaginary-time
conjugation, a trace-cyclicity KMS identity, and the `2π i` periodicity of the
complexified boost.  It does not assert the analytic KMS theorem for a
von Neumann algebra.
-/

namespace KmsBoundary

open Matrix

/-- The `2 × 2` complex matrix carrier used for the finite modular model. -/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Diagonal boost Hamiltonian in the finite Rindler model. -/
def modularHamiltonian : Mat2C :=
  !![(1 : ℂ), 0;
     0, -1]

/-- The finite diagonal modular Hamiltonian is Hermitian. -/
@[simp]
theorem modularHamiltonian_conjTranspose :
    modularHamiltonianᴴ = modularHamiltonian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modularHamiltonian]

/-- The finite diagonal modular Hamiltonian is self-adjoint as an operator. -/
theorem modularHamiltonian_isSelfAdjoint :
    IsSelfAdjoint modularHamiltonian := by
  rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose]
  exact modularHamiltonian_conjTranspose

/--
The operator-valued Bregman remainder of the finite self-adjoint modular
Hamiltonian:

`exp (ε • K) - I - ε • K`, with `K = modularHamiltonian`.
-/
noncomputable def modularHamiltonianBregmanRemainder (ε : ℝ) : Mat2C :=
  (NormedSpace.exp (ε • modularHamiltonian) : Mat2C) - 1
    - (ε • modularHamiltonian : Mat2C)

/-- A real step along the finite modular Hamiltonian remains self-adjoint. -/
theorem modularHamiltonian_step_isSelfAdjoint (ε : ℝ) :
    IsSelfAdjoint (ε • modularHamiltonian : Mat2C) := by
  rw [isSelfAdjoint_iff, star_smul, modularHamiltonian_isSelfAdjoint.star_eq]
  simp

/-- The matrix exponential of the finite self-adjoint modular step is self-adjoint. -/
theorem modularHamiltonian_exp_isSelfAdjoint (ε : ℝ) :
    IsSelfAdjoint ((NormedSpace.exp (ε • modularHamiltonian) : Mat2C)) := by
  simpa using (modularHamiltonian_step_isSelfAdjoint ε).exp

/-- The finite modular-Hamiltonian Bregman remainder is self-adjoint. -/
theorem modularHamiltonianBregmanRemainder_isSelfAdjoint (ε : ℝ) :
    IsSelfAdjoint (modularHamiltonianBregmanRemainder ε) := by
  have hExp : IsSelfAdjoint ((NormedSpace.exp (ε • modularHamiltonian) : Mat2C)) :=
    modularHamiltonian_exp_isSelfAdjoint ε
  have hOne : IsSelfAdjoint (1 : Mat2C) :=
    IsSelfAdjoint.one Mat2C
  have hStep : IsSelfAdjoint (ε • modularHamiltonian : Mat2C) :=
    modularHamiltonian_step_isSelfAdjoint ε
  exact (hExp.sub hOne).sub hStep

/-- Imaginary-time Gibbs weight `exp(-β H)`. -/
def imaginaryTimeEvolution (β : ℂ) : Mat2C :=
  !![Complex.exp (-β), 0;
     0, Complex.exp β]

/-- The inverse diagonal weight `exp(β H)`. -/
def inverseImaginaryTimeEvolution (β : ℂ) : Mat2C :=
  !![Complex.exp β, 0;
     0, Complex.exp (-β)]

/-- Imaginary-time modular conjugation by the diagonal Gibbs weight. -/
def imaginaryAutomorphism (β : ℂ) (A : Mat2C) : Mat2C :=
  imaginaryTimeEvolution β * A * inverseImaginaryTimeEvolution β

/-- The unnormalised diagonal thermal density profile. -/
def rindlerThermalDensity (β : ℂ) : Mat2C :=
  imaginaryTimeEvolution β

/-- The diagonal imaginary-time weight is inverted by the opposite weight. -/
theorem imaginaryTimeEvolution_mul_inverse (β : ℂ) :
    imaginaryTimeEvolution β * inverseImaginaryTimeEvolution β = (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [imaginaryTimeEvolution, inverseImaginaryTimeEvolution, Matrix.mul_apply,
      ← Complex.exp_add]

/-- The opposite diagonal weight is also a left inverse. -/
theorem inverse_mul_imaginaryTimeEvolution (β : ℂ) :
    inverseImaginaryTimeEvolution β * imaginaryTimeEvolution β = (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [imaginaryTimeEvolution, inverseImaginaryTimeEvolution, Matrix.mul_apply,
      ← Complex.exp_add]

/--
Finite KMS boundary identity for the diagonal Gibbs weight.

It is just trace cyclicity plus the cancellation
`exp(β H) * exp(-β H) = 1` in the finite matrix model.
-/
theorem kms_boundary_condition (β : ℂ) (A B : Mat2C) :
    Matrix.trace (rindlerThermalDensity β * A * imaginaryAutomorphism β B) =
      Matrix.trace (rindlerThermalDensity β * B * A) := by
  let D := imaginaryTimeEvolution β
  let Dinv := inverseImaginaryTimeEvolution β
  have hDinvD : Dinv * D = (1 : Mat2C) := by
    simpa [D, Dinv] using inverse_mul_imaginaryTimeEvolution β
  calc
    Matrix.trace (rindlerThermalDensity β * A * imaginaryAutomorphism β B)
        = Matrix.trace (D * A * (D * B * Dinv)) := by
            simp [D, Dinv, rindlerThermalDensity, imaginaryAutomorphism]
    _ = Matrix.trace (((D * A * D) * B) * Dinv) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace (Dinv * ((D * A * D) * B)) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (((Dinv * D) * A * D) * B) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace ((A * D) * B) := by
            rw [hDinvD]
            simp [Matrix.mul_assoc]
    _ = Matrix.trace (B * (A * D)) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((B * A) * D) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace (D * (B * A)) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (D * B * A) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace (rindlerThermalDensity β * B * A) := by
            simp [D, rindlerThermalDensity]

/-- Imaginary-time evolution is the identity at zero time. -/
@[simp] theorem imaginaryTimeEvolution_zero :
    imaginaryTimeEvolution 0 = (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [imaginaryTimeEvolution]

/--
The finite diagonal boost is periodic at imaginary rapidity `2π i`.
-/
theorem unruh_periodicity :
    imaginaryTimeEvolution (2 * (Real.pi : ℂ) * Complex.I) = (1 : Mat2C) := by
  have hpos : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    simp [Complex.exp_two_pi_mul_I]
  have hneg : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_neg, hpos, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [imaginaryTimeEvolution, hpos, hneg]

end KmsBoundary
