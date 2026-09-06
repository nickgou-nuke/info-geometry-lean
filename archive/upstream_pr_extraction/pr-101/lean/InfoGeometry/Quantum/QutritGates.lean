import InfoGeometry.Quantum.Qutrit
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Qutrit rotation gates

This file gives a structural, normalized Gell--Mann realization of the qutrit
rotation formula

`exp (-i / 2 • ∑ a, Θ a • λ a)`.

The generators live in the real submodule of traceless Hermitian `3 × 3`
complex matrices.  This makes Hermiticity and tracelessness stable under real
linear combinations without coordinate case splits.  Matrix-exponential
identities then prove that every resulting rotation is a genuine element of
`U(3)`.

The older physics owner `Physics/GellMannSU3.lean` uses the unnormalized matrix
`diag(1,1,-2)` as `gl8`; here `λ₈` has the standard factor `1 / √3` required by
the qutrit/SU(3) convention.

Mathlib currently lacks the general theorem
`det (exp A) = exp (trace A)`.  Consequently this file proves unitarity and a
zero-trace generator, but does not misstate the exponential as an element of
Mathlib's `specialUnitaryGroup`.  The claimed universal nine-gate synthesis is
also not asserted: it requires a separate surjectivity/Euler-decomposition
theorem for this parameterization.
-/

noncomputable section

open Matrix NormedSpace

namespace InfoGeometry.Quantum.Qutrit

/-- Matrices acting on a qutrit. -/
abbrev QutritMatrix : Type := Matrix (Fin 3) (Fin 3) ℂ

/-- Gates on the computational realization of an `n`-qutrit register. -/
abbrev QutritRegisterGate (n : ℕ) : Type :=
  Matrix.unitaryGroup (QutritRegisterIndex n) ℂ

/-- Matrix unit `Eᵢⱼ`. -/
def matrixUnit (i j : Fin 3) : QutritMatrix := Matrix.single i j 1

@[simp] theorem matrixUnit_conjTranspose (i j : Fin 3) :
    (matrixUnit i j)ᴴ = matrixUnit j i := by
  simp [matrixUnit]

/-- `Eᵢⱼ + Eⱼᵢ`, bundled as a Hermitian matrix. -/
def symmetricUnit (i j : Fin 3) : selfAdjoint QutritMatrix :=
  ⟨matrixUnit i j + matrixUnit j i, by
    rw [selfAdjoint.mem_iff]
    change (matrixUnit i j + matrixUnit j i)ᴴ = _
    simp [matrixUnit_conjTranspose, add_comm]⟩

/-- `-iEᵢⱼ + iEⱼᵢ`, bundled as a Hermitian matrix. -/
def antisymmetricUnit (i j : Fin 3) : selfAdjoint QutritMatrix :=
  ⟨(-Complex.I) • matrixUnit i j + Complex.I • matrixUnit j i, by
    rw [selfAdjoint.mem_iff]
    change ((-Complex.I) • matrixUnit i j + Complex.I • matrixUnit j i)ᴴ = _
    simp [matrixUnit_conjTranspose, add_comm]⟩

/-- The rank-one coordinate projector `Eᵢᵢ`. -/
def diagonalUnit (i : Fin 3) : selfAdjoint QutritMatrix :=
  ⟨matrixUnit i i, by
    rw [selfAdjoint.mem_iff]
    change (matrixUnit i i)ᴴ = _
    simp [matrixUnit_conjTranspose]⟩

/-- The real subspace of traceless Hermitian `3 × 3` complex matrices. -/
def tracelessHermitian : Submodule ℝ QutritMatrix :=
  selfAdjoint.submodule ℝ QutritMatrix ⊓ (Matrix.traceLinearMap (Fin 3) ℝ ℂ).ker

/-- An off-diagonal real Gell--Mann direction. -/
def symmetricGellMann (i j : Fin 3) (hij : i ≠ j) : tracelessHermitian :=
  ⟨symmetricUnit i j, ⟨(symmetricUnit i j).property, by
    simp [symmetricUnit, matrixUnit, Matrix.trace_single_eq_of_ne, hij, hij.symm]⟩⟩

/-- An off-diagonal imaginary Gell--Mann direction. -/
def antisymmetricGellMann (i j : Fin 3) (hij : i ≠ j) : tracelessHermitian :=
  ⟨antisymmetricUnit i j, ⟨(antisymmetricUnit i j).property, by
    simp [antisymmetricUnit, matrixUnit, Matrix.trace_single_eq_of_ne, hij, hij.symm]⟩⟩

/-- The standard third Gell--Mann matrix `diag(1,-1,0)`. -/
def diagonalGellMann3 : tracelessHermitian :=
  ⟨(diagonalUnit 0 : QutritMatrix) - diagonalUnit 1,
    ⟨(diagonalUnit 0).property.sub (diagonalUnit 1).property, by
      simp [diagonalUnit, matrixUnit, Matrix.trace_single_eq_same]⟩⟩

/-- The normalized eighth Gell--Mann matrix `diag(1,1,-2)/√3`. -/
def diagonalGellMann8 : tracelessHermitian :=
  ⟨((1 / Real.sqrt 3 : ℝ) : ℂ) •
      ((diagonalUnit 0 : QutritMatrix) + (diagonalUnit 1 : QutritMatrix) -
        2 • (diagonalUnit 2 : QutritMatrix)),
    ⟨by
      change (((1 / Real.sqrt 3 : ℝ) : ℂ) •
        ((diagonalUnit 0 : QutritMatrix) + (diagonalUnit 1 : QutritMatrix) -
          2 • (diagonalUnit 2 : QutritMatrix)))ᴴ = _
      simp [diagonalUnit, matrixUnit],
      by
        simp [diagonalUnit, matrixUnit, Matrix.trace_single_eq_same]
        norm_num⟩⟩

/-- The eight standard normalized Gell--Mann matrices. -/
def gellMann : Fin 8 → tracelessHermitian := ![
  symmetricGellMann 0 1 (by omega),
  antisymmetricGellMann 0 1 (by omega),
  diagonalGellMann3,
  symmetricGellMann 0 2 (by omega),
  antisymmetricGellMann 0 2 (by omega),
  symmetricGellMann 1 2 (by omega),
  antisymmetricGellMann 1 2 (by omega),
  diagonalGellMann8
]

/-- The Hermitian generator `H(Θ) = 1/2 ∑ₐ Θₐ λₐ`. -/
def rotationHamiltonian (Θ : Fin 8 → ℝ) : tracelessHermitian :=
  (1 / 2 : ℝ) • ∑ a, Θ a • gellMann a

/-- Matrix readback of the real-linear Gell--Mann combination. -/
theorem rotationHamiltonian_coe (Θ : Fin 8 → ℝ) :
    (rotationHamiltonian Θ : QutritMatrix) =
      (((1 / 2 : ℝ) : ℂ) •
        ∑ a, ((Θ a : ℝ) : ℂ) • (gellMann a : QutritMatrix)) := by
  rfl

/-- The Gell--Mann rotation Hamiltonian is Hermitian. -/
theorem rotationHamiltonian_isHermitian (Θ : Fin 8 → ℝ) :
    Matrix.IsHermitian (rotationHamiltonian Θ : QutritMatrix) :=
  (rotationHamiltonian Θ).property.1

/-- The Gell--Mann rotation Hamiltonian is traceless. -/
theorem rotationHamiltonian_trace (Θ : Fin 8 → ℝ) :
    Matrix.trace (rotationHamiltonian Θ : QutritMatrix) = 0 :=
  (rotationHamiltonian Θ).property.2

/-- The qutrit rotation matrix `exp (-i H(Θ))`. -/
def rotationMatrix (Θ : Fin 8 → ℝ) : QutritMatrix :=
  exp ((-Complex.I) • (rotationHamiltonian Θ : QutritMatrix))

/-- Readback in the source's displayed `exp(-i/2 ∑ₐ Θₐ λₐ)` form. -/
theorem rotationMatrix_eq_source_formula (Θ : Fin 8 → ℝ) :
    rotationMatrix Θ =
      exp (((-Complex.I) / 2) •
        ∑ a, ((Θ a : ℝ) : ℂ) • (gellMann a : QutritMatrix)) := by
  simp [rotationMatrix, rotationHamiltonian_coe, smul_smul]
  congr 1
  rw [← neg_smul]
  congr 1
  ring

private theorem skew_of_tracelessHermitian (H : tracelessHermitian) :
    star ((-Complex.I) • (H : QutritMatrix)) =
      -((-Complex.I) • (H : QutritMatrix)) := by
  rw [star_smul, H.property.1]
  simp

/-- The exponential of a skew-Hermitian qutrit matrix is unitary. -/
theorem exp_skewHermitian_mem_unitary (A : QutritMatrix) (hA : star A = -A) :
    exp A ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  change Aᴴ = -A at hA
  rw [Matrix.mem_unitaryGroup_iff']
  change (exp A)ᴴ * exp A = 1
  rw [← Matrix.exp_conjTranspose, hA]
  calc
    exp (-A) * exp A = exp (-A + A) := by
      rw [Matrix.exp_add_of_commute]
      exact Commute.neg_left (Commute.refl A)
    _ = 1 := by simp

/-- Every real Gell--Mann parameter vector yields a genuine unitary qutrit matrix. -/
theorem rotationMatrix_mem_unitary (Θ : Fin 8 → ℝ) :
    rotationMatrix Θ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  apply exp_skewHermitian_mem_unitary
  exact skew_of_tracelessHermitian (rotationHamiltonian Θ)

/-- The Gell--Mann rotation bundled as a genuine qutrit gate. -/
def rotationGate (Θ : Fin 8 → ℝ) : QutritGate :=
  ⟨rotationMatrix Θ, rotationMatrix_mem_unitary Θ⟩

/-- The global phase matrix is exactly `exp(iδ I)`. -/
theorem globalPhaseMatrix_eq_exp (δ : ℝ) :
    globalPhaseMatrix δ = exp (((δ : ℂ) * Complex.I) • (1 : QutritMatrix)) := by
  rw [globalPhaseMatrix, phase, Matrix.smul_one_eq_diagonal,
    Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal]
  rw [Complex.exp_eq_exp_ℂ]
  rw [Pi.exp_def]

end InfoGeometry.Quantum.Qutrit
