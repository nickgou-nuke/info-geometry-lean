import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open Matrix Complex
open scoped Matrix Norms.Operator

noncomputable section

/-!
# Bregman deformation of the modular operator

The Bregman generator for the Poisson/coherent-state potential is

`f(x) = exp x - 1 - x`.

For a modular Hamiltonian step `x`, the corresponding matrix deformation is
`exp x - I - x`. For a relative modular operator `Δ` and a chosen logarithmic
readout `x`, the same regularized deformation is `Δ - I - x`.

This module is intentionally parameterized: it introduces no global modular
operator constants and no global proof postulates.

#### BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully
checked by the kernel.]

* `bregman_deformation_zero`
* `bregman_deformation_of_hamiltonian_zero`
* `phaseAxis_sq`
* `modularDelta_zero`
* `modularDelta_commutes_phaseAxis`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* `bregman_deformation_vanishes_at_flat_boundary`

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields,
witnesses, certificates, or renamed placeholders.]

* Prove that `modularDelta ε` agrees with `NormedSpace.exp (ε • phaseAxis)`
  from the matrix-exponential Taylor theorem.
* Lift the concrete `Fin 2` rotation model to the `Cl(1,1)` tower limit.
* Proof of Klein's inequality for a concrete trace/readout on the Cuntz/Cantor
  spectral triple.
* Identification of the parameterized matrix deformation here with Araki
  relative entropy in the repository's standard-form von Neumann algebra lane.
-/

namespace BregmanDeformation

/--
The concrete real phase-axis generator in the two-dimensional rotation lane.

It is the matrix representation of multiplication by the internal complex
structure unit, with `phaseAxis^2 = -1`.  It is not the self-adjoint modular
Hamiltonian; the self-adjoint diagonal Hamiltonian is owned by
`InfoGeometry.Dynamics.KmsBoundary.modularHamiltonian`.
-/
def phaseAxis : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, -1], ![1, 0]]

/--
The explicit closed-form phase-axis rotation
`Δ(ε) = [[cos ε, -sin ε], [sin ε, cos ε]]`.

This is the finite 2×2 model for `exp (ε • phaseAxis)` in the skew
complex-structure lane.  It is separate from the self-adjoint modular
Hamiltonian exponential `exp (ε • K)` used by the KMS/Bregman operator lane.
-/
def modularDelta (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(Real.cos ε : ℂ), -(Real.sin ε : ℂ)],
    ![(Real.sin ε : ℂ), (Real.cos ε : ℂ)]]

@[simp]
theorem phaseAxis_sq :
    phaseAxis * phaseAxis = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [phaseAxis, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem modularDelta_zero :
    modularDelta 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modularDelta]

/--
The explicit 2×2 modular rotation commutes with the phase axis.

This is the finite algebraic KMS phase-axis relation for the closed-form
rotation model.
-/
theorem modularDelta_commutes_phaseAxis (ε : ℝ) :
    modularDelta ε * phaseAxis = phaseAxis * modularDelta ε := by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [modularDelta, phaseAxis, Matrix.mul_apply, Fin.sum_univ_two]

/--
The regularized modular shape deformation `Δ - I - x`.
-/
def bregman_deformation
    (delta_op x_mod : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  delta_op - (1 : Matrix (Fin 2) (Fin 2) ℂ) - x_mod

/--
The exponential Bregman deformation generated directly from a modular
Hamiltonian step.
-/
def bregman_deformation_of_hamiltonian
    (x_mod : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp x_mod - (1 : Matrix (Fin 2) (Fin 2) ℂ) - x_mod

@[simp]
theorem bregman_deformation_zero :
    bregman_deformation
      (1 : Matrix (Fin 2) (Fin 2) ℂ)
      (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [bregman_deformation]

/--
At the flat KMS boundary where `Δ = 1` and the modular Hamiltonian step is
zero, the Bregman deformation vanishes.
-/
theorem bregman_deformation_vanishes_at_flat_boundary
    (delta_op x_mod : Matrix (Fin 2) (Fin 2) ℂ)
    (h_delta_one : delta_op = (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (h_x_zero : x_mod = 0) :
    bregman_deformation delta_op x_mod = 0 := by
  rw [h_delta_one, h_x_zero]
  exact bregman_deformation_zero

@[simp]
theorem bregman_deformation_of_hamiltonian_zero :
    bregman_deformation_of_hamiltonian
      (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [bregman_deformation_of_hamiltonian]

end BregmanDeformation
