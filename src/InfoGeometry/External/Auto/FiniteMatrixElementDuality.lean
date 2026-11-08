import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite matrix elements, observables, and adjoints

This file formalizes the finite-dimensional kernel behind the user's statement:
expectation values `<ω|OP|ω>`, transition amplitudes `<ω₁|OP|ω₂>`, and
transition probabilities are linear functionals of the operator algebra once the
states are fixed.  Group/basis transformations act by conjugating the operator
and transforming the states; measurable quantities are the invariant/covariant
matrix elements.

The analytic GNS/Krein/Dirac/modular completion remains socketed elsewhere.  The
kernel here is finite `2 × 2` complex linear algebra.
-/

noncomputable section

open Complex

namespace FiniteMatrixElementDuality

abbrev V2C := InfoGeometry.Algebra.FiniteSpin.Vec2C
abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

def cstar (z : ℂ) : ℂ := starRingEnd ℂ z

/-- Explicit finite matrix-vector product. -/
def act (A : M2C) (v : V2C) : V2C := fun i => ∑ j : Fin 2, A i j * v j

/-- Dirac matrix element `<bra|A|ket>`.  For fixed states this is a linear
functional on the operator algebra. -/
def matrixElement (bra : V2C) (A : M2C) (ket : V2C) : ℂ :=
  ∑ i : Fin 2, cstar (bra i) * act A ket i

/-- Expectation value `<ω|A|ω>`. -/
def expectation (ω : V2C) (A : M2C) : ℂ := matrixElement ω A ω

/-- Transition amplitude `<ω₁|A|ω₂>`. -/
def transitionAmplitude (ω₁ : V2C) (A : M2C) (ω₂ : V2C) : ℂ :=
  matrixElement ω₁ A ω₂

/-- Transition probability `|<ω₁|A|ω₂>|²`. -/
def transitionProbability (ω₁ : V2C) (A : M2C) (ω₂ : V2C) : ℝ :=
  Complex.normSq (transitionAmplitude ω₁ A ω₂)

/-- Operator transformation by a pair of inverse matrices. -/
def conjugateBy (U V A : M2C) : M2C := U * A * V

/-- State transformation. -/
def transformState (U : M2C) (ω : V2C) : V2C := act U ω

/-- Pauli-X swap matrix. -/
def σx : M2C := !![(0 : ℂ), 1; 1, 0]

/-- Krein/Dirac signature matrix `J = diag(1,-1)`. -/
def J : M2C := !![(1 : ℂ), 0; 0, -1]

/-- The finite Dirac adjoint. -/
def diracAdjoint (A : M2C) : M2C := Matrix.conjTranspose A

/-- The finite Krein adjoint with metric `J`: `A^× = J A† J`. -/
def kreinAdjoint (A : M2C) : M2C := J * Matrix.conjTranspose A * J

/-- The standard basis ket `|0>`. -/
def ket0 : V2C := fun i => if i = 0 then 1 else 0

/-- The standard basis ket `|1>`. -/
def ket1 : V2C := fun i => if i = 1 then 1 else 0

/-- The operator basis matrix unit `Eᵢⱼ`. -/
def matrixUnit (i j : Fin 2) : M2C := fun a b => if a = i ∧ b = j then 1 else 0

/-- Matrix elements extract entries: `<i|A|j> = Aᵢⱼ`. -/
theorem matrixElement_basis_entry (A : M2C) (i j : Fin 2) :
    matrixElement (fun a => if a = i then 1 else 0) A (fun b => if b = j then 1 else 0) = A i j := by
  fin_cases i <;> fin_cases j <;>
    simp [matrixElement, act, cstar]

/-- In particular, measurements of all basis transitions invert the finite
operator: the observed matrix elements determine the operator entries. -/
theorem operator_ext_from_matrix_elements {A B : M2C}
    (h : ∀ i j : Fin 2,
      matrixElement (fun a => if a = i then 1 else 0) A (fun b => if b = j then 1 else 0) =
      matrixElement (fun a => if a = i then 1 else 0) B (fun b => if b = j then 1 else 0)) :
    A = B := by
  ext i j
  simpa [matrixElement_basis_entry] using h i j

/-- Matrix elements are additive in the operator. -/
theorem matrixElement_add (bra ket : V2C) (A B : M2C) :
    matrixElement bra (A + B) ket = matrixElement bra A ket + matrixElement bra B ket := by
  unfold matrixElement act
  simp [Matrix.add_apply, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc,
    mul_left_comm, mul_comm]

/-- Matrix elements are scalar-linear in the operator. -/
theorem matrixElement_smul (bra ket : V2C) (c : ℂ) (A : M2C) :
    matrixElement bra (c • A) ket = c * matrixElement bra A ket := by
  simp [matrixElement, act, Matrix.smul_apply, mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
  ring

/-- The swap matrix is involutive. -/
theorem σx_sq : σx * σx = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [σx, Matrix.mul_apply]

/-- The Krein metric is involutive. -/
theorem J_sq : J * J = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply]

/-- Direct finite swap of state components. -/
def swapState (ω : V2C) : V2C := fun i => if i = 0 then ω 1 else ω 0

/-- Direct finite conjugation of operator entries by the swap permutation. -/
def swapOperator (A : M2C) : M2C := fun i j =>
  if i = 0 then
    if j = 0 then A 1 1 else A 1 0
  else
    if j = 0 then A 0 1 else A 0 0

/-- Krein matrix element is the Dirac matrix element after applying `J` to the
bra/state. -/
theorem krein_matrixElement_eq_dirac_J (bra ket : V2C) (A : M2C) :
    matrixElement bra (J * A) ket = matrixElement (transformState J bra) A ket := by
  simp [matrixElement, transformState, act, J, cstar, Matrix.mul_apply, mul_assoc,
    mul_left_comm, mul_comm, Finset.mul_sum]
  ring_nf

/-- For the swap basis change, transforming both states and conjugating the
operator leaves the finite matrix element invariant. -/
theorem swap_covariance (bra ket : V2C) (A : M2C) :
    matrixElement (swapState bra) (swapOperator A) (swapState ket) =
      matrixElement bra A ket := by
  simp [matrixElement, swapState, swapOperator, act, cstar, Matrix.mul_apply, mul_assoc,
    mul_left_comm, mul_comm, Finset.mul_sum]
  ring_nf

/-- The corresponding transition probability is invariant under the same swap
basis change. -/
theorem swap_transitionProbability_invariant (bra ket : V2C) (A : M2C) :
    transitionProbability (swapState bra) (swapOperator A) (swapState ket) =
      transitionProbability bra A ket := by
  simp [transitionProbability, transitionAmplitude, swap_covariance]

end FiniteMatrixElementDuality
