import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearParityGradedHamiltonian
import InfoGeometry.Physics.NuclearSolovievParitySymmetry
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling

/-!
# Nuclear / spectroscopy Z₂ grading bridge

This module records the exact algebraic invariant shared by the finite
Soloviev CAR model and the mass-spectrometry directed-operator doubling.

The statement is deliberately representation-safe:

* the finite nuclear carrier is `Matrix (Fin 2) (Fin 2) ℝ` with fermion
  parity `finiteParity`;
* the spectroscopy carrier is the doubled `Sum (Fin n) (Fin n)` matrix space
  with grading `gradingMatrix n`;
* no equality or physical identification between those carriers is asserted.

What is common is the same native predicate from
`NuclearParityGradedHamiltonian`:

`OddUnderConjugation P X :↔ P * X * P = -X`.

Thus the zero-diagonal Soloviev interaction Hamiltonian and every doubled
spectroscopy transfer operator are exact instances of one Z₂-graded operator
law.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearSpectroscopyZ2GradingBridge

open InfoGeometry.Physics.NuclearParityGradedHamiltonian
open InfoGeometry.Physics.NuclearFiniteCARProjection
open InfoGeometry.Physics.NuclearFiniteCARCartanSolovievBridge
open InfoGeometry.Physics.NuclearSolovievParitySymmetry
open InfoGeometry.MassSpectrometry

/-- The spectroscopy grading matrix is an involution in the same generic
sense used by the nuclear parity-graded Hamiltonian owner. -/
theorem spectroscopyGrading_isInvolution (n : ℕ) :
    IsInvolution (gradingMatrix n) := by
  exact gradingMatrix_sq n

/-- Every doubled directed spectroscopy operator is odd under the native
`Γ = diag(+I,-I)` grading. -/
theorem doubledOperator_odd
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) :
    OddUnderConjugation (gradingMatrix n) (doubledOperator K) := by
  exact grading_conjugates_doubledOperator_to_neg K

/-- The zero-energy one-mode Soloviev Hamiltonian is purely the odd CAR
interaction sector. -/
theorem zero_energy_coupledHamiltonian_eq_smul_interaction
    (v : ℝ) :
    coupledHamiltonian 0 v = v • interactionGenerator := by
  rw [coupledHamiltonian_eq_parameterHamiltonian]
  simp [parameterHamiltonian, oneModeHamiltonian]

/-- At zero diagonal energy the finite Soloviev Hamiltonian is Z₂-odd under
fermion parity. -/
theorem zero_energy_coupledHamiltonian_odd (v : ℝ) :
    OddUnderConjugation finiteParity (coupledHamiltonian 0 v) := by
  rw [zero_energy_coupledHamiltonian_eq_smul_interaction]
  exact odd_smul v interactionGenerator_odd

/-- Multiplicative form of the zero-diagonal nuclear grading law:

`Π_F H(0,v) Π_F = -H(0,v)`.
-/
theorem finiteParity_conjugates_zero_energy_to_neg (v : ℝ) :
    finiteParity * coupledHamiltonian 0 v * finiteParity =
      -coupledHamiltonian 0 v := by
  exact zero_energy_coupledHamiltonian_odd v

/-- Multiplicative form of the spectroscopy grading law:

`Γ D_K Γ = -D_K`.
-/
theorem spectroscopyGrading_conjugates_doubled_to_neg
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) :
    gradingMatrix n * doubledOperator K * gradingMatrix n =
      -doubledOperator K := by
  exact doubledOperator_odd K

/-- The two lanes instantiate exactly the same Z₂-odd conjugation predicate,
while remaining distinct representations. -/
theorem shared_Z2_odd_operator_packet
    {n : ℕ} (v : ℝ) (K : Matrix (Fin n) (Fin n) ℝ) :
    OddUnderConjugation finiteParity (coupledHamiltonian 0 v) ∧
      OddUnderConjugation (gradingMatrix n) (doubledOperator K) := by
  exact ⟨zero_energy_coupledHamiltonian_odd v, doubledOperator_odd K⟩

/-- Both grading operators are involutions, so both odd-sector sign flips are
implemented by genuine Z₂ conjugation actions. -/
theorem shared_Z2_involution_packet
    (n : ℕ) :
    IsInvolution finiteParity ∧ IsInvolution (gradingMatrix n) := by
  exact ⟨finiteParity_isInvolution, spectroscopyGrading_isInvolution n⟩

/-- Applying either grading conjugation twice returns the original odd
operator.  This is the common Z₂ action, stated without identifying carriers. -/
theorem shared_Z2_action_twice_packet
    {n : ℕ} (v : ℝ) (K : Matrix (Fin n) (Fin n) ℝ) :
    conjugate finiteParity
        (conjugate finiteParity (coupledHamiltonian 0 v)) =
          coupledHamiltonian 0 v ∧
      conjugate (gradingMatrix n)
        (conjugate (gradingMatrix n) (doubledOperator K)) =
          doubledOperator K := by
  constructor
  · exact conjugate_involutive finiteParity_isInvolution _
  · exact conjugate_involutive (spectroscopyGrading_isInvolution n) _

end InfoGeometry.Physics.NuclearSpectroscopyZ2GradingBridge

end noncomputable section
