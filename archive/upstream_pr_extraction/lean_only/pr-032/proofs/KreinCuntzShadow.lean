import Mathlib
import proofs.SolovievQPNMChiralCuntz
import proofs.FiniteMatrixElementDuality
import proofs.FierzIdentities
import proofs.Cl11ChiralCARBridge

/-!
# Krein--Cuntz finite shadow

This file welds the finite chiral Cuntz/CAR matrix-unit shadow to the finite
matrix-element/Krein observable layer.

The proved content is deliberately finite:

* the odd chiral generators are nilpotent matrix units;
* their loops give the even projectors;
* `η = diag(1,-1)` is a strict involution;
* the Krein adjoint is `A ↦ η A† η`;
* on the chiral generators this sends `Splus ↦ -Sminus` and
  `Sminus ↦ -Splus`;
* all basis matrix elements reconstruct the operator;
* finite swap covariance preserves transition probabilities.

-/

noncomputable section

namespace KreinCuntzShadow

abbrev V2C := FiniteMatrixElementDuality.V2C
abbrev M2C := FiniteMatrixElementDuality.M2C

/-- The finite indefinite metric / fundamental Krein symmetry. -/
def eta : M2C := FiniteMatrixElementDuality.J

/-- Chiral odd generator. -/
def Splus : M2C := SolovievQPNMChiralCuntz.Splus

/-- Opposite chiral odd generator. -/
def Sminus : M2C := SolovievQPNMChiralCuntz.Sminus

/-- Even projector `Nplus = Splus*Sminus`. -/
def Nplus : M2C := SolovievQPNMChiralCuntz.Nplus

/-- Even projector `Nminus = Sminus*Splus`. -/
def Nminus : M2C := SolovievQPNMChiralCuntz.Nminus

/-- Finite matrix element `<bra|A|ket>`. -/
def matrixElement : V2C → M2C → V2C → ℂ := FiniteMatrixElementDuality.matrixElement

/-- Finite transition probability. -/
def transitionProbability : V2C → M2C → V2C → ℝ :=
  FiniteMatrixElementDuality.transitionProbability

/-- Krein adjoint `A^× = η A† η`. -/
def kreinAdjoint : M2C → M2C := FiniteMatrixElementDuality.kreinAdjoint

/-- The finite Krein metric is an involution. -/
theorem eta_sq : eta * eta = (1 : M2C) := by
  exact FiniteMatrixElementDuality.J_sq

/-- `Splus` is nilpotent: finite Pauli exclusion. -/
theorem Splus_nilpotent : Splus * Splus = 0 := by
  exact SolovievQPNMChiralCuntz.Splus_nilpotent

/-- `Sminus` is nilpotent. -/
theorem Sminus_nilpotent : Sminus * Sminus = 0 := by
  exact SolovievQPNMChiralCuntz.Sminus_nilpotent

/-- Odd loop closes to `Nplus`. -/
theorem Splus_mul_Sminus_eq_Nplus : Splus * Sminus = Nplus := by
  exact SolovievQPNMChiralCuntz.Splus_mul_Sminus_eq_Nplus

/-- Reverse odd loop closes to `Nminus`. -/
theorem Sminus_mul_Splus_eq_Nminus : Sminus * Splus = Nminus := by
  exact SolovievQPNMChiralCuntz.Sminus_mul_Splus_eq_Nminus

/-- Completeness of the finite chiral matrix-unit shadow. -/
theorem chiral_completeness : Splus * Sminus + Sminus * Splus = (1 : M2C) := by
  exact SolovievQPNMChiralCuntz.chiral_completeness

/-- The finite shadow is not a literal finite `O₂` isometry: `Splus† Splus = Nminus`. -/
theorem Splus_adjoint_times_Splus : Matrix.conjTranspose Splus * Splus = Nminus := by
  exact SolovievQPNMChiralCuntz.Splus_adjoint_times_Splus

/-- Similarly `Sminus† Sminus = Nplus`. -/
theorem Sminus_adjoint_times_Sminus : Matrix.conjTranspose Sminus * Sminus = Nplus := by
  exact SolovievQPNMChiralCuntz.Sminus_adjoint_times_Sminus

/-- Krein adjoint sends `Splus` to `-Sminus`. -/
theorem kreinAdjoint_Splus : kreinAdjoint Splus = -Sminus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kreinAdjoint, FiniteMatrixElementDuality.kreinAdjoint, eta, Splus, Sminus,
      FiniteMatrixElementDuality.J, SolovievQPNMChiralCuntz.Splus,
      SolovievQPNMChiralCuntz.Sminus, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

/-- Krein adjoint sends `Sminus` to `-Splus`. -/
theorem kreinAdjoint_Sminus : kreinAdjoint Sminus = -Splus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kreinAdjoint, FiniteMatrixElementDuality.kreinAdjoint, eta, Splus, Sminus,
      FiniteMatrixElementDuality.J, SolovievQPNMChiralCuntz.Splus,
      SolovievQPNMChiralCuntz.Sminus, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

/-- Even projectors are fixed by the Krein adjoint. -/
theorem kreinAdjoint_Nplus : kreinAdjoint Nplus = Nplus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kreinAdjoint, FiniteMatrixElementDuality.kreinAdjoint, eta, Nplus,
      FiniteMatrixElementDuality.J, SolovievQPNMChiralCuntz.Nplus,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

/-- The other even projector is also fixed. -/
theorem kreinAdjoint_Nminus : kreinAdjoint Nminus = Nminus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kreinAdjoint, FiniteMatrixElementDuality.kreinAdjoint, eta, Nminus,
      FiniteMatrixElementDuality.J, SolovievQPNMChiralCuntz.Nminus,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

/-- Matrix elements of the basis kets recover operator entries. -/
theorem matrixElement_basis_entry (A : M2C) (i j : Fin 2) :
    matrixElement (fun a => if a = i then 1 else 0) A (fun b => if b = j then 1 else 0) = A i j := by
  exact FiniteMatrixElementDuality.matrixElement_basis_entry A i j

/-- Complete finite measurement table reconstructs the operator. -/
theorem operator_ext_from_matrix_elements {A B : M2C}
    (h : ∀ i j : Fin 2,
      matrixElement (fun a => if a = i then 1 else 0) A (fun b => if b = j then 1 else 0) =
      matrixElement (fun a => if a = i then 1 else 0) B (fun b => if b = j then 1 else 0)) :
    A = B := by
  exact FiniteMatrixElementDuality.operator_ext_from_matrix_elements h

/-- Matrix elements are linear in the operator. -/
theorem matrixElement_add (bra ket : V2C) (A B : M2C) :
    matrixElement bra (A + B) ket = matrixElement bra A ket + matrixElement bra B ket := by
  exact FiniteMatrixElementDuality.matrixElement_add bra ket A B

/-- Matrix elements are scalar-linear in the operator. -/
theorem matrixElement_smul (bra ket : V2C) (c : ℂ) (A : M2C) :
    matrixElement bra (c • A) ket = c * matrixElement bra A ket := by
  exact FiniteMatrixElementDuality.matrixElement_smul bra ket c A

/-- Finite swap covariance of matrix elements. -/
theorem swap_covariance (bra ket : V2C) (A : M2C) :
    matrixElement (FiniteMatrixElementDuality.swapState bra)
      (FiniteMatrixElementDuality.swapOperator A)
      (FiniteMatrixElementDuality.swapState ket) = matrixElement bra A ket := by
  exact FiniteMatrixElementDuality.swap_covariance bra ket A

/-- Finite swap invariance of transition probabilities. -/
theorem swap_transitionProbability_invariant (bra ket : V2C) (A : M2C) :
    transitionProbability (FiniteMatrixElementDuality.swapState bra)
      (FiniteMatrixElementDuality.swapOperator A)
      (FiniteMatrixElementDuality.swapState ket) = transitionProbability bra A ket := by
  exact FiniteMatrixElementDuality.swap_transitionProbability_invariant bra ket A

/-- Synthesis: the finite Krein--Cuntz shadow is closed. -/
theorem krein_cuntz_shadow_synthesis :
    eta * eta = (1 : M2C) ∧
    Splus * Splus = 0 ∧
    Sminus * Sminus = 0 ∧
    Splus * Sminus = Nplus ∧
    Sminus * Splus = Nminus ∧
    Splus * Sminus + Sminus * Splus = (1 : M2C) ∧
    Matrix.conjTranspose Splus * Splus = Nminus ∧
    Matrix.conjTranspose Sminus * Sminus = Nplus ∧
    kreinAdjoint Splus = -Sminus ∧
    kreinAdjoint Sminus = -Splus ∧
    kreinAdjoint Nplus = Nplus ∧
    kreinAdjoint Nminus = Nminus ∧
    (∀ A B : M2C,
      (∀ i j : Fin 2,
        matrixElement (fun a => if a = i then 1 else 0) A (fun b => if b = j then 1 else 0) =
        matrixElement (fun a => if a = i then 1 else 0) B (fun b => if b = j then 1 else 0)) → A = B) := by
  exact ⟨eta_sq, Splus_nilpotent, Sminus_nilpotent, Splus_mul_Sminus_eq_Nplus,
    Sminus_mul_Splus_eq_Nminus, chiral_completeness, Splus_adjoint_times_Splus,
    Sminus_adjoint_times_Sminus, kreinAdjoint_Splus, kreinAdjoint_Sminus,
    kreinAdjoint_Nplus, kreinAdjoint_Nminus,
    (fun A B h => operator_ext_from_matrix_elements h)⟩

end KreinCuntzShadow
