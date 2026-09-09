import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import InfoGeometry.Algebra.FiniteSUSYBlocks
import InfoGeometry.Physics.SplitCliffordAlgebras
import InfoGeometry.OperatorAlgebra.ChiralRetainedWordFiveGradeClosure

/-!
# Finite one-mode CAR moment SDP

This owner is the first exact operator-to-convex vertical slice.

The noncommutative input is the concrete one-mode CAR representation already
owned by `InfoGeometry.Algebra.FiniteSUSY`.  For the normalized diagonal state

`rho(p) = diag(p, 1 - p)`,

the word lists `(1, a)` and `(1, a_dag)` produce the real moment matrices

`diag(1, p)` and `diag(1, 1 - p)`.

For `0 <= p <= 1` both matrices are positive semidefinite.  The expectation
of the number operator `a_dag * a` is exactly `p`, so the resulting
one-variable semidefinite problem has exact optimum zero, attained by the
vacuum parameter `p = 0`, with the matching dual lower bound zero.

This is a finite exact SDP instance.  It does not assert that a general
noncommutative polynomial problem has a finite exact relaxation.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteCAROneModeSDP

open Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Algebra.FiniteSUSY

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The annihilation operator inherited from the finite SUSY owner. -/
def annihilation : Mat2C :=
  superchargeA

/-- The creation operator inherited from the finite SUSY owner. -/
def creation : Mat2C :=
  superchargeAdag

/-- The one-mode fermion number operator `N = a_dag a`. -/
def numberOperator : Mat2C :=
  creation * annihilation

/-- The complementary occupation operator `1 - N = a a_dag`. -/
def complementaryNumberOperator : Mat2C :=
  annihilation * creation

@[simp] theorem annihilation_sq_zero :
    annihilation * annihilation = 0 := by
  exact canonical_supercharge_square_zero

@[simp] theorem creation_sq_zero :
    creation * creation = 0 := by
  exact canonical_adjoint_supercharge_square_zero

@[simp] theorem creation_eq_adjoint :
    annihilationᴴ = creation := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [annihilation, creation, superchargeA, superchargeAdag, J_minus, J_plus]

@[simp] theorem car_identity :
    annihilation * creation + creation * annihilation = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [annihilation, creation, superchargeA, superchargeAdag, J_minus, J_plus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite matrix model is an instance of the repository-wide CAR packet.
This is the structural wire to the Clifford/operator-algebra lane; it adds no
new relations beyond the three native matrix proofs above. -/
noncomputable def carPair : SplitClifford.CARPair Mat2C where
  ann := annihilation
  cre := creation
  ann_sq := annihilation_sq_zero
  cre_sq := creation_sq_zero
  anti := car_identity

@[simp] theorem carPair_ann : carPair.ann = annihilation := rfl

@[simp] theorem carPair_cre : carPair.cre = creation := rfl

theorem number_add_complementary_eq_one :
    numberOperator + complementaryNumberOperator = 1 := by
  simpa [numberOperator, complementaryNumberOperator, add_comm] using car_identity

@[simp] theorem numberOperator_explicit :
    numberOperator = !![(1 : ℂ), 0; 0, 0] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [numberOperator, creation, annihilation, superchargeA, superchargeAdag,
      J_minus, J_plus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem complementaryNumberOperator_explicit :
    complementaryNumberOperator = !![0, 0; 0, (1 : ℂ)] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [complementaryNumberOperator, creation, annihilation, superchargeA,
      superchargeAdag, J_minus, J_plus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Normalized diagonal one-mode state, with occupation parameter `p`. -/
def density (p : ℝ) : Mat2C :=
  !![(p : ℂ), 0; 0, ((1 - p : ℝ) : ℂ)]

@[simp] theorem density_trace (p : ℝ) :
    Matrix.trace (density p) = 1 := by
  simp [density, Matrix.trace, Fin.sum_univ_two]

/-- Operator expectation before taking a real readout. -/
def expectation (p : ℝ) (X : Mat2C) : ℂ :=
  Matrix.trace (density p * X)

@[simp] theorem expectation_numberOperator (p : ℝ) :
    expectation p numberOperator = (p : ℂ) := by
  rw [numberOperator_explicit]
  simp [expectation, density, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem expectation_complementaryNumberOperator (p : ℝ) :
    expectation p complementaryNumberOperator = ((1 - p : ℝ) : ℂ) := by
  rw [complementaryNumberOperator_explicit]
  simp [expectation, density, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Truncated noncommutative word list `(1, a)`. -/
def annihilationWord : Fin 2 → Mat2C
  | 0 => 1
  | 1 => annihilation

/-- Truncated noncommutative word list `(1, a_dag)`. -/
def creationWord : Fin 2 → Mat2C
  | 0 => 1
  | 1 => creation

/-- Real readout of `L_p(w_i^* w_j)` for the word list `(1, a)`. -/
def annihilationMomentMatrix (p : ℝ) : Mat2R :=
  fun i j =>
    (expectation p ((annihilationWord i)ᴴ * annihilationWord j)).re

/-- Real readout of `L_p(w_i^* w_j)` for the word list `(1, a_dag)`. -/
def creationMomentMatrix (p : ℝ) : Mat2R :=
  fun i j =>
    (expectation p ((creationWord i)ᴴ * creationWord j)).re

theorem annihilationMomentMatrix_eq_diagonal (p : ℝ) :
    annihilationMomentMatrix p = Matrix.diagonal ![1, p] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [annihilationMomentMatrix, annihilationWord, expectation, density,
      annihilation, creation, superchargeA, superchargeAdag, J_minus, J_plus,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num [Complex.ext_iff, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply,
      Matrix.vecMul, dotProduct]

theorem creationMomentMatrix_eq_diagonal (p : ℝ) :
    creationMomentMatrix p = Matrix.diagonal ![1, 1 - p] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [creationMomentMatrix, creationWord, expectation, density,
      annihilation, creation, superchargeA, superchargeAdag, J_minus, J_plus,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num [Complex.ext_iff, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply,
      Matrix.vecMul, dotProduct]

theorem annihilationMomentMatrix_posSemidef
    {p : ℝ} (hp : 0 ≤ p) :
    (annihilationMomentMatrix p).PosSemidef := by
  rw [annihilationMomentMatrix_eq_diagonal]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x
    simp [dotProduct, mulVec, Matrix.diagonal, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

theorem creationMomentMatrix_posSemidef
    {p : ℝ} (hp : p ≤ 1) :
    (creationMomentMatrix p).PosSemidef := by
  rw [creationMomentMatrix_eq_diagonal]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x
    have h : 0 ≤ 1 - p := sub_nonneg.mpr hp
    simp [dotProduct, mulVec, Matrix.diagonal, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- Feasibility of the exact one-mode moment relaxation. -/
def IsFeasible (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1

theorem feasible_moment_matrices {p : ℝ} (hp : IsFeasible p) :
    (annihilationMomentMatrix p).PosSemidef ∧
      (creationMomentMatrix p).PosSemidef := by
  exact ⟨annihilationMomentMatrix_posSemidef hp.1,
    creationMomentMatrix_posSemidef hp.2⟩

/-- SDP objective: the real expectation of the number operator. -/
def objective (p : ℝ) : ℝ :=
  (expectation p numberOperator).re

@[simp] theorem objective_eq (p : ℝ) :
    objective p = p := by
  rw [objective, expectation_numberOperator]
  rfl

/-- The vacuum parameter is a feasible primal point. -/
theorem vacuum_feasible : IsFeasible 0 := by
  constructor <;> norm_num

/-- Every feasible moment point obeys the certified lower bound zero. -/
theorem objective_nonneg_of_feasible {p : ℝ} (hp : IsFeasible p) :
    0 ≤ objective p := by
  simpa [objective_eq] using hp.1

/-- The vacuum attains the lower bound. -/
@[simp] theorem vacuum_objective :
    objective 0 = 0 := by
  simp

/-- Exact dual lower bound for the one-mode SDP. -/
def dualLowerBound : ℝ :=
  0

theorem dualLowerBound_valid {p : ℝ} (hp : IsFeasible p) :
    dualLowerBound ≤ objective p := by
  exact objective_nonneg_of_feasible hp

/-- The primal vacuum and dual lower bound have zero duality gap. -/
theorem primal_dual_gap_zero :
    objective 0 - dualLowerBound = 0 := by
  simp [dualLowerBound]

/--
Exact one-mode CAR ground-state result:
the feasible objective is bounded below by zero and the vacuum attains zero.
-/
theorem exact_ground_state_optimum :
    IsFeasible 0 ∧ objective 0 = 0 ∧
      ∀ p : ℝ, IsFeasible p → objective 0 ≤ objective p := by
  refine ⟨vacuum_feasible, vacuum_objective, ?_⟩
  intro p hp
  simpa using objective_nonneg_of_feasible hp

end InfoGeometry.OperatorAlgebra.FiniteCAROneModeSDP

end noncomputable section
