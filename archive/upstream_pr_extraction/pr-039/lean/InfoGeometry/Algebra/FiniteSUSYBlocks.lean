import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite SUSY block algebra

Reusable finite matrix layer for a pair of supercharges `A`, `A†` and the
partner blocks `H₋ = A†A`, `H₊ = AA†`.

The theorem surface is purely finite algebra: associativity gives the partner
intertwining identity, and the concrete two-state block has zero Witten-trace
imbalance.  No spectral theorem, completion theorem, or model-realization claim
is asserted.
-/

noncomputable section

namespace InfoGeometry.Algebra.FiniteSUSY

open Matrix
open InfoGeometry.Algebra.FiniteSpin

/-- Complex `n × n` matrices. -/
abbrev MatC (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Finite supercharge block system. -/
structure FiniteSUSYSystem (n : ℕ) where
  A : MatC n
  A_dag : MatC n

namespace FiniteSUSYSystem

variable {n : ℕ} (sys : FiniteSUSYSystem n)

/-- The negative partner Hamiltonian is canonically `A†A`. -/
def H_minus : MatC n :=
  sys.A_dag * sys.A

/-- The positive partner Hamiltonian is canonically `AA†`. -/
def H_plus : MatC n :=
  sys.A * sys.A_dag

/-- `H₋` unfolds to the product `A†A`. -/
@[simp]
theorem h_H_minus_def :
    sys.H_minus = sys.A_dag * sys.A := rfl

/-- `H₊` unfolds to the product `AA†`. -/
@[simp]
theorem h_H_plus_def :
    sys.H_plus = sys.A * sys.A_dag := rfl

/-- Partner block intertwining: `A H₋ = H₊ A`. -/
theorem susy_partner_intertwining :
    sys.A * sys.H_minus = sys.H_plus * sys.A := by
  change sys.A * (sys.A_dag * sys.A) =
    (sys.A * sys.A_dag) * sys.A
  exact (mul_assoc sys.A sys.A_dag sys.A).symm

/-- Reverse partner intertwining: `A† H₊ = H₋ A†`. -/
theorem reverse_partner_intertwining :
    sys.A_dag * sys.H_plus = sys.H_minus * sys.A_dag := by
  change sys.A_dag * (sys.A * sys.A_dag) =
    (sys.A_dag * sys.A) * sys.A_dag
  exact (mul_assoc sys.A_dag sys.A sys.A_dag).symm

/-- Finite partner blocks have equal ordinary trace. -/
theorem partner_trace_balance :
    Matrix.trace sys.H_minus = Matrix.trace sys.H_plus := by
  simpa [H_minus, H_plus] using
    (Matrix.trace_mul_comm sys.A_dag sys.A)

theorem trace_h_minus_sub_h_plus :
    Matrix.trace (sys.H_minus - sys.H_plus) = 0 := by
  rw [Matrix.trace_sub, sys.partner_trace_balance]
  exact sub_self _

/-- `H₋` is exactly the product `A†A`. -/
theorem h_minus_is_product :
    sys.H_minus = sys.A_dag * sys.A := rfl

/-- `H₊` is exactly the product `AA†`. -/
theorem h_plus_is_product :
    sys.H_plus = sys.A * sys.A_dag := rfl

/-- The odd-odd anticommutator is exactly the even-slab sum: `{A,A†} = H₊ + H₋`. -/
theorem odd_anticommutator_is_even_sum :
    sys.A * sys.A_dag + sys.A_dag * sys.A = sys.H_plus + sys.H_minus := by
  rfl

end FiniteSUSYSystem

/-- The algebraic system together with a proof that `A_dag` is the matrix adjoint. -/
def FiniteSUSYSystem.IsAdjointPair
    {n : ℕ} (sys : FiniteSUSYSystem n) : Prop :=
  sys.A_dag = sys.Aᴴ

/-- A finite SUSY system whose adjoint partner is defined canonically. -/
structure AdjointFiniteSUSYSystem (n : ℕ) where
  A : MatC n

namespace AdjointFiniteSUSYSystem

variable {n : ℕ} (sys : AdjointFiniteSUSYSystem n)

def A_dag : MatC n := sys.Aᴴ

def H_minus : MatC n := sys.Aᴴ * sys.A

def H_plus : MatC n := sys.A * sys.Aᴴ

@[simp] theorem adjoint_pair : sys.A_dag = sys.Aᴴ := rfl

theorem partner_trace_balance :
    Matrix.trace sys.H_minus = Matrix.trace sys.H_plus := by
  simpa [H_minus, H_plus] using Matrix.trace_mul_comm sys.Aᴴ sys.A

end AdjointFiniteSUSYSystem

/-- Concrete lowering supercharge. -/
def superchargeA : MatC 2 :=
  J_minus

/-- Concrete raising supercharge. -/
def superchargeAdag : MatC 2 :=
  J_plus

/-- Concrete finite partner block `H₋ = A†A`. -/
def H_minus : MatC 2 :=
  superchargeAdag * superchargeA

/-- Concrete finite partner block `H₊ = AA†`. -/
def H_plus : MatC 2 :=
  superchargeA * superchargeAdag

/-- Concrete finite SUSY block system from the spin-half ladder operators. -/
def canonicalFiniteSUSYSystem : FiniteSUSYSystem 2 where
  A := superchargeA
  A_dag := superchargeAdag

/-- Concrete partner block intertwining. -/
theorem canonical_partner_intertwining :
    superchargeA * H_minus = H_plus * superchargeA :=
  canonicalFiniteSUSYSystem.susy_partner_intertwining

/-- Concrete supercharge square-zero for lowering charge. -/
theorem canonical_supercharge_square_zero :
    superchargeA * superchargeA = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [superchargeA, J_minus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete supercharge square-zero for raising charge. -/
theorem canonical_adjoint_supercharge_square_zero :
    superchargeAdag * superchargeAdag = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [superchargeAdag, J_plus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem canonical_adjoint_law :
    superchargeAᴴ = superchargeAdag := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [superchargeA, superchargeAdag, J_minus, J_plus]

@[simp] theorem canonical_H_minus_explicit :
    H_minus = !![(1 : ℂ), 0; 0, 0] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [H_minus, superchargeA, superchargeAdag, J_minus, J_plus,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem canonical_H_plus_explicit :
    H_plus = !![0, 0; 0, (1 : ℂ)] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [H_plus, superchargeA, superchargeAdag, J_minus, J_plus,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem canonical_anticommutator_eq_one :
    superchargeA * superchargeAdag + superchargeAdag * superchargeA =
      (1 : MatC 2) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [superchargeA, superchargeAdag, J_minus, J_plus,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem canonical_H_minus_add_H_plus :
    H_minus + H_plus = (1 : MatC 2) := by
  rw [canonical_H_minus_explicit, canonical_H_plus_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp

/-- Concrete odd-odd anticommutator equals H₊+H₋. -/
theorem canonical_odd_anticommutator_is_even_sum :
    superchargeA * superchargeAdag + superchargeAdag * superchargeA = H_plus + H_minus := by
  simp [H_plus, H_minus, add_comm, add_left_comm, add_assoc]

/-- Fermion-parity grading on the two-state block. -/
def fermionParity : MatC 2 :=
  !![1, 0;
     0, -1]

@[simp] theorem fermionParity_sq :
    fermionParity * fermionParity = (1 : MatC 2) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [fermionParity, Matrix.mul_apply, Fin.sum_univ_two]

theorem fermionParity_anticomm_superchargeA :
    fermionParity * superchargeA + superchargeA * fermionParity = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [fermionParity, superchargeA, J_minus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem fermionParity_anticomm_superchargeAdag :
    fermionParity * superchargeAdag + superchargeAdag * fermionParity = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [fermionParity, superchargeAdag, J_plus,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem fermionParity_star :
    fermionParityᴴ = fermionParity := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fermionParity]

theorem fermionParity_commutes_H_minus :
    fermionParity * H_minus = H_minus * fermionParity := by
  rw [canonical_H_minus_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fermionParity, Matrix.mul_apply, Fin.sum_univ_two]

theorem fermionParity_commutes_H_plus :
    fermionParity * H_plus = H_plus * fermionParity := by
  rw [canonical_H_plus_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fermionParity, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem canonical_H_minus_sq :
    H_minus * H_minus = H_minus := by
  rw [canonical_H_minus_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem canonical_H_plus_sq :
    H_plus * H_plus = H_plus := by
  rw [canonical_H_plus_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem canonical_H_minus_mul_H_plus :
    H_minus * H_plus = 0 := by
  rw [canonical_H_minus_explicit, canonical_H_plus_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem canonical_H_plus_mul_H_minus :
    H_plus * H_minus = 0 := by
  rw [canonical_H_plus_explicit, canonical_H_minus_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem fermionParity_eq_partner_difference :
    fermionParity = H_minus - H_plus := by
  rw [canonical_H_minus_explicit, canonical_H_plus_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fermionParity]

/-- Finite Witten trace of a diagonal two-state occupancy. -/
def finiteWittenTrace (nB nF : ℂ) : ℂ :=
  Matrix.trace (fermionParity * !![nB, 0; 0, nF])

/-- The finite Witten trace is boson count minus fermion count. -/
theorem finiteWittenTrace_eq (nB nF : ℂ) :
    finiteWittenTrace nB nF = nB - nF := by
  simp [finiteWittenTrace, fermionParity, Matrix.trace, Fin.sum_univ_two]
  ring

/-- Equal finite boson/fermion occupancy has zero Witten trace. -/
theorem finiteWittenTrace_eq_zero_of_equal (n : ℂ) :
    finiteWittenTrace n n = 0 := by
  rw [finiteWittenTrace_eq]
  ring

/-- Consolidated finite SUSY block packet. -/
theorem finite_susy_block_packet :
    superchargeA * H_minus = H_plus * superchargeA ∧
      finiteWittenTrace 1 1 = 0 := by
  exact ⟨canonical_partner_intertwining, by simpa using finiteWittenTrace_eq_zero_of_equal 1⟩

end InfoGeometry.Algebra.FiniteSUSY

end noncomputable section
