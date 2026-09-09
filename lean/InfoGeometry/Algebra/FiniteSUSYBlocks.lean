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
  simp only [H_minus, H_plus, Matrix.mul_assoc]

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

/-- Concrete odd-odd anticommutator equals H₊+H₋. -/
theorem canonical_odd_anticommutator_is_even_sum :
    superchargeA * superchargeAdag + superchargeAdag * superchargeA = H_plus + H_minus := by
  simp [H_plus, H_minus, add_comm, add_left_comm, add_assoc]

/-- Fermion-parity grading on the two-state block. -/
def fermionParity : MatC 2 :=
  !![1, 0;
     0, -1]

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
