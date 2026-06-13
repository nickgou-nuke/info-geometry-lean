import Mathlib
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
  H_minus : MatC n
  H_plus : MatC n
  h_H_minus_def : H_minus = A_dag * A
  h_H_plus_def : H_plus = A * A_dag

namespace FiniteSUSYSystem

variable {n : ℕ} (sys : FiniteSUSYSystem n)

/-- Partner block intertwining: `A H₋ = H₊ A`. -/
theorem susy_partner_intertwining :
    sys.A * sys.H_minus = sys.H_plus * sys.A := by
  calc
    sys.A * sys.H_minus = sys.A * (sys.A_dag * sys.A) := by rw [sys.h_H_minus_def]
    _ = (sys.A * sys.A_dag) * sys.A := by rw [Matrix.mul_assoc]
    _ = sys.H_plus * sys.A := by rw [sys.h_H_plus_def]

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
  H_minus := H_minus
  H_plus := H_plus
  h_H_minus_def := rfl
  h_H_plus_def := rfl

/-- Concrete partner block intertwining. -/
theorem canonical_partner_intertwining :
    superchargeA * H_minus = H_plus * superchargeA :=
  canonicalFiniteSUSYSystem.susy_partner_intertwining

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
