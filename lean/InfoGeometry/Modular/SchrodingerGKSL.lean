import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Schrödinger-Picture GKSL Generator and Exact Trace Preservation

This module formalizes:
1. The Schrödinger-picture dual Lindblad generator acting on density operators:
     ℒ†(ρ) = -i • [H, ρ] + ∑_k ( V_k ρ V_k† - (1/2) {V_k† V_k, ρ} )
2. Proven cyclic trace cancellation for the Hamiltonian commutator:
     Tr([H, ρ]) = 0
3. Proven exact trace cancellation for every Lindblad jump channel:
     Tr(V_k ρ V_k† - (1/2) {V_k† V_k, ρ}) = 0
4. Complete Schrödinger Trace Preservation:
     Tr(ℒ†(ρ)) = 0  for all density matrices ρ.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open Matrix
open BigOperators
open Finset

namespace InfoGeometry.Modular.SchrodingerGKSL

variable {n : Type*} [Fintype n]

local notation "Mat" => Matrix n n ℂ

/-!
=============================================================================
PART 1: Hamiltonian Commutator Trace Cancellation
=============================================================================
-/

/-- The Unitary/Hamiltonian part of the Schrödinger generator: -i • [H, ρ]. -/
def hamiltonianTerm (H ρ : Mat) : Mat :=
  - Complex.I • (H * ρ - ρ * H)

/-- 
  THEOREM 1: The Trace of the Hamiltonian Commutator Strictly Vanishes:
  Tr(-i • [H, ρ]) = 0
  Proven natively via the cyclic property of the trace (Tr(AB) = Tr(BA)).
-/
@[simp]
theorem trace_hamiltonianTerm_zero (H ρ : Mat) :
    Matrix.trace (hamiltonianTerm H ρ) = 0 := by
  dsimp [hamiltonianTerm]
  rw [Matrix.trace_smul, Matrix.trace_sub]
  rw [Matrix.trace_mul_comm H ρ]
  simp only [sub_self, smul_zero]

/-!
=============================================================================
PART 2: Single-Channel Dissipative Trace Cancellation
=============================================================================
-/

/-- 
  The Schrödinger-picture single-channel dissipator:
  𝒟†_V(ρ) = V ρ V† - (1/2) • (V† V ρ + ρ V† V)
-/
def schrodingerDissipatorTerm (V_k ρ : Mat) : Mat :=
  V_k * ρ * star V_k - (1 / 2 : ℂ) • (star V_k * V_k * ρ + ρ * star V_k * V_k)

/-- 
  THEOREM 2: The Trace of each Lindblad Dissipator Term is Identically Zero:
  Tr(V ρ V† - (1/2) {V† V, ρ}) = 0
-/
@[simp]
theorem trace_schrodingerDissipatorTerm_zero (V_k ρ : Mat) :
    Matrix.trace (schrodingerDissipatorTerm V_k ρ) = 0 := by
  dsimp [schrodingerDissipatorTerm]
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  
  -- Cyclic permutations of the trace
  have h_cyc1 : Matrix.trace (V_k * ρ * star V_k) = Matrix.trace (star V_k * V_k * ρ) := by
    calc
      Matrix.trace (V_k * ρ * star V_k) = Matrix.trace (star V_k * (V_k * ρ)) := by
        exact Matrix.trace_mul_comm (V_k * ρ) (star V_k)
      _ = Matrix.trace (star V_k * V_k * ρ) := by
        simp only [mul_assoc]
  
  have h_cyc2 : Matrix.trace (ρ * star V_k * V_k) = Matrix.trace (star V_k * V_k * ρ) := by
    calc
      Matrix.trace (ρ * star V_k * V_k) = Matrix.trace (ρ * (star V_k * V_k)) := by
        simp only [mul_assoc]
      _ = Matrix.trace (star V_k * V_k * ρ) := by
        exact Matrix.trace_mul_comm ρ (star V_k * V_k)
  
  rw [h_cyc1, h_cyc2]
  ring

/-!
=============================================================================
PART 3: Full Multichannel Generator and Total Trace Preservation
=============================================================================
-/

variable {ι : Type*} [Fintype ι]

/-- The Full Multichannel Schrödinger Dissipator: 𝒟†(ρ) = ∑_k 𝒟†_{V_k}(ρ). -/
def schrodingerDissipator (V : ι → Mat) (ρ : Mat) : Mat :=
  ∑ k, schrodingerDissipatorTerm (V k) ρ

/-- 
  The Complete Schrödinger-Picture GKSL Lindbladian:
  ℒ†(ρ) = -i • [H, ρ] + ∑_k ( V_k ρ V_k† - (1/2) {V_k† V_k, ρ} )
-/
def schrodingerLindbladian (H : Mat) (V : ι → Mat) (ρ : Mat) : Mat :=
  hamiltonianTerm H ρ + schrodingerDissipator V ρ

/-- 
  MASTER THEOREM: Total Quantum Probability / Trace Preservation:
  Tr(ℒ†(ρ)) = 0  for ANY density matrix ρ.
-/
@[simp]
theorem trace_schrodingerLindbladian_zero (H : Mat) (V : ι → Mat) (ρ : Mat) :
    Matrix.trace (schrodingerLindbladian H V ρ) = 0 := by
  dsimp [schrodingerLindbladian, schrodingerDissipator]
  rw [Matrix.trace_add, trace_hamiltonianTerm_zero, zero_add]
  rw [Matrix.trace_sum]
  have h_all_zero : ∀ k ∈ (Finset.univ : Finset ι),
      Matrix.trace (schrodingerDissipatorTerm (V k) ρ) = 0 := by
    intro k _
    exact trace_schrodingerDissipatorTerm_zero (V k) ρ
  rw [Finset.sum_congr rfl h_all_zero, Finset.sum_const_zero]

end InfoGeometry.Modular.SchrodingerGKSL

end noncomputable section
