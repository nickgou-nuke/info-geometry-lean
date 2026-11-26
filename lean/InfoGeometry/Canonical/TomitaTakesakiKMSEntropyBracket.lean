/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.TomitaTakesakiCommutantBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace TomitaTakesakiKMSEntropy

/-!
# Finite Real Matrix Commutator and Lindblad Trace-Zero Identities

Proves cyclic trace vanishing `trace ([H, ρ]) = 0` and
`trace (L ρ Lᵀ - (1/2) (Lᵀ L ρ + ρ Lᵀ L)) = 0` for real `n × n` matrices.
No differential equation `dρ/dt`, complex factor `-i`, modular automorphism flow,
or KMS state condition is formalized in this file.
-/

variable {n : ℕ}

/-- Matrix commutator bracket `[H, ρ] = H * ρ - ρ * H` on real `n × n` matrices. -/
def hamiltonianCommutator (H rho : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  H * rho - rho * H

/-- Trace of the matrix commutator vanishes: `trace ([H, ρ]) = 0`. -/
theorem hamiltonian_trace_nullity (H rho : Matrix (Fin n) (Fin n) ℝ) :
    trace (hamiltonianCommutator H rho) = 0 := by
  dsimp [hamiltonianCommutator]
  rw [trace_sub, trace_mul_comm H rho, sub_self]

/-- Real-matrix Lindblad dissipator expression `L * rho * Lᵀ - (1/2) • (Lᵀ * L * rho + rho * Lᵀ * L)`. -/
noncomputable def lindbladDissipator (L rho : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  L * rho * L.transpose - (1 / 2 : ℝ) • (L.transpose * L * rho + rho * L.transpose * L)

/-- Trace of `lindbladDissipator L rho` vanishes by cyclicity of the matrix trace. -/
theorem lindblad_trace_preservation (L rho : Matrix (Fin n) (Fin n) ℝ) :
    trace (lindbladDissipator L rho) = 0 := by
  dsimp [lindbladDissipator]
  have h_comm1 : trace (L * rho * L.transpose) = trace (L.transpose * L * rho) := by
    calc trace (L * rho * L.transpose) = trace (L.transpose * (L * rho)) := by rw [trace_mul_comm]
      _ = trace (L.transpose * L * rho) := by rw [Matrix.mul_assoc]
  have h_comm2 : trace (rho * L.transpose * L) = trace (L.transpose * L * rho) := by
    calc trace (rho * L.transpose * L) = trace (L * (rho * L.transpose)) := by rw [trace_mul_comm]
      _ = trace (L * rho * L.transpose) := by rw [← Matrix.mul_assoc]
      _ = trace (L.transpose * L * rho) := h_comm1
  rw [trace_sub, trace_smul, trace_add, h_comm2, h_comm1, smul_eq_mul]
  ring

/-- Trace of the sum `hamiltonianCommutator H rho + lindbladDissipator L rho` vanishes on real `n × n` matrices. -/
theorem metriplectic_total_trace_preservation (H L rho : Matrix (Fin n) (Fin n) ℝ) :
    trace (hamiltonianCommutator H rho + lindbladDissipator L rho) = 0 := by
  rw [trace_add, hamiltonian_trace_nullity, lindblad_trace_preservation, add_zero]

end TomitaTakesakiKMSEntropy
