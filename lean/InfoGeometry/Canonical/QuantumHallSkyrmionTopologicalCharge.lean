import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace QuantumHallSkyrmionTopologicalCharge

/-- SU(2) Non-Abelian Field Strength Representation in Mₙ(ℂ). -/
structure SkyrmionFieldStrength (n : ℕ) [DecidableEq (Fin n)] where
  field_tensor : Matrix (Fin n) (Fin n) ℂ

namespace SkyrmionFieldStrength

variable {n : ℕ} [DecidableEq (Fin n)] (F F1 F2 : SkyrmionFieldStrength n)

/-- Second Chern Class Skyrmion Charge Density: Tr(F * F). -/
def skyrmionDensity (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  trace (X * X)

/-- **Theorem**: Skyrmion Density Gauge Invariance under U ∈ U(n):
    Tr((U F U⁻¹)^²) = Tr(F²). -/
theorem skyrmion_density_gauge_invariance (U F_mat : Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : U.conjTranspose * U = 1) :
    trace ((U * F_mat * U.conjTranspose) * (U * F_mat * U.conjTranspose)) = trace (F_mat * F_mat) := by
  have h_assoc : (U * F_mat * U.conjTranspose) * (U * F_mat * U.conjTranspose) = U * (F_mat * (U.conjTranspose * U) * F_mat * U.conjTranspose) := by
    noncomm_ring
  rw [h_assoc, h_unitary]
  have h_simp : U * (F_mat * 1 * F_mat * U.conjTranspose) = U * (F_mat * F_mat) * U.conjTranspose := by
    noncomm_ring
  rw [h_simp, trace_mul_comm (U * (F_mat * F_mat)) U.conjTranspose]
  have h_simp2 : U.conjTranspose * (U * (F_mat * F_mat)) = (U.conjTranspose * U) * (F_mat * F_mat) := by
    noncomm_ring
  rw [h_simp2, h_unitary, one_mul]

/-- **Theorem**: Skyrmion Topological Charge Linear Additivity for Commuting Sectors:
    Tr((F₁ + F₂)^²) = Tr(F₁²) + Tr(F₂²) when Tr(F₁ F₂) = 0. -/
theorem skyrmion_charge_additivity (F1_mat F2_mat : Matrix (Fin n) (Fin n) ℂ)
    (h_ortho : trace (F1_mat * F2_mat) = 0) (h_ortho_rev : trace (F2_mat * F1_mat) = 0) :
    skyrmionDensity (F1_mat + F2_mat) = skyrmionDensity F1_mat + skyrmionDensity F2_mat := by
  dsimp [skyrmionDensity]
  rw [add_mul, mul_add, mul_add, trace_add, trace_add, trace_add, h_ortho, h_ortho_rev]
  ring

end SkyrmionFieldStrength

end QuantumHallSkyrmionTopologicalCharge
