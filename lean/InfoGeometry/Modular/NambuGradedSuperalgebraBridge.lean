import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.Modular.Graded

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "BlockMat" => Matrix (ι ⊕ ι) (ι ⊕ ι) R
local notation "SubMat" => Matrix ι ι R

/-- The Block Grading Operator: Γ = [[1, 0], [0, -1]]. -/
def Gamma : BlockMat :=
  fromBlocks (1 : SubMat) 0 0 (-1 : SubMat)

/-- The Identity matrix on the doubled space: I₂ₙ = [[1, 0], [0, 1]]. -/
def identityDoubled : BlockMat :=
  fromBlocks (1 : SubMat) 0 0 (1 : SubMat)

/-- Involutive property: Γ² = I. -/
theorem Gamma_sq : (Gamma : BlockMat) * Gamma = 1 := by
  dsimp [Gamma]
  rw [fromBlocks_multiply]
  simp only [mul_one, mul_zero, add_zero, mul_neg, neg_neg, zero_add]
  ext (i | i) (j | j)
  · simp [fromBlocks_apply₁₁, one_apply]
  · simp [fromBlocks_apply₁₂, zero_apply]
  · simp [fromBlocks_apply₂₁, zero_apply]
  · simp [fromBlocks_apply₂₂, one_apply]

/-- The Supertrace of a block matrix: STr(M) = Tr(M₁₁) - Tr(M₂₂). -/
def superTrace (M : BlockMat) : R :=
  Matrix.trace (toBlocks₁₁ M) - Matrix.trace (toBlocks₂₂ M)

@[simp]
theorem superTrace_fromBlocks (A B C D : SubMat) :
    superTrace (fromBlocks A B C D) = Matrix.trace A - Matrix.trace D := by
  dsimp [superTrace, toBlocks₁₁, toBlocks₂₂]

@[simp]
theorem trace_Gamma_zero :
    Matrix.trace (Gamma : BlockMat) = 0 := by
  dsimp [Gamma]
  have h : Matrix.trace (fromBlocks (1 : SubMat) 0 0 (-1 : SubMat)) =
      Matrix.trace (1 : SubMat) + Matrix.trace (-1 : SubMat) := by
    simp [Matrix.trace, Fintype.sum_sum_type]
  rw [h, Matrix.trace_one, Matrix.trace_neg, Matrix.trace_one]
  ring

@[simp]
theorem superTrace_identityDoubled_zero :
    superTrace (identityDoubled : BlockMat) = 0 := by
  dsimp [superTrace, identityDoubled, toBlocks₁₁, toBlocks₂₂]
  simp only [Matrix.trace_one]
  ring

/-- THEOREM: Supertrace of a block-diagonal commutator vanishes:
    STr([M, N]) = 0 for block-diagonal M, N. -/
theorem superTrace_block_commutator (A B C D : SubMat) :
    superTrace (fromBlocks A 0 0 D * fromBlocks B 0 0 C - fromBlocks B 0 0 C * fromBlocks A 0 0 D) = 0 := by
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [mul_zero, add_zero, zero_mul, zero_add]
  have h_sub : fromBlocks (A * B) 0 0 (D * C) - fromBlocks (B * A) 0 0 (C * D) =
      fromBlocks (A * B - B * A) 0 0 (D * C - C * D) := by
    rw [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp [sub_eq_add_neg]
  rw [h_sub, superTrace_fromBlocks]
  rw [Matrix.trace_sub, Matrix.trace_sub]
  rw [Matrix.trace_mul_comm A B, Matrix.trace_mul_comm D C]
  ring

/-!
=============================================================================
BdG PARTICLE-HOLE MATRIX HAMILTONIAN & EXACT ANTICOMMUTATION
=============================================================================
-/

/-- The BdG Hamiltonian as an exact Block Matrix:
    H_BdG(h, Δ, Δ†, -h†) = [[h, Δ], [Δ†, -h†]]. -/
def H_BdG (h Δ Δ_adj h_adj : SubMat) : BlockMat :=
  fromBlocks h Δ Δ_adj (-h_adj)

/-- The Particle-Hole Charge Conjugation Matrix C = [[0, c], [c, 0]]. -/
def C_mat (c : SubMat) : BlockMat :=
  fromBlocks 0 c c 0

/--
  MASTER THEOREM: BdG Particle-Hole Anticommutation on Block Matrices:
  C * H_BdG + H_BdG * C = 0
  under the standard component relations:
  c * h - h_adj * c = 0, c * Δ + Δ_adj * c = 0, c * Δ_adj + Δ * c = 0.
-/
theorem H_BdG_anticommutes_with_C (h Δ Δ_adj h_adj c : SubMat)
    (h_norm1 : c * h + (-h_adj) * c = 0)
    (h_norm2 : c * (-h_adj) + h * c = 0)
    (h_pair1 : c * Δ + Δ_adj * c = 0)
    (h_pair2 : c * Δ_adj + Δ * c = 0) :
    C_mat c * H_BdG h Δ Δ_adj h_adj + H_BdG h Δ Δ_adj h_adj * C_mat c = 0 := by
  dsimp [C_mat, H_BdG]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [zero_mul, add_zero, mul_zero, zero_add]
  rw [fromBlocks_add]
  ext (i | i) (j | j)
  · simp only [fromBlocks_apply₁₁, zero_apply]
    have h1 : (c * Δ_adj + Δ * c) i j = 0 := by rw [h_pair2]; rfl
    exact h1
  · simp only [fromBlocks_apply₁₂, zero_apply]
    have h2 : (c * (-h_adj) + h * c) i j = 0 := by rw [h_norm2]; rfl
    exact h2
  · simp only [fromBlocks_apply₂₁, zero_apply]
    have h3 : (c * h + (-h_adj) * c) i j = 0 := by rw [h_norm1]; rfl
    exact h3
  · simp only [fromBlocks_apply₂₂, zero_apply]
    have h4 : (c * Δ + Δ_adj * c) i j = 0 := by rw [h_pair1]; rfl
    exact h4

/-- Schur complement self-energy for block matrices: Σ(E) = h + Δ (E • I + h_adj)⁻¹ Δ† -/
def schurSelfEnergy (h Δ Δ_adj : SubMat) (resolvent : SubMat) : SubMat :=
  h + Δ * resolvent * Δ_adj

theorem schur_resolvent_identity (Δ Δ_adj resolvent E_h_adj : SubMat)
    (h_res : E_h_adj * resolvent = 1) :
    E_h_adj * (resolvent * Δ_adj) = Δ_adj := by
  rw [← mul_assoc, h_res, one_mul]

end InfoGeometry.Modular.Graded
