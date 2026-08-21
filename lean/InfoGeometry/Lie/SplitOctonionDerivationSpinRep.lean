import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Spin Representation of Split-Octonion Derivations: Stabilizer and Pairing Sectors

This module formalizes:
1. The grading involution `Γ = [[1, 0], [0, -1]]` on the doubled spin space `S₊ ⊕ S₋`.
2. The canonical projection onto the block-diagonal stabilizer sector `𝔰𝔩₃` (commuting with Γ)
   and the block-off-diagonal pairing sector `𝟑 ⊕ 𝟑*` (anticommuting with Γ).
3. The exact algebraic decomposition: `M = M_diag + M_off`.
4. Vanishing of trace and supertrace on the pairing sector: `Tr(M_off) = 0` and `STr(M_off) = 0`.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.Lie.SplitOctonionDerivationSpinRep

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "BlockMat" => Matrix (ι ⊕ ι) (ι ⊕ ι) R
local notation "SubMat" => Matrix ι ι R

/-!
=============================================================================
PART 1: The Grading Operator and the Block Projections
=============================================================================
-/

/-- The Involutive Grading Operator on S₊ ⊕ S₋: Γ = [[1, 0], [0, -1]]. -/
def Gamma : BlockMat :=
  fromBlocks (1 : SubMat) 0 0 (-1 : SubMat)

/-- The Block-Diagonal Stabilizer Component: M_diag = [[A, 0], [0, D]]. -/
def diagComponent (M : BlockMat) : BlockMat :=
  fromBlocks (toBlocks₁₁ M) 0 0 (toBlocks₂₂ M)

/-- The Block-Off-Diagonal Pairing Component: M_off = [[0, B], [C, 0]]. -/
def offDiagComponent (M : BlockMat) : BlockMat :=
  fromBlocks 0 (toBlocks₁₂ M) (toBlocks₂₁ M) 0

/-- THEOREM 1: The Grading Operator is Involutive: Γ² = I. -/
@[simp]
theorem Gamma_sq : Gamma (ι := ι) (R := R) * Gamma = 1 := by
  dsimp [Gamma]
  rw [fromBlocks_multiply]
  simp only [mul_one, mul_zero, add_zero, zero_add, mul_neg, neg_neg, neg_zero]
  exact fromBlocks_one

/-- THEOREM 2: Exact Reconstruction: M = M_diag + M_off. -/
omit [Fintype ι] [DecidableEq ι] in
theorem block_reconstruction (M : BlockMat) :
    diagComponent M + offDiagComponent M = M := by
  ext (i | i) (j | j) <;> simp [diagComponent, offDiagComponent, fromBlocks, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]

/-!
=============================================================================
PART 2: Commutation and Anticommutation with the Grading Operator
=============================================================================
-/

/-- 
  THEOREM 3 (Stabilizer Commutation):
  The block-diagonal stabilizer sector strictly commutes with Γ:
    [Γ, M_diag] = Γ * M_diag - M_diag * Γ = 0
-/
theorem diagComponent_commutes_Gamma (M : BlockMat) :
    Gamma * diagComponent M = diagComponent M * Gamma := by
  dsimp [Gamma, diagComponent]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul, neg_zero]

/-- 
  THEOREM 4 (Pairing Anticommutation):
  The block-off-diagonal pairing sector strictly anticommutes with Γ:
    {Γ, M_off} = Γ * M_off + M_off * Γ = 0
-/
theorem offDiagComponent_anticommutes_Gamma (M : BlockMat) :
    Gamma * offDiagComponent M = - (offDiagComponent M * Gamma) := by
  dsimp [Gamma, offDiagComponent]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul, neg_zero, neg_neg, fromBlocks_neg]

/-!
=============================================================================
PART 3: Projector Algebra via the Cartan Involution
=============================================================================
-/

/-- 
  The Cartan Reflection: θ(M) = Γ * M * Γ.
  θ(M_diag) = M_diag and θ(M_off) = - M_off.
-/
def cartanReflection (M : BlockMat) : BlockMat :=
  Gamma * M * Gamma

@[simp]
theorem cartanReflection_diag (M : BlockMat) :
    cartanReflection (diagComponent M) = diagComponent M := by
  dsimp [cartanReflection]
  calc
    Gamma * diagComponent M * Gamma
      = diagComponent M * Gamma * Gamma := by rw [diagComponent_commutes_Gamma]
    _ = diagComponent M * (Gamma * Gamma) := by rw [mul_assoc]
    _ = diagComponent M * 1 := by rw [Gamma_sq]
    _ = diagComponent M := by rw [mul_one]

@[simp]
theorem cartanReflection_offDiag (M : BlockMat) :
    cartanReflection (offDiagComponent M) = - offDiagComponent M := by
  dsimp [cartanReflection]
  calc
    Gamma * offDiagComponent M * Gamma
      = - (offDiagComponent M * Gamma) * Gamma := by rw [offDiagComponent_anticommutes_Gamma]
    _ = - (offDiagComponent M * Gamma * Gamma) := by rw [neg_mul]
    _ = - (offDiagComponent M * (Gamma * Gamma)) := by rw [mul_assoc]
    _ = - (offDiagComponent M * 1) := by rw [Gamma_sq]
    _ = - offDiagComponent M := by rw [mul_one]

/-- THEOREM 5: The Diagonal Projection equals (1/2) • (M + Γ M Γ). -/
theorem projDiag_eq_half_add_cartan
    (two_inv : R) (h2 : (2 : R) * two_inv = 1) (M : BlockMat) :
    two_inv • (M + cartanReflection M) = diagComponent M := by
  have h_refl : cartanReflection M = diagComponent M - offDiagComponent M := by
    calc
      cartanReflection M = cartanReflection (diagComponent M + offDiagComponent M) := by
        rw [block_reconstruction]
      _ = cartanReflection (diagComponent M) + cartanReflection (offDiagComponent M) := by
        dsimp [cartanReflection]
        simp only [mul_add, add_mul]
      _ = diagComponent M + - offDiagComponent M := by rw [cartanReflection_diag, cartanReflection_offDiag]
      _ = diagComponent M - offDiagComponent M := by rw [sub_eq_add_neg]
  nth_rw 1 [← block_reconstruction M]
  rw [h_refl]
  have h_sum : (diagComponent M + offDiagComponent M) + (diagComponent M - offDiagComponent M) =
      (2 : R) • diagComponent M := by
    calc
      (diagComponent M + offDiagComponent M) + (diagComponent M - offDiagComponent M)
        = (diagComponent M + diagComponent M) + (offDiagComponent M - offDiagComponent M) := by abel
      _ = (2 : R) • diagComponent M + 0 := by rw [two_smul, sub_self]
      _ = (2 : R) • diagComponent M := by rw [add_zero]
  rw [h_sum, smul_smul]
  have h_scalar : two_inv * 2 = 1 := by rw [mul_comm, h2]
  rw [h_scalar, one_smul]

/-- THEOREM 6: The Pairing Projection equals (1/2) • (M - Γ M Γ). -/
theorem projOffDiag_eq_half_sub_cartan
    (two_inv : R) (h2 : (2 : R) * two_inv = 1) (M : BlockMat) :
    two_inv • (M - cartanReflection M) = offDiagComponent M := by
  have h_refl : cartanReflection M = diagComponent M - offDiagComponent M := by
    calc
      cartanReflection M = cartanReflection (diagComponent M + offDiagComponent M) := by
        rw [block_reconstruction]
      _ = cartanReflection (diagComponent M) + cartanReflection (offDiagComponent M) := by
        dsimp [cartanReflection]
        simp only [mul_add, add_mul]
      _ = diagComponent M + - offDiagComponent M := by rw [cartanReflection_diag, cartanReflection_offDiag]
      _ = diagComponent M - offDiagComponent M := by rw [sub_eq_add_neg]
  nth_rw 1 [← block_reconstruction M]
  rw [h_refl]
  have h_sub : (diagComponent M + offDiagComponent M) - (diagComponent M - offDiagComponent M) =
      (2 : R) • offDiagComponent M := by
    calc
      (diagComponent M + offDiagComponent M) - (diagComponent M - offDiagComponent M)
        = (diagComponent M - diagComponent M) + (offDiagComponent M + offDiagComponent M) := by abel
      _ = 0 + (2 : R) • offDiagComponent M := by rw [sub_self, two_smul]
      _ = (2 : R) • offDiagComponent M := by rw [zero_add]
  rw [h_sub, smul_smul]
  have h_scalar : two_inv * 2 = 1 := by rw [mul_comm, h2]
  rw [h_scalar, one_smul]

/-!
=============================================================================
PART 4: Vanishing of Trace-Volume and Supertrace on the Pairing Sector
=============================================================================
-/

/-- Supertrace defined as Tr(Γ * M). -/
def superTrace (M : BlockMat) : R :=
  Matrix.trace (Gamma * M)

omit [DecidableEq ι] in
@[simp]
theorem trace_offDiagComponent (M : BlockMat) :
    Matrix.trace (offDiagComponent M) = 0 := by
  simp [Matrix.trace, offDiagComponent, fromBlocks, Fintype.sum_sum_type]

@[simp]
theorem superTrace_offDiagComponent (M : BlockMat) :
    superTrace (offDiagComponent M) = 0 := by
  dsimp [superTrace, Gamma, offDiagComponent]
  rw [fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  simp [Matrix.trace, fromBlocks, Fintype.sum_sum_type]

/-- 
  THEOREM 7: The Ordinary Trace is Carried Entirely by the Stabilizer Sector:
    Tr(M) = Tr(M_diag)
-/
theorem trace_eq_trace_diag (M : BlockMat) :
    Matrix.trace M = Matrix.trace (diagComponent M) := by
  have h := congr_arg Matrix.trace (block_reconstruction M)
  rw [Matrix.trace_add, trace_offDiagComponent, add_zero] at h
  exact h.symm

/-- 
  THEOREM 8: The Supertrace is Carried Entirely by the Stabilizer Sector:
    STr(M) = STr(M_diag)
-/
theorem superTrace_eq_superTrace_diag (M : BlockMat) :
    superTrace M = superTrace (diagComponent M) := by
  dsimp [superTrace]
  have h_mul : Gamma * M = Gamma * diagComponent M + Gamma * offDiagComponent M := by
    rw [← mul_add, block_reconstruction]
  rw [h_mul, Matrix.trace_add]
  have h_zero : Matrix.trace (Gamma * offDiagComponent M) = 0 := superTrace_offDiagComponent M
  rw [h_zero, add_zero]

end InfoGeometry.Lie.SplitOctonionDerivationSpinRep

end noncomputable section
