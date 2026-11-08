import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Section 60 / Super-Grassmannian: General (p | q) Supercarrier Deformation Algebra

Formalization in native Mathlib of the general graded matrix operator supercarrier `(p | q)`:
1. Graded Supertrace on General Block Matrices:
   `STr(M) = Tr(M₁₁) - Tr(M₂₂)` on `Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R`.
   Linearity: additivity, scalar multiplication, negation.
2. The Noncommutative Deformation Triad:
   - Scale Mode: homothety on diagonal blocks `Matrix.fromBlocks (σ • 1) 0 0 (σ • 1)`.
   - Chiral Mode: off-diagonal odd blocks `Matrix.fromBlocks 0 B C 0`.
   - Volume Mode: unimodular diagonal blocks `Matrix.fromBlocks A 0 0 D` with `Tr(A) = Tr(D)`.
3. Fundamental Supertrace Theorems:
   - Scale mode supertrace: `STr(S(σ)) = (|ι₁| - |ι₂|) · σ`.
   - Balanced scale invariance: when `|ι₁| = |ι₂|`, `STr(S(σ)) = 0`.
   - Chiral mode supertrace vanishing: `STr(X(B, C)) = 0`.
   - Volume mode supertrace vanishing: `STr(V(A, D)) = 0`.
   - Total deformation splitting: `STr(S + X + V) = (|ι₁| - |ι₂|) · σ`.
4. Noncommutative Algebra and Trace Cyclicity:
   - Block multiplication of chiral mode: `X(B, C)² = Matrix.fromBlocks (B * C) 0 0 (C * B)`.
   - Supertrace of chiral square vanishes identically via Mathlib's cyclic trace theorem:
     `Tr(B * C) = Tr(C * B)`.
   - Commutation of scale and chiral modes: `[S(σ), X(B, C)] = 0`.
5. Master verification certificate:
   `GeneralSupercarrierDeformationCertificate` bundling all core theorems.
-/

namespace Experimental.Sandbox.SuperGrassmannian.GeneralSupercarrierDeformation

open Matrix

variable {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
variable {R : Type*} [CommRing R]

/-! ### 1. Graded Supertrace on General Block Matrices -/

/-- Graded Supertrace on general block matrices `Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R`:
    `superTrace M = Matrix.trace (Matrix.toBlocks₁₁ M) - Matrix.trace (Matrix.toBlocks₂₂ M)`. -/
def superTrace (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R) : R :=
  Matrix.trace (Matrix.toBlocks₁₁ M) - Matrix.trace (Matrix.toBlocks₂₂ M)

@[simp] lemma toBlocks₁₁_add (M N : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R) :
    Matrix.toBlocks₁₁ (M + N) = Matrix.toBlocks₁₁ M + Matrix.toBlocks₁₁ N := rfl

@[simp] lemma toBlocks₂₂_add (M N : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R) :
    Matrix.toBlocks₂₂ (M + N) = Matrix.toBlocks₂₂ M + Matrix.toBlocks₂₂ N := rfl

@[simp] lemma toBlocks₁₁_smul (r : R) (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R) :
    Matrix.toBlocks₁₁ (r • M) = r • Matrix.toBlocks₁₁ M := rfl

@[simp] lemma toBlocks₂₂_smul (r : R) (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R) :
    Matrix.toBlocks₂₂ (r • M) = r • Matrix.toBlocks₂₂ M := rfl

@[simp] lemma toBlocks₁₁_neg (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R) :
    Matrix.toBlocks₁₁ (-M) = -Matrix.toBlocks₁₁ M := rfl

@[simp] lemma toBlocks₂₂_neg (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R) :
    Matrix.toBlocks₂₂ (-M) = -Matrix.toBlocks₂₂ M := rfl

/-- Additivity of supertrace: `superTrace (M + N) = superTrace M + superTrace N`. -/
theorem superTrace_add (M N : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R) :
    superTrace (M + N) = superTrace M + superTrace N := by
  dsimp [superTrace]
  rw [Matrix.trace_add, Matrix.trace_add]
  ring

/-- Scalar multiplication linearity of supertrace: `superTrace (r • M) = r * superTrace M`. -/
theorem superTrace_smul (r : R) (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R) :
    superTrace (r • M) = r * superTrace M := by
  dsimp [superTrace]
  rw [Matrix.trace_smul, Matrix.trace_smul]
  ring

/-- Negation linearity of supertrace: `superTrace (-M) = -superTrace M`. -/
theorem superTrace_neg (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R) :
    superTrace (-M) = -superTrace M := by
  dsimp [superTrace]
  rw [Matrix.trace_neg, Matrix.trace_neg]
  ring

/-! ### 2. The Three Deformation Modes as Explicit Block Matrices -/

/-- Scale Mode: homothety `σ • 1` on both diagonal blocks. -/
def scaleMode (σ : R) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R :=
  Matrix.fromBlocks (σ • (1 : Matrix ι₁ ι₁ R)) 0 0 (σ • (1 : Matrix ι₂ ι₂ R))

/-- Chiral Mode: off-diagonal odd blocks `B : Matrix ι₁ ι₂ R` and `C : Matrix ι₂ ι₁ R`. -/
def chiralMode (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R :=
  Matrix.fromBlocks 0 B C 0

/-- Volume Mode: even diagonal blocks `A : Matrix ι₁ ι₁ R` and `D : Matrix ι₂ ι₂ R`. -/
def volumeMode (A : Matrix ι₁ ι₁ R) (D : Matrix ι₂ ι₂ R) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R :=
  Matrix.fromBlocks A 0 0 D

/-! ### 3. Fundamental Supertrace Theorems -/

/-- Supertrace of the scale mode operator:
    `superTrace (scaleMode σ) = ((Fintype.card ι₁ : R) - (Fintype.card ι₂ : R)) * σ`. -/
theorem superTrace_scaleMode (σ : R) :
    superTrace (scaleMode (ι₁ := ι₁) (ι₂ := ι₂) (R := R) σ) =
      ((Fintype.card ι₁ : R) - (Fintype.card ι₂ : R)) * σ := by
  dsimp [superTrace, scaleMode]
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rw [Matrix.trace_one, Matrix.trace_one]
  ring

/-- Balanced scale invariance: when `Fintype.card ι₁ = Fintype.card ι₂`, the scale mode supertrace vanishes. -/
theorem superTrace_scale_balanced (h : Fintype.card ι₁ = Fintype.card ι₂) (σ : R) :
    superTrace (scaleMode (ι₁ := ι₁) (ι₂ := ι₂) (R := R) σ) = 0 := by
  rw [superTrace_scaleMode, h]
  ring

/-- Supertrace of the chiral mode operator vanishes identically: `superTrace (chiralMode B C) = 0`. -/
theorem superTrace_chiralMode (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R) :
    superTrace (chiralMode (ι₁ := ι₁) (ι₂ := ι₂) B C) = 0 := by
  dsimp [superTrace, chiralMode]
  rw [Matrix.trace_zero, Matrix.trace_zero]
  ring

/-- Supertrace of the volume mode operator vanishes when `Matrix.trace A = Matrix.trace D`. -/
theorem superTrace_volumeMode (A : Matrix ι₁ ι₁ R) (D : Matrix ι₂ ι₂ R)
    (h : Matrix.trace A = Matrix.trace D) :
    superTrace (volumeMode A D) = 0 := by
  dsimp [superTrace, volumeMode]
  rw [h]
  ring

/-- Total deformation splitting theorem:
    `superTrace (scaleMode σ + chiralMode B C + volumeMode A D) = ((Fintype.card ι₁ : R) - (Fintype.card ι₂ : R)) * σ`. -/
theorem total_deformation_superTrace (σ : R) (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R)
    (A : Matrix ι₁ ι₁ R) (D : Matrix ι₂ ι₂ R) (h : Matrix.trace A = Matrix.trace D) :
    superTrace (scaleMode σ + chiralMode B C + volumeMode A D) =
      ((Fintype.card ι₁ : R) - (Fintype.card ι₂ : R)) * σ := by
  rw [superTrace_add, superTrace_add]
  rw [superTrace_scaleMode, superTrace_chiralMode, superTrace_volumeMode A D h]
  ring

/-! ### 4. Noncommutative Algebra and Trace Cyclicity -/

/-- Multiplication of two chiral mode operators:
    `chiralMode B C * chiralMode B C = Matrix.fromBlocks (B * C) 0 0 (C * B)`. -/
theorem chiral_mode_mul (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R) :
    chiralMode B C * chiralMode B C = Matrix.fromBlocks (B * C) 0 0 (C * B) := by
  dsimp [chiralMode]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Supertrace of the square of any chiral operator vanishes identically by trace cyclicity:
    `Matrix.trace (B * C) = Matrix.trace (C * B)`. -/
theorem superTrace_chiral_square (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R) :
    superTrace (chiralMode B C * chiralMode B C) = 0 := by
  rw [chiral_mode_mul]
  dsimp [superTrace]
  rw [Matrix.trace_mul_comm B C]
  ring

/-- Commutation of scale and chiral modes:
    `scaleMode σ * chiralMode B C - chiralMode B C * scaleMode σ = 0`. -/
theorem scale_chiral_commutator (σ : R) (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R) :
    scaleMode σ * chiralMode B C - chiralMode B C * scaleMode σ = 0 := by
  dsimp [scaleMode, chiralMode]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-! ### 5. Master Verification Certificate -/

/-- Master Verification Certificate bundling all core theorems of the general supercarrier deformation. -/
structure GeneralSupercarrierDeformationCertificate : Prop where
  superTrace_add : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (M N : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R),
    superTrace (M + N) = superTrace M + superTrace N
  superTrace_smul : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (r : R) (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R),
    superTrace (r • M) = r * superTrace M
  superTrace_neg : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) R),
    superTrace (-M) = -superTrace M
  superTrace_scaleMode : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (σ : R),
    superTrace (scaleMode (ι₁ := ι₁) (ι₂ := ι₂) (R := R) σ) =
      ((Fintype.card ι₁ : R) - (Fintype.card ι₂ : R)) * σ
  superTrace_scale_balanced : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (h : Fintype.card ι₁ = Fintype.card ι₂) (σ : R),
    superTrace (scaleMode (ι₁ := ι₁) (ι₂ := ι₂) (R := R) σ) = 0
  superTrace_chiralMode : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R),
    superTrace (chiralMode B C) = 0
  superTrace_volumeMode : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (A : Matrix ι₁ ι₁ R) (D : Matrix ι₂ ι₂ R) (h : Matrix.trace A = Matrix.trace D),
    superTrace (volumeMode A D) = 0
  total_deformation_superTrace : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (σ : R) (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R)
    (A : Matrix ι₁ ι₁ R) (D : Matrix ι₂ ι₂ R) (h : Matrix.trace A = Matrix.trace D),
    superTrace (scaleMode σ + chiralMode B C + volumeMode A D) =
      ((Fintype.card ι₁ : R) - (Fintype.card ι₂ : R)) * σ
  chiral_mode_mul : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R),
    chiralMode B C * chiralMode B C = Matrix.fromBlocks (B * C) 0 0 (C * B)
  superTrace_chiral_square : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R),
    superTrace (chiralMode B C * chiralMode B C) = 0
  scale_chiral_commutator : ∀ {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
    {R : Type*} [CommRing R] (σ : R) (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R),
    scaleMode σ * chiralMode B C - chiralMode B C * scaleMode σ = 0

/-- Compilation of the master verification certificate. -/
theorem compile_general_supercarrier_deformation : GeneralSupercarrierDeformationCertificate where
  superTrace_add := fun M N => superTrace_add M N
  superTrace_smul := fun r M => superTrace_smul r M
  superTrace_neg := fun M => superTrace_neg M
  superTrace_scaleMode := fun σ => superTrace_scaleMode σ
  superTrace_scale_balanced := fun h σ => superTrace_scale_balanced h σ
  superTrace_chiralMode := fun B C => superTrace_chiralMode B C
  superTrace_volumeMode := fun A D h => superTrace_volumeMode A D h
  total_deformation_superTrace := fun σ B C A D h => total_deformation_superTrace σ B C A D h
  chiral_mode_mul := fun B C => chiral_mode_mul B C
  superTrace_chiral_square := fun B C => superTrace_chiral_square B C
  scale_chiral_commutator := fun σ B C => scale_chiral_commutator σ B C

end Experimental.Sandbox.SuperGrassmannian.GeneralSupercarrierDeformation
