/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# The Graph Hodge-Dirac Embedding into the 3-Mode Supercarrier Deformation Triad

Chiral Mode Injection, Graded Supertrace Vanishing, Hodge-Laplacian Cancellation,
and Projective Berezinian Invariance.

Target Sandbox:
`lean/Experimental/Sandbox/SuperGrassmannian/GraphDiracSupercarrierEmbedding.lean`

This module formalizes in native Mathlib:
1. Graded Supertrace on the Total Supercarrier `Matrix (V ⊕ E) (V ⊕ E) R`:
   `STr(M) = Tr(M₁₁) - Tr(M₂₂)`.
2. The 3-Mode Supercarrier Deformation Triad:
   - Scale Mode: homothety `σ • 1` on diagonal blocks.
   - Chiral Mode: off-diagonal odd blocks `Matrix.fromBlocks 0 B C 0`.
   - Volume Mode: unimodular diagonal blocks `Matrix.fromBlocks A 0 0 D`.
3. Discrete Graph Hodge-Dirac Embedding:
   Given graph incidence matrix `B : Matrix E V R`, the discrete Hodge-Dirac operator
   is embedded as a pure chiral mode:
   `D = chiralMode Bᵀ B = Matrix.fromBlocks 0 Bᵀ B 0`.
4. Fundamental Theorems:
   - Linear Dirac Supertrace Vanishing: `STr(D) = 0`.
   - Hodge-Laplacian Square is a Volume Mode:
     `D² = volumeMode (Bᵀ * B) (B * Bᵀ) = Matrix.fromBlocks Δ₀ 0 0 Δ₁`.
   - Hodge-Laplacian Supertrace Exact Cancellation via Cyclicity:
     `STr(D²) = Tr(Bᵀ * B) - Tr(B * Bᵀ) = 0` via `Matrix.trace_mul_comm`.
   - Scale Mode Commutation: `[scaleMode σ, D] = 0`.
   - Total Deformation Supertrace Separation:
     `STr(scaleMode σ + D + volumeMode A D) = (|V| - |E|) * σ`.
   - Balanced Graph Supertrace Annihilation:
     When `|V| = |E|`, `STr = 0`.
   - Chiral Parity Anticommutation:
     `D * Γ + Γ * D = 0` where `Γ = Matrix.fromBlocks 1 0 0 (-1)`.
5. Projective Berezinian Invariance:
   - Infinitesimal Berezinian invariance `STr(M) = 0`.
   - Multiplicative homothety Berezinian scaling on balanced and unbalanced spaces.
6. The named owner theorems are audited directly; no certificate bundle
   substitutes a record constructor for those declarations.
-/

namespace InfoGeometry.SuperGrassmannian.GraphDiracSupercarrierEmbedding

open Matrix

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
variable {R : Type*} [Ring R]

/-! ### 1. Graded Supertrace on General Block Carrier -/

/-- Graded Supertrace on total supercarrier `Matrix (V ⊕ E) (V ⊕ E) R`:
    `superTrace M = Matrix.trace (Matrix.toBlocks₁₁ M) - Matrix.trace (Matrix.toBlocks₂₂ M)`. -/
def superTrace (M : Matrix (V ⊕ E) (V ⊕ E) R) : R :=
  Matrix.trace (Matrix.toBlocks₁₁ M) - Matrix.trace (Matrix.toBlocks₂₂ M)

@[simp] lemma toBlocks₁₁_add (M N : Matrix (V ⊕ E) (V ⊕ E) R) :
    Matrix.toBlocks₁₁ (M + N) = Matrix.toBlocks₁₁ M + Matrix.toBlocks₁₁ N := rfl

@[simp] lemma toBlocks₂₂_add (M N : Matrix (V ⊕ E) (V ⊕ E) R) :
    Matrix.toBlocks₂₂ (M + N) = Matrix.toBlocks₂₂ M + Matrix.toBlocks₂₂ N := rfl

@[simp] lemma toBlocks₁₁_smul (r : R) (M : Matrix (V ⊕ E) (V ⊕ E) R) :
    Matrix.toBlocks₁₁ (r • M) = r • Matrix.toBlocks₁₁ M := rfl

@[simp] lemma toBlocks₂₂_smul (r : R) (M : Matrix (V ⊕ E) (V ⊕ E) R) :
    Matrix.toBlocks₂₂ (r • M) = r • Matrix.toBlocks₂₂ M := rfl

@[simp] lemma toBlocks₁₁_neg (M : Matrix (V ⊕ E) (V ⊕ E) R) :
    Matrix.toBlocks₁₁ (-M) = -Matrix.toBlocks₁₁ M := rfl

@[simp] lemma toBlocks₂₂_neg (M : Matrix (V ⊕ E) (V ⊕ E) R) :
    Matrix.toBlocks₂₂ (-M) = -Matrix.toBlocks₂₂ M := rfl

/-- Additivity of supertrace: `superTrace (M + N) = superTrace M + superTrace N`. -/
theorem superTrace_add (M N : Matrix (V ⊕ E) (V ⊕ E) R) :
    superTrace (M + N) = superTrace M + superTrace N := by
  dsimp [superTrace]
  rw [Matrix.trace_add, Matrix.trace_add]
  noncomm_ring

/-- Scalar multiplication linearity of supertrace: `superTrace (r • M) = r * superTrace M`. -/
theorem superTrace_smul (r : R) (M : Matrix (V ⊕ E) (V ⊕ E) R) :
    superTrace (r • M) = r * superTrace M := by
  dsimp [superTrace]
  rw [Matrix.trace_smul, Matrix.trace_smul]
  noncomm_ring

/-- Negation linearity of supertrace: `superTrace (-M) = -superTrace M`. -/
theorem superTrace_neg (M : Matrix (V ⊕ E) (V ⊕ E) R) :
    superTrace (-M) = -superTrace M := by
  dsimp [superTrace]
  rw [Matrix.trace_neg, Matrix.trace_neg]
  noncomm_ring

/-! ### 2. The 3-Mode Supercarrier Deformation Triad -/

/-- Scale Mode: homothety `σ • 1` on diagonal blocks. -/
def scaleMode (σ : R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks (σ • (1 : Matrix V V R)) 0 0 (σ • (1 : Matrix E E R))

/-- Chiral Mode: off-diagonal odd blocks `B : Matrix V E R` and `C : Matrix E V R`. -/
def chiralMode (B : Matrix V E R) (C : Matrix E V R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks 0 B C 0

/-- Volume Mode: diagonal even blocks `A : Matrix V V R` and `D : Matrix E E R`. -/
def volumeMode (A : Matrix V V R) (D : Matrix E E R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks A 0 0 D

/-- Supertrace of the scale mode operator:
    `superTrace (scaleMode σ) = ((Fintype.card V : R) - (Fintype.card E : R)) * σ`. -/
theorem superTrace_scaleMode (σ : R) :
    superTrace (scaleMode (V := V) (E := E) (R := R) σ) =
      ((Fintype.card V : R) - (Fintype.card E : R)) * σ := by
  dsimp [superTrace, scaleMode]
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rw [Matrix.trace_one, Matrix.trace_one]
  simp only [smul_eq_mul, sub_mul]
  rw [← Nat.cast_comm (Fintype.card V) σ, ← Nat.cast_comm (Fintype.card E) σ]

/-- Supertrace of the volume mode operator vanishes when `Matrix.trace A = Matrix.trace D`. -/
theorem superTrace_volumeMode (A : Matrix V V R) (D : Matrix E E R)
    (h : Matrix.trace A = Matrix.trace D) :
    superTrace (volumeMode A D) = 0 := by
  dsimp [superTrace, volumeMode]
  rw [h]
  noncomm_ring

/-! ### 3. Embedding the Graph Hodge-Dirac as a Pure Chiral Mode -/

/-- Embedding the discrete Graph Hodge-Dirac operator as a pure chiral mode:
    given incidence matrix `B : Matrix E V R`, the Hodge-Dirac operator is
    `hodgeDiracChiral B = chiralMode Bᵀ B = Matrix.fromBlocks 0 Bᵀ B 0`. -/
def hodgeDiracChiral (B : Matrix E V R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  chiralMode Bᵀ B

@[simp] lemma hodgeDiracChiral_def (B : Matrix E V R) :
    hodgeDiracChiral B = Matrix.fromBlocks 0 Bᵀ B 0 := rfl

/-! ### 3a. The graph grading is the Peirce cut on the same matrix carrier -/

/-- Vertex projection in the full graph cochain matrix algebra. -/
def vertexProjection : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks (1 : Matrix V V R) (0 : Matrix V E R)
    (0 : Matrix E V R) (0 : Matrix E E R)

theorem vertexProjection_idempotent :
    vertexProjection (V := V) (E := E) (R := R) *
        vertexProjection (V := V) (E := E) (R := R) =
      vertexProjection (V := V) (E := E) (R := R) := by
  rw [vertexProjection, Matrix.fromBlocks_multiply]
  simp

theorem one_sub_vertexProjection :
    (1 : Matrix (V ⊕ E) (V ⊕ E) R) - vertexProjection =
      Matrix.fromBlocks 0 0 0 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [vertexProjection, Matrix.one_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]

/-- The two Peirce cones of the existing graph Hodge--Dirac are its original
upper and lower incidence blocks. -/
theorem graphDirac_peirce_cones (B : Matrix E V R) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus vertexProjection
        (hodgeDiracChiral B) = Matrix.fromBlocks 0 Bᵀ 0 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus vertexProjection
        (hodgeDiracChiral B) = Matrix.fromBlocks 0 0 B 0 := by
  rw [hodgeDiracChiral_def]
  constructor
  · unfold InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
    rw [one_sub_vertexProjection, vertexProjection]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  · unfold InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus
    rw [one_sub_vertexProjection, vertexProjection]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp

/-- The existing graph Hodge--Dirac is exactly the Peirce `Φ` generator on
the vertex/edge matrix carrier. -/
theorem graphDirac_eq_peirce_genPhi (B : Matrix E V R) :
    hodgeDiracChiral B = InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
      vertexProjection (hodgeDiracChiral B) (hodgeDiracChiral B) := by
  rw [InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi,
    (graphDirac_peirce_cones B).1, (graphDirac_peirce_cones B).2,
    hodgeDiracChiral_def]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂]

/-- The graph Hodge Laplacian square is the Peirce tetraktys Jordan element
`V` on this same matrix carrier. -/
theorem graphDirac_sq_eq_peirce_genV (B : Matrix E V R) :
    hodgeDiracChiral B * hodgeDiracChiral B =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genV
        vertexProjection (hodgeDiracChiral B) (hodgeDiracChiral B) := by
  rw [InfoGeometry.OperatorAlgebra.PeirceSpine.genV,
    (graphDirac_peirce_cones B).1, (graphDirac_peirce_cones B).2,
    hodgeDiracChiral_def]
  simp [InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm,
    Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_add]
  simp

/-! ### 4. Fundamental Graded Supertrace Vanishing & Hodge Cancellation -/

/-- Theorem 1 (Linear Dirac Supertrace Vanishing):
    The supertrace of the discrete Hodge-Dirac operator vanishes identically. -/
theorem superTrace_hodgeDiracChiral (B : Matrix E V R) :
    superTrace (hodgeDiracChiral B) = 0 := by
  dsimp [superTrace, hodgeDiracChiral, chiralMode]
  rw [Matrix.trace_zero, Matrix.trace_zero]
  noncomm_ring

/-- Theorem 2 (Hodge-Laplacian Square is a Volume Mode):
    The square of the Hodge-Dirac operator equals the block Hodge Laplacian:
    `D² = volumeMode (Bᵀ * B) (B * Bᵀ) = Matrix.fromBlocks Δ₀ 0 0 Δ₁`. -/
theorem hodgeDiracChiral_sq (B : Matrix E V R) :
    hodgeDiracChiral B * hodgeDiracChiral B = volumeMode (Bᵀ * B) (B * Bᵀ) := by
  dsimp [hodgeDiracChiral, chiralMode, volumeMode]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Theorem 3 (Hodge-Laplacian Supertrace Exact Cancellation via Cyclicity):
    The supertrace of the squared Hodge-Dirac operator vanishes identically:
    `STr(D²) = Tr(Bᵀ * B) - Tr(B * Bᵀ) = 0` via Mathlib's `trace_mul_comm`. -/
theorem superTrace_hodgeDiracChiral_sq {R : Type*} [CommRing R] (B : Matrix E V R) :
    superTrace (hodgeDiracChiral B * hodgeDiracChiral B) = 0 := by
  rw [hodgeDiracChiral_sq]
  dsimp [superTrace, volumeMode]
  rw [Matrix.trace_mul_comm Bᵀ B]
  noncomm_ring

/-- Theorem 4 (Scale Commutation):
    Uniform homotheties strictly commute with the discrete Hodge-Dirac operator:
    `scaleMode σ * hodgeDiracChiral B = hodgeDiracChiral B * scaleMode σ`. -/
theorem scaleMode_hodgeDiracChiral_comm {R : Type*} [CommRing R] (σ : R) (B : Matrix E V R) :
    scaleMode σ * hodgeDiracChiral B = hodgeDiracChiral B * scaleMode σ := by
  apply eq_of_sub_eq_zero
  dsimp [scaleMode, hodgeDiracChiral, chiralMode]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Theorem 5 (Total Deformation Supertrace Separation):
    Under a general triad deformation `scaleMode σ + hodgeDiracChiral B + volumeMode A D`,
    the supertrace isolates the pure Euler-Poincaré scale charge:
    `STr = (|V| - |E|) * σ`. -/
theorem total_deformation_superTrace (σ : R) (B : Matrix E V R) (A : Matrix V V R) (D : Matrix E E R)
    (hvol : Matrix.trace A = Matrix.trace D) :
    superTrace (scaleMode σ + hodgeDiracChiral B + volumeMode A D) =
      ((Fintype.card V : R) - (Fintype.card E : R)) * σ := by
  rw [superTrace_add, superTrace_add]
  rw [superTrace_scaleMode, superTrace_hodgeDiracChiral, superTrace_volumeMode A D hvol]
  noncomm_ring

/-- Theorem 6 (Balanced Graph Supertrace Annihilation):
    On a balanced graph where `|V| = |E|` (Euler characteristic zero),
    the total triad deformation supertrace vanishes identically. -/
theorem balanced_graph_superTrace (hcard : Fintype.card V = Fintype.card E) (σ : R) (B : Matrix E V R)
    (A : Matrix V V R) (D : Matrix E E R) (hvol : Matrix.trace A = Matrix.trace D) :
    superTrace (scaleMode σ + hodgeDiracChiral B + volumeMode A D) = 0 := by
  rw [total_deformation_superTrace σ B A D hvol, hcard]
  noncomm_ring

/-! ### 5. Chiral Parity Grading and Anticommutation -/

/-- The canonical Chiral Parity Grading operator `Γ`:
    `Γ = Matrix.fromBlocks 1 0 0 (-1)`. -/
def chiralParity : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- The chiral parity operator squares to identity: `Γ² = 1`. -/
theorem chiralParity_sq :
    chiralParity (V := V) (E := E) (R := R) * chiralParity = 1 := by
  dsimp [chiralParity]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Chiral Parity Anticommutation:
    The discrete Hodge-Dirac operator strictly anticommutes with chiral parity:
    `D * Γ + Γ * D = 0`. -/
theorem hodgeDirac_anticomm_parity (B : Matrix E V R) :
    hodgeDiracChiral B * chiralParity + chiralParity * hodgeDiracChiral B = 0 := by
  dsimp [hodgeDiracChiral, chiralMode, chiralParity]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp
  rw [Matrix.fromBlocks_add]
  simp [Matrix.fromBlocks_zero]

/-! ### 6. Projective Berezinian Invariance -/

/-- Infinitesimal Berezinian Invariance condition:
    An operator `M` generates a volume-preserving flow if its graded supertrace vanishes. -/
def isBerezinianInvariant (M : Matrix (V ⊕ E) (V ⊕ E) R) : Prop :=
  superTrace M = 0

/-- Linear Hodge-Dirac operator generates a Berezinian-invariant flow. -/
theorem hodgeDiracChiral_isBerezinianInvariant (B : Matrix E V R) :
    isBerezinianInvariant (hodgeDiracChiral B) :=
  superTrace_hodgeDiracChiral B

/-- Squared Hodge-Dirac operator (Hodge Laplacian) generates a Berezinian-invariant flow. -/
theorem hodgeDiracChiral_sq_isBerezinianInvariant {R : Type*} [CommRing R] (B : Matrix E V R) :
    isBerezinianInvariant (hodgeDiracChiral B * hodgeDiracChiral B) :=
  superTrace_hodgeDiracChiral_sq B

/-- Volume mode generates a Berezinian-invariant flow when `Tr(A) = Tr(D)`. -/
theorem volumeMode_isBerezinianInvariant (A : Matrix V V R) (D : Matrix E E R)
    (hvol : Matrix.trace A = Matrix.trace D) :
    isBerezinianInvariant (volumeMode A D) :=
  superTrace_volumeMode A D hvol

/-- Total balanced deformation generates a Berezinian-invariant flow. -/
theorem balanced_deformation_isBerezinianInvariant (hcard : Fintype.card V = Fintype.card E)
    (σ : R) (B : Matrix E V R) (A : Matrix V V R) (D : Matrix E E R)
    (hvol : Matrix.trace A = Matrix.trace D) :
    isBerezinianInvariant (scaleMode σ + hodgeDiracChiral B + volumeMode A D) :=
  balanced_graph_superTrace hcard σ B A D hvol

/-- Multiplicative Berezinian Homothety Invariance on Balanced Super-spaces:
    Under uniform homothety by unit `c`, the Berezinian scale factor is
    `c^p * (inv_c)^p = 1`. -/
theorem balanced_berezinian_homothety {R : Type*} [CommRing R] (p : ℕ) (c inv_c : R) (h : c * inv_c = 1) :
    (c ^ p) * (inv_c ^ p) = 1 := by
  rw [← mul_pow, h, one_pow]

/-- Unbalanced Berezinian projective scaling factor:
    `c^(p+q) * (inv_c)^q = c^p * (c * inv_c)^q = c^p`. -/
theorem unbalanced_berezinian_factor {R : Type*} [CommRing R] (p q : ℕ) (c inv_c : R) (h : c * inv_c = 1) :
    (c ^ (p + q)) * (inv_c ^ q) = c ^ p := by
  calc
    (c ^ (p + q)) * (inv_c ^ q) = (c ^ p * c ^ q) * (inv_c ^ q) := by rw [pow_add]
    _ = c ^ p * (c ^ q * inv_c ^ q) := by rw [mul_assoc]
    _ = c ^ p * (c * inv_c) ^ q := by rw [← mul_pow]
    _ = c ^ p * (1 : R) ^ q := by rw [h]
    _ = c ^ p * 1 := by rw [one_pow]
    _ = c ^ p := by rw [mul_one]

/-- Berezinian homothety invariance for balanced graphs (`|V| = |E|`). -/
theorem balanced_graph_berezinian_homothety {R : Type*} [CommRing R] (hcard : Fintype.card V = Fintype.card E)
    (c inv_c : R) (h : c * inv_c = 1) :
    (c ^ (Fintype.card V)) * (inv_c ^ (Fintype.card E)) = 1 := by
  rw [hcard]
  exact balanced_berezinian_homothety (Fintype.card E) c inv_c h

end InfoGeometry.SuperGrassmannian.GraphDiracSupercarrierEmbedding
