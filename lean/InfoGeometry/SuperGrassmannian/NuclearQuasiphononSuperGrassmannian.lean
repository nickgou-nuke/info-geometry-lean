/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
import InfoGeometry.Canonical.Erlangen20Unification
import InfoGeometry.Physics.NuclearFeshbachReduction
import InfoGeometry.Algebra.BdGSchurBerezinianCompatibility
import InfoGeometry.Supergeometry.BerezinianDecomposition

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Section 81 / Target 2: Nuclear Quasiphonon Super-Grassmannian

Graded Supercarrier, Exact SUSY Supertrace Vanishing, 5-Graded Deformation Triad,
and Berezinian Projective Invariance.

This module formalizes in native Mathlib:
1. The Graded Supercarrier & Graded Supertrace on general block matrices `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R`:
   - `superTrace M = Matrix.trace (Matrix.toBlocks₁₁ M) - Matrix.trace (Matrix.toBlocks₂₂ M)`
   - Linearity: additivity, scalar multiplication, negation, subtraction.
2. Exact Real SUSY Hamiltonian Supertrace Annihilation:
   - Off-diagonal chiral supercharges `Q(V)` and `Q†(V)` for coupling `V : Matrix ι₀ ι₁ R`
   - Supersymmetric Hamiltonian `H = Q Q† + Q† Q`
   - Exact block factorization `H = fromBlocks (V * Vᵀ) 0 0 (Vᵀ * V)`
   - Exact real SUSY supertrace cancellation: `superTrace (susyH V) = 0` via cyclic invariance `Tr(V Vᵀ) = Tr(Vᵀ V)`.
3. The 5-Graded Deformation Triad:
   - Scale Mode: homothety on diagonal blocks `fromBlocks (σ • 1) 0 0 (σ • 1)`
   - Chiral Mode: off-diagonal odd blocks `fromBlocks 0 B C 0`
   - Volume Mode: even diagonal blocks `fromBlocks A 0 0 D` with `Tr(A) = Tr(D)`
   - Supertrace formulas and splitting: `STr(S + X + V) = (|ι₀| - |ι₁|) · σ`
   - Chiral square vanishing via trace cyclicity: `STr(X²(B, C)) = 0`.
4. Super-Grassmannian Berezinian & Homothety Invariance:
   - Berezinian on 2x2 scalar block level and `Matrix (Fin 2) (Fin 2) R`
   - Invariance under uniform homothety scaling: `Ber(scale • M) = Ber(M)`
   - Balanced homothety cancellation `(c^p) * (inv_c^p) = 1`
   - Unbalanced projective factor absorption `(c^(p+q)) * (inv_c^q) = c^p`.
5. Master Verification Certificate:
   - Bundles all core theorems into `NuclearQuasiphononSuperGrassmannianCertificate`.
-/

namespace InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian

open Matrix

section RingSupercarrier

variable {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
variable {R : Type*} [Ring R]

/-! ### 1. The Graded Supercarrier & Graded Supertrace -/

/-- Graded supertrace on general block matrices `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R`:
    `superTrace M = Matrix.trace (Matrix.toBlocks₁₁ M) - Matrix.trace (Matrix.toBlocks₂₂ M)`. -/
def superTrace (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) : R :=
  Matrix.trace (Matrix.toBlocks₁₁ M) - Matrix.trace (Matrix.toBlocks₂₂ M)

@[simp] lemma toBlocks₁₁_add (M N : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    Matrix.toBlocks₁₁ (M + N) = Matrix.toBlocks₁₁ M + Matrix.toBlocks₁₁ N := rfl

@[simp] lemma toBlocks₂₂_add (M N : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    Matrix.toBlocks₂₂ (M + N) = Matrix.toBlocks₂₂ M + Matrix.toBlocks₂₂ N := rfl

@[simp] lemma toBlocks₁₁_smul (r : R) (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    Matrix.toBlocks₁₁ (r • M) = r • Matrix.toBlocks₁₁ M := rfl

@[simp] lemma toBlocks₂₂_smul (r : R) (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    Matrix.toBlocks₂₂ (r • M) = r • Matrix.toBlocks₂₂ M := rfl

@[simp] lemma toBlocks₁₁_neg (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    Matrix.toBlocks₁₁ (-M) = -Matrix.toBlocks₁₁ M := rfl

@[simp] lemma toBlocks₂₂_neg (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    Matrix.toBlocks₂₂ (-M) = -Matrix.toBlocks₂₂ M := rfl

/-- Additivity of supertrace: `superTrace (M + N) = superTrace M + superTrace N`. -/
theorem superTrace_add (M N : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    superTrace (M + N) = superTrace M + superTrace N := by
  dsimp [superTrace]
  rw [Matrix.trace_add, Matrix.trace_add]
  abel

/-- Scalar multiplication linearity of supertrace: `superTrace (c • M) = c * superTrace M`. -/
theorem superTrace_smul (c : R) (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    superTrace (c • M) = c * superTrace M := by
  dsimp [superTrace]
  rw [Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, mul_sub]

/-- Negation linearity of supertrace: `superTrace (-M) = -superTrace M`. -/
theorem superTrace_neg (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    superTrace (-M) = -superTrace M := by
  dsimp [superTrace]
  rw [Matrix.trace_neg, Matrix.trace_neg]
  abel

/-- Subtraction linearity of supertrace: `superTrace (M - N) = superTrace M - superTrace N`. -/
theorem superTrace_sub (M N : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    superTrace (M - N) = superTrace M - superTrace N := by
  rw [sub_eq_add_neg, superTrace_add, superTrace_neg, sub_eq_add_neg]

/-! ### 2. Exact Real SUSY Hamiltonian Supertrace Annihilation -/

/-- Off-diagonal chiral supercharge $Q(V)$:
    $Q(V) = \begin{pmatrix} 0 & V \\ 0 & 0 \end{pmatrix}$. -/
def susyQ (V : Matrix ι₀ ι₁ R) : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R :=
  Matrix.fromBlocks 0 V 0 0

/-- Adjoint / conjugate chiral supercharge $Q^\dagger(V)$:
    $Q^\dagger(V) = \begin{pmatrix} 0 & 0 \\ Vᵀ & 0 \end{pmatrix}$. -/
def susyQ_dag (V : Matrix ι₀ ι₁ R) : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R :=
  Matrix.fromBlocks 0 0 Vᵀ 0

/-- Supersymmetric Hamiltonian $H = Q Q^\dagger + Q^\dagger Q$. -/
def susyH (V : Matrix ι₀ ι₁ R) : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R :=
  (susyQ V) * (susyQ_dag V) + (susyQ_dag V) * (susyQ V)

/-- Nilpotency of the chiral supercharge: $Q^2 = 0$. -/
theorem susyQ_sq (V : Matrix ι₀ ι₁ R) :
    susyQ V * susyQ V = 0 := by
  dsimp [susyQ]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Nilpotency of the conjugate chiral supercharge: $(Q^\dagger)^2 = 0$. -/
theorem susyQ_dag_sq (V : Matrix ι₀ ι₁ R) :
    susyQ_dag V * susyQ_dag V = 0 := by
  dsimp [susyQ_dag]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Block formula for the supersymmetric Hamiltonian:
    $H(V) = \begin{pmatrix} V Vᵀ & 0 \\ 0 & Vᵀ V \end{pmatrix}$. -/
theorem susyH_eq (V : Matrix ι₀ ι₁ R) :
    susyH V = Matrix.fromBlocks (V * Vᵀ) 0 0 (Vᵀ * V) := by
  dsimp [susyH, susyQ, susyQ_dag]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp

/-! ### 3. The 5-Graded Supercarrier Deformation Triad -/

/-- Scale Mode: homothety `σ • 1` on diagonal blocks. -/
def scaleMode (σ : R) : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R :=
  Matrix.fromBlocks (σ • (1 : Matrix ι₀ ι₀ R)) 0 0 (σ • (1 : Matrix ι₁ ι₁ R))

/-- Chiral Mode: off-diagonal odd blocks `B : Matrix ι₀ ι₁ R` and `C : Matrix ι₁ ι₀ R`. -/
def chiralMode (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R) : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R :=
  Matrix.fromBlocks 0 B C 0

/-- Volume Mode: even diagonal blocks `A : Matrix ι₀ ι₀ R` and `D : Matrix ι₁ ι₁ R`. -/
def volumeMode (A : Matrix ι₀ ι₀ R) (D : Matrix ι₁ ι₁ R) : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R :=
  Matrix.fromBlocks A 0 0 D

/-- Supertrace of the scale mode operator:
    `superTrace (scaleMode σ) = ((Fintype.card ι₀ : R) - (Fintype.card ι₁ : R)) * σ`. -/
theorem superTrace_scaleMode (σ : R) :
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) (R := R) σ) =
      ((Fintype.card ι₀ : R) - (Fintype.card ι₁ : R)) * σ := by
  dsimp [superTrace, scaleMode]
  rw [Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, Matrix.trace_one]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
  rw [← (Nat.cast_commute (Fintype.card ι₀) σ).eq,
      ← (Nat.cast_commute (Fintype.card ι₁) σ).eq,
      ← sub_mul]

/-- Balanced scale invariance: when `Fintype.card ι₀ = Fintype.card ι₁`, the scale mode supertrace vanishes. -/
theorem superTrace_scale_balanced (h : Fintype.card ι₀ = Fintype.card ι₁) (σ : R) :
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) (R := R) σ) = 0 := by
  rw [superTrace_scaleMode, h, sub_self, zero_mul]

/-- Supertrace of the chiral mode operator vanishes identically: `superTrace (chiralMode B C) = 0`. -/
theorem superTrace_chiralMode (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R) :
    superTrace (chiralMode (ι₀ := ι₀) (ι₁ := ι₁) B C) = 0 := by
  dsimp [superTrace, chiralMode]
  rw [Matrix.trace_zero, Matrix.trace_zero, sub_self]

/-- Supertrace of the volume mode operator vanishes when `Matrix.trace A = Matrix.trace D`. -/
theorem superTrace_volumeMode (A : Matrix ι₀ ι₀ R) (D : Matrix ι₁ ι₁ R)
     (h : Matrix.trace A = Matrix.trace D) :
    superTrace (volumeMode (ι₀ := ι₀) (ι₁ := ι₁) A D) = 0 := by
  dsimp [superTrace, volumeMode]
  rw [h, sub_self]

/-- Multiplication of two chiral mode operators:
    `chiralMode B C * chiralMode B C = Matrix.fromBlocks (B * C) 0 0 (C * B)`. -/
theorem chiral_mode_mul (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R) :
    chiralMode B C * chiralMode B C = Matrix.fromBlocks (B * C) 0 0 (C * B) := by
  dsimp [chiralMode]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Total deformation splitting theorem:
    `superTrace (scaleMode σ + chiralMode B C + volumeMode A D) = ((Fintype.card ι₀ : R) - (Fintype.card ι₁ : R)) * σ`. -/
theorem total_deformation_superTrace (σ : R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (A : Matrix ι₀ ι₀ R) (D : Matrix ι₁ ι₁ R) (hvol : Matrix.trace A = Matrix.trace D) :
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) σ + chiralMode B C + volumeMode A D) =
      ((Fintype.card ι₀ : R) - (Fintype.card ι₁ : R)) * σ := by
  rw [superTrace_add, superTrace_add]
  rw [superTrace_scaleMode, superTrace_chiralMode, superTrace_volumeMode A D hvol]
  abel

/-- Berezinian for a 2x2 supermatrix with scalar entries `a, b, c, d` where `d` has specified inverse `inv_d`:
    $\mathrm{Ber} \begin{pmatrix} a & b \\ c & d \end{pmatrix} = (a - b \, d^{-1} \, c) \, d^{-1}$. -/
def berezinian2 (a b c d inv_d : R) : R :=
  (a - b * inv_d * c) * inv_d

/-- Berezinian on full 2x2 block matrix carrier `Matrix (Fin 2) (Fin 2) R`:
    evaluates `berezinian2` on matrix components. -/
def berezinianMat (M : Matrix (Fin 2) (Fin 2) R) (inv_d : R) : R :=
  berezinian2 (M 0 0) (M 0 1) (M 1 0) (M 1 1) inv_d

end RingSupercarrier

section CommSupercarrier

variable {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
variable {R : Type*} [CommRing R]

/-- The Fundamental Real SUSY Vacuum Energy Cancellation:
    $\mathrm{STr}(H_{\mathrm{susy}}(V)) = \mathrm{Tr}(V Vᵀ) - \mathrm{Tr}(Vᵀ V) = 0$
    strictly by cyclic invariance of trace. -/
theorem superTrace_susyH (V : Matrix ι₀ ι₁ R) :
    superTrace (susyH V) = 0 := by
  rw [susyH_eq]
  dsimp [superTrace]
  rw [Matrix.trace_mul_comm V Vᵀ]
  exact sub_self _

/-- Supertrace of the square of any chiral operator vanishes identically by trace cyclicity:
    `superTrace ((chiralMode B C) * (chiralMode B C)) = 0`. -/
theorem superTrace_chiralSquare (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R) :
    superTrace ((chiralMode B C) * (chiralMode B C)) = 0 := by
  rw [chiral_mode_mul]
  dsimp [superTrace]
  rw [Matrix.trace_mul_comm B C]
  exact sub_self _

/-! ### 4. Super-Grassmannian Berezinian & Homothety Invariance -/

/-- Berezinian homothety balance: under uniform scale homothety by a unit `scale` with inverse `inv_scale`,
    $\mathrm{Ber}(\mathrm{scale} \cdot M) = \mathrm{Ber}(M)$. -/
theorem berezinian_homothety_balance (a b c d inv_d scale inv_scale : R)
    (h_scale : scale * inv_scale = 1) (h_inv_d : d * inv_d = 1) :
    berezinian2 (scale * a) (scale * b) (scale * c) (scale * d) (inv_scale * inv_d) =
      berezinian2 a b c d inv_d := by
  dsimp [berezinian2]
  have h_inner : (scale * a - scale * b * (inv_scale * inv_d) * (scale * c)) = scale * (a - b * inv_d * c) := by
    calc scale * a - scale * b * (inv_scale * inv_d) * (scale * c)
        = scale * a - (scale * inv_scale) * (b * inv_d * (scale * c)) := by ring
      _ = scale * a - 1 * (scale * (b * inv_d * c)) := by rw [h_scale]; ring
      _ = scale * (a - b * inv_d * c) := by ring
  rw [h_inner]
  calc scale * (a - b * inv_d * c) * (inv_scale * inv_d)
      = (scale * inv_scale) * ((a - b * inv_d * c) * inv_d) := by ring
    _ = 1 * ((a - b * inv_d * c) * inv_d) := by rw [h_scale]
    _ = (a - b * inv_d * c) * inv_d := by ring

/-- Berezinian scale invariance on `Matrix (Fin 2) (Fin 2) R` under scalar homothety:
    $\mathrm{Ber}(scale • M) = \mathrm{Ber}(M)$. -/
theorem berezinianMat_smul (M : Matrix (Fin 2) (Fin 2) R) (inv_d scale inv_scale : R)
    (h_scale : scale * inv_scale = 1) (h_inv_d : M 1 1 * inv_d = 1) :
    berezinianMat (scale • M) (inv_scale * inv_d) = berezinianMat M inv_d := by
  dsimp [berezinianMat]
  exact berezinian_homothety_balance (M 0 0) (M 0 1) (M 1 0) (M 1 1) inv_d scale inv_scale h_scale h_inv_d

/-- Berezinian homothety balance in balanced dimension $(p \mid p)$:
    $c^p \cdot (c^{-1})^p = 1$. -/
theorem balanced_homothety_berezinian_eq_one (p : ℕ) (c inv_c : R) (h : c * inv_c = 1) :
    (c ^ p) * (inv_c ^ p) = 1 := by
  rw [← mul_pow, h, one_pow]

/-- The algebraic decomposition of the unbalanced Berezinian homothety factor:
    $c^{p+q} \cdot (c^{-1})^q = c^p \cdot (c \cdot c^{-1})^q$. -/
theorem unbalanced_homothety_berezinian_factor (p q : ℕ) (c inv_c : R) :
    (c ^ (p + q)) * (inv_c ^ q) = c ^ p * (c * inv_c) ^ q := by
  calc
    (c ^ (p + q)) * (inv_c ^ q) = (c ^ p * c ^ q) * (inv_c ^ q) := by rw [pow_add]
    _ = c ^ p * (c ^ q * inv_c ^ q) := by rw [mul_assoc]
    _ = c ^ p * (c * inv_c) ^ q := by rw [← mul_pow]

/-- Unbalanced Berezinian projective scaling:
    for $(p+q \mid q)$, uniform homothety by unit $c$ scales the Berezinian volume form by $c^p$. -/
theorem unbalanced_homothety_berezinian (p q : ℕ) (c inv_c : R) (h : c * inv_c = 1) :
    (c ^ (p + q)) * (inv_c ^ q) = c ^ p := by
  rw [unbalanced_homothety_berezinian_factor, h, one_pow, mul_one]

/-! ### 5. Master Verification Certificate -/

/-- Master Verification Certificate bundling all core theorems of the Nuclear Quasiphonon Super-Grassmannian. -/
def NuclearQuasiphononSuperGrassmannianCertificate : Prop :=
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (M N : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R),
    superTrace (M + N) = superTrace M + superTrace N) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (c : R) (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R),
    superTrace (c • M) = c * superTrace M) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R),
    superTrace (-M) = -superTrace M) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (M N : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R),
    superTrace (M - N) = superTrace M - superTrace N) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (V : Matrix ι₀ ι₁ R),
    susyQ V * susyQ V = 0) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (V : Matrix ι₀ ι₁ R),
    susyQ_dag V * susyQ_dag V = 0) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (V : Matrix ι₀ ι₁ R),
    susyH V = Matrix.fromBlocks (V * Vᵀ) 0 0 (Vᵀ * V)) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (V : Matrix ι₀ ι₁ R),
    superTrace (susyH V) = 0) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (σ : R),
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) (R := R) σ) =
      ((Fintype.card ι₀ : R) - (Fintype.card ι₁ : R)) * σ) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (h : Fintype.card ι₀ = Fintype.card ι₁) (σ : R),
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) (R := R) σ) = 0) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R),
    superTrace (chiralMode (ι₀ := ι₀) (ι₁ := ι₁) B C) = 0) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (A : Matrix ι₀ ι₀ R) (D : Matrix ι₁ ι₁ R)
    (h : Matrix.trace A = Matrix.trace D),
    superTrace (volumeMode (ι₀ := ι₀) (ι₁ := ι₁) A D) = 0) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R),
    chiralMode B C * chiralMode B C = Matrix.fromBlocks (B * C) 0 0 (C * B)) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R),
    superTrace ((chiralMode B C) * (chiralMode B C)) = 0) ∧
  (∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (σ : R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (A : Matrix ι₀ ι₀ R) (D : Matrix ι₁ ι₁ R) (hvol : Matrix.trace A = Matrix.trace D),
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) σ + chiralMode B C + volumeMode A D) =
      ((Fintype.card ι₀ : R) - (Fintype.card ι₁ : R)) * σ) ∧
  (∀ {R : Type*} [CommRing R] (a b c d inv_d scale inv_scale : R),
    scale * inv_scale = 1 → d * inv_d = 1 →
    berezinian2 (scale * a) (scale * b) (scale * c) (scale * d) (inv_scale * inv_d) =
      berezinian2 a b c d inv_d) ∧
  (∀ {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (inv_d scale inv_scale : R),
    scale * inv_scale = 1 → M 1 1 * inv_d = 1 →
    berezinianMat (scale • M) (inv_scale * inv_d) = berezinianMat M inv_d) ∧
  (∀ {R : Type*} [CommRing R] (p : ℕ) (c inv_c : R),
    c * inv_c = 1 → (c ^ p) * (inv_c ^ p) = 1) ∧
  (∀ {R : Type*} [CommRing R] (p q : ℕ) (c inv_c : R),
    (c ^ (p + q)) * (inv_c ^ q) = c ^ p * (c * inv_c) ^ q) ∧
  (∀ {R : Type*} [CommRing R] (p q : ℕ) (c inv_c : R),
    c * inv_c = 1 → (c ^ (p + q)) * (inv_c ^ q) = c ^ p)

/-- Verification theorem constructing the master certificate. -/
theorem compile_nuclear_quasiphonon_super_grassmannian :
    NuclearQuasiphononSuperGrassmannianCertificate :=
  ⟨fun M N => superTrace_add M N,
   fun c M => superTrace_smul c M,
   fun M => superTrace_neg M,
   fun M N => superTrace_sub M N,
   fun V => susyQ_sq V,
   fun V => susyQ_dag_sq V,
   fun V => susyH_eq V,
   fun V => superTrace_susyH V,
   fun σ => superTrace_scaleMode σ,
   fun h σ => superTrace_scale_balanced h σ,
   fun B C => superTrace_chiralMode B C,
   fun A D h => superTrace_volumeMode A D h,
   fun B C => chiral_mode_mul B C,
   fun B C => superTrace_chiralSquare B C,
   fun σ B C A D h => total_deformation_superTrace σ B C A D h,
   fun a b c d inv_d scale inv_scale hs hd =>
     berezinian_homothety_balance a b c d inv_d scale inv_scale hs hd,
   fun M inv_d scale inv_scale hs hd =>
     berezinianMat_smul M inv_d scale inv_scale hs hd,
   fun p c inv_c h =>
     balanced_homothety_berezinian_eq_one p c inv_c h,
   fun p q c inv_c =>
     unbalanced_homothety_berezinian_factor p q c inv_c,
   fun p q c inv_c h =>
     unbalanced_homothety_berezinian p q c inv_c h⟩

end CommSupercarrier

/-! ### 6. Deliverable D1a: Erlangen 2.0 Symmetry Actions, `O(ι₀) × O(ι₁)` Covariance & Non-Orthogonality Obstruction -/

section ErlangenD1a

open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
open InfoGeometry.OperatorAlgebra

variable (ι₀ ι₁ : Type*) [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
variable (R : Type*) [CommRing R]

/-- Explicit noncommutativity witness on the graded block matrix supercarrier `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R`
when both sectors are nonempty and `R` is nontrivial. -/
theorem susyQ_susyQ_dag_noncomm [Nonempty ι₀] [Nonempty ι₁] [Nontrivial R] :
    ∃ V : Matrix ι₀ ι₁ R, susyQ V * susyQ_dag V ≠ susyQ_dag V * susyQ V := by
  obtain ⟨i₀⟩ := ‹Nonempty ι₀›
  obtain ⟨i₁⟩ := ‹Nonempty ι₁›
  let V : Matrix ι₀ ι₁ R := Matrix.of fun a b => if a = i₀ ∧ b = i₁ then 1 else 0
  refine ⟨V, fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R => M (Sum.inl i₀) (Sum.inl i₀)) h
  simp [V, susyQ, susyQ_dag, Matrix.fromBlocks_multiply, Matrix.mul_apply] at h00

/-- Embed `(g₀, g₁) : GL(ι₀, R) × GL(ι₁, R)` as a block-diagonal unit in `GL(ι₀ ⊕ ι₁, R)`. -/
def blockDiagGL
    (g : Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R) :
    Matrix.GeneralLinearGroup (ι₀ ⊕ ι₁) R where
  val := Matrix.fromBlocks g.1.1 0 0 g.2.1
  inv := Matrix.fromBlocks g.1⁻¹.1 0 0 g.2⁻¹.1
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp [← Matrix.fromBlocks_one]
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp [← Matrix.fromBlocks_one]

/-- Group homomorphism `GL(ι₀, R) × GL(ι₁, R) →* GL(ι₀ ⊕ ι₁, R)`. -/
def blockDiagGLHom :
    (Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R) →*
      Matrix.GeneralLinearGroup (ι₀ ⊕ ι₁) R where
  toFun := blockDiagGL ι₀ ι₁ R
  map_one' := by
    ext i j
    simp [blockDiagGL, Matrix.fromBlocks_one]
  map_mul' g h := by
    ext i j
    simp [blockDiagGL, Matrix.fromBlocks_multiply]

/-- Linear equivalence on `(ι₀ ⊕ ι₁) → R` induced by `blockDiagGL g`. -/
noncomputable def blockDiagLinearEquiv
    (g : Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R) :
    ((ι₀ ⊕ ι₁) → R) ≃ₗ[R] ((ι₀ ⊕ ι₁) → R) where
  toLinearMap := Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g).1
  invFun := Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g)⁻¹.1
  left_inv v := by
    have hmul : (blockDiagGL ι₀ ι₁ R g)⁻¹.1 * (blockDiagGL ι₀ ι₁ R g).1 = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    change (Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g)⁻¹.1 *
      Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g).1) v = v
    rw [← map_mul, hmul, map_one]
    rfl
  right_inv v := by
    have hmul : (blockDiagGL ι₀ ι₁ R g).1 * (blockDiagGL ι₀ ι₁ R g)⁻¹.1 = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    change (Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g).1 *
      Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g)⁻¹.1) v = v
    rw [← map_mul, hmul, map_one]
    rfl

/-- Orthogonal subgroup `O(n, R) ≤ GL(n, R)` defined via `u * uᵀ = 1` over any `[CommRing R]`
(avoiding `starRingOfComm` vs `StarRing` diamonds). -/
def orthogonalGLSubgroup (n : Type*) [DecidableEq n] [Fintype n]
    (R : Type*) [CommRing R] : Subgroup (Matrix.GeneralLinearGroup n R) where
  carrier := {u | (u : Matrix n n R) * (u : Matrix n n R)ᵀ = 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    change (u.1 * v.1) * (u.1 * v.1)ᵀ = 1
    rw [Matrix.transpose_mul]
    calc
      (u.1 * v.1) * (v.1ᵀ * u.1ᵀ) = u.1 * (v.1 * v.1ᵀ) * u.1ᵀ := by
        simp only [Matrix.mul_assoc]
      _ = u.1 * 1 * u.1ᵀ := by rw [hv]
      _ = u.1 * u.1ᵀ := by rw [Matrix.mul_one]
      _ = 1 := hu
  inv_mem' {u} hu := by
    change u⁻¹.1 * u⁻¹.1ᵀ = 1
    have hinv : u⁻¹.1 = u.1ᵀ := by
      calc
        u⁻¹.1 = u⁻¹.1 * (u.1 * u.1ᵀ) := by rw [hu, Matrix.mul_one]
        _ = (u⁻¹.1 * u.1) * u.1ᵀ := (Matrix.mul_assoc _ _ _).symm
        _ = u.1ᵀ := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [hinv, Matrix.transpose_transpose]
    calc
      u.1ᵀ * u.1 = (u⁻¹.1) * u.1 := by rw [hinv]
      _ = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- For every `u ∈ orthogonalGLSubgroup n R`, the inverse matrix equals the transpose `u⁻¹.1 = u.1ᵀ`. -/
theorem orthogonalGL_inv_eq_transpose {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (u : orthogonalGLSubgroup n R) :
    (u.1⁻¹ : Matrix.GeneralLinearGroup n R).1 = u.1.1ᵀ := by
  calc
    u.1⁻¹.1 = u.1⁻¹.1 * (u.1.1 * u.1.1ᵀ) := by rw [u.2, Matrix.mul_one]
    _ = (u.1⁻¹.1 * u.1.1) * u.1.1ᵀ := (Matrix.mul_assoc _ _ _).symm
    _ = u.1.1ᵀ := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-- Canonical embedding of Mathlib's real `Matrix.orthogonalGroup n ℝ` into
`orthogonalGLSubgroup n ℝ`. -/
def ofMathlibOrthogonalGroup {n : Type*} [DecidableEq n] [Fintype n]
    (u : Matrix.orthogonalGroup n ℝ) : orthogonalGLSubgroup n ℝ :=
  ⟨⟨u.1, u.1ᵀ,
      (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mp u.2,
      (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp u.2⟩,
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mp u.2⟩

/-- Conjugation `R`-algebra equivalence of `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R` by `blockDiagGL g`. -/
def superBlockGLConjugationEquiv
    (g : Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R) :
    Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R ≃ₐ[R] Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R where
  toFun M := (blockDiagGL ι₀ ι₁ R g).1 * M * (blockDiagGL ι₀ ι₁ R g)⁻¹.1
  invFun M := (blockDiagGL ι₀ ι₁ R g)⁻¹.1 * M * (blockDiagGL ι₀ ι₁ R g).1
  left_inv M := by
    calc
      (blockDiagGL ι₀ ι₁ R g)⁻¹.1 *
          ((blockDiagGL ι₀ ι₁ R g).1 * M * (blockDiagGL ι₀ ι₁ R g)⁻¹.1) *
          (blockDiagGL ι₀ ι₁ R g).1
          = ((blockDiagGL ι₀ ι₁ R g)⁻¹ * blockDiagGL ι₀ ι₁ R g).1 * M *
              ((blockDiagGL ι₀ ι₁ R g)⁻¹ * blockDiagGL ι₀ ι₁ R g).1 := by
                simp only [Units.val_mul, Matrix.mul_assoc]
      _ = M := by simp
  right_inv M := by
    calc
      (blockDiagGL ι₀ ι₁ R g).1 *
          ((blockDiagGL ι₀ ι₁ R g)⁻¹.1 * M * (blockDiagGL ι₀ ι₁ R g).1) *
          (blockDiagGL ι₀ ι₁ R g)⁻¹.1
          = (blockDiagGL ι₀ ι₁ R g * (blockDiagGL ι₀ ι₁ R g)⁻¹).1 * M *
              (blockDiagGL ι₀ ι₁ R g * (blockDiagGL ι₀ ι₁ R g)⁻¹).1 := by
                simp only [Units.val_mul, Matrix.mul_assoc]
      _ = M := by simp
  map_mul' M N := by
    calc
      (blockDiagGL ι₀ ι₁ R g).1 * (M * N) * (blockDiagGL ι₀ ι₁ R g)⁻¹.1
          = (blockDiagGL ι₀ ι₁ R g).1 * M *
              ((blockDiagGL ι₀ ι₁ R g)⁻¹ * blockDiagGL ι₀ ι₁ R g).1 * N *
              (blockDiagGL ι₀ ι₁ R g)⁻¹.1 := by
                simp only [inv_mul_cancel, Units.val_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = ((blockDiagGL ι₀ ι₁ R g).1 * M * (blockDiagGL ι₀ ι₁ R g)⁻¹.1) *
            ((blockDiagGL ι₀ ι₁ R g).1 * N * (blockDiagGL ι₀ ι₁ R g)⁻¹.1) := by
              simp only [Units.val_mul, Matrix.mul_assoc]
  map_add' M N := by rw [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- Symmetry action of `GL(ι₀, R) × GL(ι₁, R)` on `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R` by
block-diagonal conjugation. -/
def superBlockGLSymmetryAction :
    SymmetryAction (Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R)
      (Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) where
  act g := (superBlockGLConjugationEquiv ι₀ ι₁ R g).toRingEquiv
  act_one M := by
    change (blockDiagGL ι₀ ι₁ R 1).1 * M * (blockDiagGL ι₀ ι₁ R 1)⁻¹.1 = M
    have h1 : blockDiagGL ι₀ ι₁ R 1 = 1 := (blockDiagGLHom ι₀ ι₁ R).map_one
    rw [h1, inv_one]
    simp
  act_mul g h M := by
    change (blockDiagGL ι₀ ι₁ R (g * h)).1 * M * (blockDiagGL ι₀ ι₁ R (g * h))⁻¹.1 =
      (blockDiagGL ι₀ ι₁ R g).1 * ((blockDiagGL ι₀ ι₁ R h).1 * M * (blockDiagGL ι₀ ι₁ R h)⁻¹.1) *
        (blockDiagGL ι₀ ι₁ R g)⁻¹.1
    have hgh : blockDiagGL ι₀ ι₁ R (g * h) = blockDiagGL ι₀ ι₁ R g * blockDiagGL ι₀ ι₁ R h :=
      (blockDiagGLHom ι₀ ι₁ R).map_mul g h
    rw [hgh, _root_.mul_inv_rev]
    simp only [Units.val_mul, Matrix.mul_assoc]

@[simp] theorem superBlockGLSymmetryAction_act
    (g : Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R)
    (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    (superBlockGLSymmetryAction ι₀ ι₁ R).act g M =
      (blockDiagGL ι₀ ι₁ R g).1 * M * (blockDiagGL ι₀ ι₁ R g)⁻¹.1 := by
  dsimp [superBlockGLSymmetryAction, superBlockGLConjugationEquiv]

/-- Restricted symmetry action of the orthogonal subgroup `O(ι₀, R) × O(ι₁, R)` on
`Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R`. -/
def superBlockOrthogonalSymmetryAction :
    SymmetryAction (orthogonalGLSubgroup ι₀ R × orthogonalGLSubgroup ι₁ R)
      (Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) where
  act u := (superBlockGLSymmetryAction ι₀ ι₁ R).act (u.1.1, u.2.1)
  act_one M := (superBlockGLSymmetryAction ι₀ ι₁ R).act_one M
  act_mul u v M := (superBlockGLSymmetryAction ι₀ ι₁ R).act_mul (u.1.1, u.2.1) (v.1.1, v.2.1) M

/-- Explicit block action formula for `superBlockGLSymmetryAction` on `Matrix.fromBlocks A B C D`. -/
theorem superBlockGLSymmetryAction_blocks
    (g : Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R)
    (A : Matrix ι₀ ι₀ R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R) (D : Matrix ι₁ ι₁ R) :
    (superBlockGLSymmetryAction ι₀ ι₁ R).act g (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (g.1.1 * A * g.1⁻¹.1) (g.1.1 * B * g.2⁻¹.1)
        (g.2.1 * C * g.1⁻¹.1) (g.2.1 * D * g.2⁻¹.1) := by
  rw [superBlockGLSymmetryAction_act]
  have hinv : (blockDiagGL ι₀ ι₁ R g)⁻¹.1 = Matrix.fromBlocks g.1⁻¹.1 0 0 g.2⁻¹.1 := rfl
  have hval : (blockDiagGL ι₀ ι₁ R g).1 = Matrix.fromBlocks g.1.1 0 0 g.2.1 := rfl
  rw [hval, hinv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Full `GL(ι₀, R) × GL(ι₁, R)` conjugation invariance of `superTrace`. -/
theorem superTrace_superBlockGL_invariant
    (g : Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R)
    (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    superTrace ((superBlockGLSymmetryAction ι₀ ι₁ R).act g M) = superTrace M := by
  have hM : M = Matrix.fromBlocks (Matrix.toBlocks₁₁ M) (Matrix.toBlocks₁₂ M)
      (Matrix.toBlocks₂₁ M) (Matrix.toBlocks₂₂ M) := (Matrix.fromBlocks_toBlocks M).symm
  conv_lhs => rw [hM, superBlockGLSymmetryAction_blocks]
  dsimp [superTrace]
  change (g.1.1 * Matrix.toBlocks₁₁ M * g.1⁻¹.1).trace -
      (g.2.1 * Matrix.toBlocks₂₂ M * g.2⁻¹.1).trace =
    (Matrix.toBlocks₁₁ M).trace - (Matrix.toBlocks₂₂ M).trace
  rw [Matrix.trace_mul_comm (g.1.1 * Matrix.toBlocks₁₁ M) g.1⁻¹.1,
    Matrix.trace_mul_comm (g.2.1 * Matrix.toBlocks₂₂ M) g.2⁻¹.1,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, ← Units.val_mul]
  simp only [inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-- `superTrace` packaged as an `InvariantReadout` for `superBlockGLSymmetryAction`. -/
def superTraceInvariantReadout :
    InvariantReadout (superBlockGLSymmetryAction ι₀ ι₁ R) R :=
  InvariantReadout.mk superTrace (superTrace_superBlockGL_invariant ι₀ ι₁ R)

/-- Every homothety `scaleMode σ` lies in the `GL(ι₀, R) × GL(ι₁, R)` invariant subring. -/
theorem scaleMode_mem_invariantSubring (σ : R) :
    scaleMode (ι₀ := ι₀) (ι₁ := ι₁) σ ∈
      invariantSubring (superBlockGLSymmetryAction ι₀ ι₁ R) := by
  intro g
  change (superBlockGLSymmetryAction ι₀ ι₁ R).act g (scaleMode σ) = scaleMode σ
  dsimp [scaleMode]
  rw [superBlockGLSymmetryAction_blocks]
  simp only [Matrix.mul_zero, Matrix.zero_mul]
  congr 1
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]

/-- Action of `GL(ι₀, R) × GL(ι₁, R)` on `chiralMode B C`. -/
theorem superBlockGL_chiralMode
    (g : Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R)
    (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R) :
    (superBlockGLSymmetryAction ι₀ ι₁ R).act g (chiralMode B C) =
      chiralMode (g.1.1 * B * g.2⁻¹.1) (g.2.1 * C * g.1⁻¹.1) := by
  dsimp [chiralMode]
  rw [superBlockGLSymmetryAction_blocks]
  simp

/-- Action of `GL(ι₀, R) × GL(ι₁, R)` on `volumeMode A D`. -/
theorem superBlockGL_volumeMode
    (g : Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R)
    (A : Matrix ι₀ ι₀ R) (D : Matrix ι₁ ι₁ R) :
    (superBlockGLSymmetryAction ι₀ ι₁ R).act g (volumeMode A D) =
      volumeMode (g.1.1 * A * g.1⁻¹.1) (g.2.1 * D * g.2⁻¹.1) := by
  dsimp [volumeMode]
  rw [superBlockGLSymmetryAction_blocks]
  simp

/-- The odd chiral supercharge anticommutator `{susyQ V, susyQ_dag V}` generates the even
`volumeMode (V * Vᵀ) (Vᵀ * V)` (= `susyH V`). -/
theorem susyH_odd_anticomm_generates_volumeMode (V : Matrix ι₀ ι₁ R) :
    susyQ V * susyQ_dag V + susyQ_dag V * susyQ V = volumeMode (V * Vᵀ) (Vᵀ * V) := by
  rw [← susyH, susyH_eq]
  dsimp [volumeMode]

/-- Orthogonal covariance of `susyQ`: `O(ι₀, R) × O(ι₁, R)` conjugation sends
`susyQ V` to `susyQ (u₀ * V * u₁ᵀ)`. -/
theorem superBlockOrthogonal_susyQ
    (u : orthogonalGLSubgroup ι₀ R × orthogonalGLSubgroup ι₁ R)
    (V : Matrix ι₀ ι₁ R) :
    (superBlockOrthogonalSymmetryAction ι₀ ι₁ R).act u (susyQ V) =
      susyQ (u.1.1.1 * V * u.2.1.1ᵀ) := by
  change (superBlockGLSymmetryAction ι₀ ι₁ R).act (u.1.1, u.2.1) (susyQ V) =
    susyQ (u.1.1.1 * V * u.2.1.1ᵀ)
  dsimp [susyQ]
  rw [superBlockGLSymmetryAction_blocks, orthogonalGL_inv_eq_transpose u.2]
  simp

/-- Orthogonal covariance of `susyQ_dag`: `O(ι₀, R) × O(ι₁, R)` conjugation sends
`susyQ_dag V` to `susyQ_dag (u₀ * V * u₁ᵀ)`. -/
theorem superBlockOrthogonal_susyQ_dag
    (u : orthogonalGLSubgroup ι₀ R × orthogonalGLSubgroup ι₁ R)
    (V : Matrix ι₀ ι₁ R) :
    (superBlockOrthogonalSymmetryAction ι₀ ι₁ R).act u (susyQ_dag V) =
      susyQ_dag (u.1.1.1 * V * u.2.1.1ᵀ) := by
  change (superBlockGLSymmetryAction ι₀ ι₁ R).act (u.1.1, u.2.1) (susyQ_dag V) =
    susyQ_dag (u.1.1.1 * V * u.2.1.1ᵀ)
  dsimp [susyQ_dag]
  rw [superBlockGLSymmetryAction_blocks, orthogonalGL_inv_eq_transpose u.1]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- Orthogonal covariance of `susyH`: `O(ι₀, R) × O(ι₁, R)` conjugation sends
`susyH V` to `susyH (u₀ * V * u₁ᵀ)`. -/
theorem superBlockOrthogonal_susyH
    (u : orthogonalGLSubgroup ι₀ R × orthogonalGLSubgroup ι₁ R)
    (V : Matrix ι₀ ι₁ R) :
    (superBlockOrthogonalSymmetryAction ι₀ ι₁ R).act u (susyH V) =
      susyH (u.1.1.1 * V * u.2.1.1ᵀ) := by
  dsimp [susyH]
  rw [RingEquiv.map_add, RingEquiv.map_mul, RingEquiv.map_mul,
    superBlockOrthogonal_susyQ, superBlockOrthogonal_susyQ_dag]

/-- If `u₀ * V * u₁ᵀ = V`, then `susyH V` lies in the `O(ι₀, R) × O(ι₁, R)` invariant subring. -/
theorem susyH_mem_invariantSubring_of_intertwine
    (u : orthogonalGLSubgroup ι₀ R × orthogonalGLSubgroup ι₁ R)
    (V : Matrix ι₀ ι₁ R) (hV : u.1.1.1 * V * u.2.1.1ᵀ = V) :
    (superBlockOrthogonalSymmetryAction ι₀ ι₁ R).act u (susyH V) = susyH V := by
  rw [superBlockOrthogonal_susyH, hV]

/-- **Non-Orthogonality Obstruction under Full `GL(ι₀, R) × GL(ι₁, R)` Conjugation**:
conjugating `susyH V` by general `(g₀, g₁) ∈ GL(ι₀, R) × GL(ι₁, R)` differs from
`susyH (g₀ * V * g₁⁻¹)` by the explicit non-orthogonality defects `(1 - g₁⁻¹ * g₁⁻¹ᵀ)`,
`(g₀⁻¹ - g₀ᵀ)`, `(1 - g₀ᵀ * g₀)`, and `(g₁⁻¹ - g₁ᵀ)`, which vanish identically on `O(ι₀) × O(ι₁)`. -/
theorem superBlockGL_susyH_nonorthogonality_obstruction
    (g : Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R)
    (V : Matrix ι₀ ι₁ R) :
    (superBlockGLSymmetryAction ι₀ ι₁ R).act g (susyH V) -
      susyH (g.1.1 * V * g.2⁻¹.1) =
      Matrix.fromBlocks
        (g.1.1 * V * (1 - g.2⁻¹.1 * g.2⁻¹.1ᵀ) * Vᵀ * g.1⁻¹.1 +
          g.1.1 * V * g.2⁻¹.1 * g.2⁻¹.1ᵀ * Vᵀ * (g.1⁻¹.1 - g.1.1ᵀ))
        0 0
        (g.2.1 * Vᵀ * (1 - g.1.1ᵀ * g.1.1) * V * g.2⁻¹.1 +
          (g.2.1 - g.2⁻¹.1ᵀ) * Vᵀ * g.1.1ᵀ * g.1.1 * V * g.2⁻¹.1) := by
  rw [susyH_eq, susyH_eq, superBlockGLSymmetryAction_blocks]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_add]
  simp only [Matrix.mul_zero, Matrix.zero_mul, neg_zero, add_zero]
  congr 1
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc]
    abel

section ErlangenWiring

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Explicit `Erlangen20Datum` on `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R` under `GL(ι₀, R) × GL(ι₁, R)`. -/
noncomputable def superGrassmannianErlangen20Datum :
    Erlangen20Datum R ((ι₀ ⊕ ι₁) → R) (Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R)
      (SymmetryAction (Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R)
        (Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R))
      (Subring (Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R)) :=
  InfoGeometry.Canonical.Erlangen20Unification.erlangen20DatumOfSymmetryActionOnModule
    (superBlockGLSymmetryAction ι₀ ι₁ R) Matrix.toLinAlgEquiv'.toAlgHom LinearMap.id
    (fun X Y => Ring.lie_def X Y)

/-- Explicit `Erlangen20Datum` on `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R` under `O(ι₀, R) × O(ι₁, R)`. -/
noncomputable def superGrassmannianOrthogonalErlangen20Datum :
    Erlangen20Datum R ((ι₀ ⊕ ι₁) → R) (Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R)
      (SymmetryAction (orthogonalGLSubgroup ι₀ R × orthogonalGLSubgroup ι₁ R)
        (Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R))
      (Subring (Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R)) :=
  InfoGeometry.Canonical.Erlangen20Unification.erlangen20DatumOfSymmetryActionOnModule
    (superBlockOrthogonalSymmetryAction ι₀ ι₁ R) Matrix.toLinAlgEquiv'.toAlgHom LinearMap.id
    (fun X Y => Ring.lie_def X Y)

/-- Lift `blockDiagGLHom` into the units of `superGrassmannianErlangen20Datum.operatorAlgebra`. -/
noncomputable def blockDiagOperatorAlgUnitHom :
    (Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R) →*
      (superGrassmannianErlangen20Datum ι₀ ι₁ R).operatorAlgebraˣ where
  toFun g :=
    { val := ⟨Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g).1, ⟨(blockDiagGL ι₀ ι₁ R g).1, rfl⟩⟩
      inv := ⟨Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g)⁻¹.1,
        ⟨(blockDiagGL ι₀ ι₁ R g)⁻¹.1, rfl⟩⟩
      val_inv := by
        apply Subtype.ext
        change Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g).1 *
          Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g)⁻¹.1 = 1
        rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
      inv_val := by
        apply Subtype.ext
        change Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g)⁻¹.1 *
          Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g).1 = 1
        rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one] }
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    change Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R 1).1 = 1
    have h1 : blockDiagGL ι₀ ι₁ R 1 = 1 := (blockDiagGLHom ι₀ ι₁ R).map_one
    rw [h1, Units.val_one, map_one]
  map_mul' g h := by
    apply Units.ext
    apply Subtype.ext
    change Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R (g * h)).1 =
      Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R g).1 *
        Matrix.toLinAlgEquiv' (blockDiagGL ι₀ ι₁ R h).1
    have hgh : blockDiagGL ι₀ ι₁ R (g * h) = blockDiagGL ι₀ ι₁ R g * blockDiagGL ι₀ ι₁ R h :=
      (blockDiagGLHom ι₀ ι₁ R).map_mul g h
    rw [hgh, Units.val_mul, map_mul]

/-- `Matrix.toLinAlgEquiv'` intertwines `superBlockGLSymmetryAction` with
`Erlangen20Unification.erlangen20EndSymmetryAction`. -/
theorem toLinAlgEquiv_superBlockGL_eq_erlangen20EndSymmetryAction
    (g : Matrix.GeneralLinearGroup ι₀ R × Matrix.GeneralLinearGroup ι₁ R)
    (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    Matrix.toLinAlgEquiv' ((superBlockGLSymmetryAction ι₀ ι₁ R).act g M) =
      (InfoGeometry.Canonical.Erlangen20Unification.erlangen20EndSymmetryAction
        (superGrassmannianErlangen20Datum ι₀ ι₁ R)
        (blockDiagOperatorAlgUnitHom ι₀ ι₁ R)).act g (Matrix.toLinAlgEquiv' M) := by
  rw [superBlockGLSymmetryAction_act, map_mul, map_mul]
  rfl

/-- Explicit `OperatorIntertwiner` on `(ι₀ ⊕ ι₁) → R` conjugating `susyH V` under
`u ∈ O(ι₀, R) × O(ι₁, R)`. -/
noncomputable def susyH_orthogonal_operatorIntertwiner
    (u : orthogonalGLSubgroup ι₀ R × orthogonalGLSubgroup ι₁ R)
    (V : Matrix ι₀ ι₁ R) :
    OperatorIntertwiner R ((ι₀ ⊕ ι₁) → R) ((ι₀ ⊕ ι₁) → R) :=
  InfoGeometry.Canonical.Erlangen20Unification.operatorIntertwinerOfLinearEquiv
    (blockDiagLinearEquiv ι₀ ι₁ R (u.1.1, u.2.1))
    (Matrix.toLinAlgEquiv' (susyH V))

/-- The target operator of `susyH_orthogonal_operatorIntertwiner u V` is literally
`Matrix.toLinAlgEquiv' (susyH (u₀ * V * u₁ᵀ))`. -/
theorem susyH_orthogonal_operatorIntertwiner_target
    (u : orthogonalGLSubgroup ι₀ R × orthogonalGLSubgroup ι₁ R)
    (V : Matrix ι₀ ι₁ R) :
    (susyH_orthogonal_operatorIntertwiner ι₀ ι₁ R u V).target =
      Matrix.toLinAlgEquiv' (susyH (u.1.1.1 * V * u.2.1.1ᵀ)) := by
  dsimp [susyH_orthogonal_operatorIntertwiner,
    InfoGeometry.Canonical.Erlangen20Unification.operatorIntertwinerOfLinearEquiv,
    InfoGeometry.Canonical.Erlangen20Unification.conjEndAlgEquiv]
  have hact :
      (blockDiagLinearEquiv ι₀ ι₁ R (u.1.1, u.2.1)).toLinearMap.comp
          ((Matrix.toLinAlgEquiv' (susyH V)).comp
            (blockDiagLinearEquiv ι₀ ι₁ R (u.1.1, u.2.1)).symm.toLinearMap) =
        Matrix.toLinAlgEquiv' ((blockDiagGL ι₀ ι₁ R (u.1.1, u.2.1)).1 * susyH V *
          (blockDiagGL ι₀ ι₁ R (u.1.1, u.2.1))⁻¹.1) := by
    rw [map_mul, map_mul]
    rfl
  rw [hact, ← superBlockGLSymmetryAction_act]
  exact congrArg Matrix.toLinAlgEquiv' (superBlockOrthogonal_susyH ι₀ ι₁ R u V)

/-- Real `OperatorSymmetryAction` of `GL(ι₀, ℝ) × GL(ι₁, ℝ)` on `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℝ`. -/
def superBlockGLOperatorSymmetryAction :
    OperatorSymmetryAction (Matrix.GeneralLinearGroup ι₀ ℝ × Matrix.GeneralLinearGroup ι₁ ℝ)
      (Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℝ) where
  toFun g := superBlockGLConjugationEquiv ι₀ ι₁ ℝ g⁻¹
  map_one' := by
    apply AlgEquiv.ext
    intro M
    dsimp [superBlockGLConjugationEquiv]
    have h1 : blockDiagGL ι₀ ι₁ ℝ (1 : _) = 1 := (blockDiagGLHom ι₀ ι₁ ℝ).map_one
    rw [inv_one, h1]
    simp
  map_mul' g h := by
    apply AlgEquiv.ext
    intro M
    dsimp [superBlockGLConjugationEquiv]
    have hinv : blockDiagGL ι₀ ι₁ ℝ (g * h)⁻¹ =
        blockDiagGL ι₀ ι₁ ℝ h⁻¹ * blockDiagGL ι₀ ι₁ ℝ g⁻¹ := by
      rw [_root_.mul_inv_rev]
      exact (blockDiagGLHom ι₀ ι₁ ℝ).map_mul h⁻¹ g⁻¹
    rw [hinv, _root_.mul_inv_rev]
    simp only [Units.val_mul, Matrix.mul_assoc]

theorem toSymmetryAction_superBlockGLOperatorSymmetryAction :
    toSymmetryAction (superBlockGLOperatorSymmetryAction ι₀ ι₁) =
      superBlockGLSymmetryAction ι₀ ι₁ ℝ := by
  have hact : ∀ g : Matrix.GeneralLinearGroup ι₀ ℝ × Matrix.GeneralLinearGroup ι₁ ℝ,
      (toSymmetryAction (superBlockGLOperatorSymmetryAction ι₀ ι₁)).act g =
        (superBlockGLSymmetryAction ι₀ ι₁ ℝ).act g := by
    intro g
    apply RingEquiv.ext
    intro M
    change (superBlockGLConjugationEquiv ι₀ ι₁ ℝ (g⁻¹)⁻¹) M =
      (superBlockGLConjugationEquiv ι₀ ι₁ ℝ g) M
    rw [inv_inv]
  cases h1 : toSymmetryAction (superBlockGLOperatorSymmetryAction ι₀ ι₁)
  cases h2 : superBlockGLSymmetryAction ι₀ ι₁ ℝ
  simp only [SymmetryAction.mk.injEq]
  funext g
  have hg := hact g
  rw [h1, h2] at hg
  exact hg

end ErlangenWiring

end ErlangenD1a

/-! ### 7. Deliverable D2: Generalized Block Berezinian, Homothety Scaling & Feshbach–SUSY Bridge -/

section BerezinianFeshbachD2

open InfoGeometry.Algebra.BdGSchurBerezinianCompatibility
open InfoGeometry.Physics
open InfoGeometry.Supergeometry

section CommBlockBerezinian

variable {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
variable {R : Type*} [CommRing R]

/-- General `(ι₀ | ι₁)` block Berezinian defined via `blockSchurComplement`:
`Ber(M) = det(A - B * D_inv * C) * det(D_inv)`. -/
def blockBerezinian (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) (D_inv : Matrix ι₁ ι₁ R) : R :=
  (blockSchurComplement (Matrix.toBlocks₁₁ M) (Matrix.toBlocks₁₂ M)
    (Matrix.toBlocks₂₁ M) D_inv).det * D_inv.det

/-- Determinant identity `blockBerezinian M D_inv = det(M) * (det(D_inv))^2` whenever
`D_inv` is the two-sided inverse of `toBlocks₂₂ M`. -/
theorem blockBerezinian_eq_det_mul_det_inv_sq
    (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) (D_inv : Matrix ι₁ ι₁ R)
    (hDR : Matrix.toBlocks₂₂ M * D_inv = 1) (hDL : D_inv * Matrix.toBlocks₂₂ M = 1) :
    blockBerezinian M D_inv = M.det * (D_inv.det) ^ 2 := by
  have hM : M = Matrix.fromBlocks (Matrix.toBlocks₁₁ M) (Matrix.toBlocks₁₂ M)
      (Matrix.toBlocks₂₁ M) (Matrix.toBlocks₂₂ M) := (Matrix.fromBlocks_toBlocks M).symm
  have hdet := det_fromBlocks_eq_det_schur_mul_det_D (Matrix.toBlocks₁₁ M)
    (Matrix.toBlocks₁₂ M) (Matrix.toBlocks₂₁ M) (Matrix.toBlocks₂₂ M) D_inv hDR hDL
  rw [← hM] at hdet
  have hDD : (Matrix.toBlocks₂₂ M).det * D_inv.det = 1 := by
    rw [← Matrix.det_mul, hDR, Matrix.det_one]
  dsimp [blockBerezinian]
  calc
    (blockSchurComplement (Matrix.toBlocks₁₁ M) (Matrix.toBlocks₁₂ M)
        (Matrix.toBlocks₂₁ M) D_inv).det * D_inv.det
        = (blockSchurComplement (Matrix.toBlocks₁₁ M) (Matrix.toBlocks₁₂ M)
            (Matrix.toBlocks₂₁ M) D_inv).det * ((Matrix.toBlocks₂₂ M).det * D_inv.det) *
            D_inv.det := by rw [hDD, mul_one]
    _ = ((blockSchurComplement (Matrix.toBlocks₁₁ M) (Matrix.toBlocks₁₂ M)
            (Matrix.toBlocks₂₁ M) D_inv).det * (Matrix.toBlocks₂₂ M).det) *
            (D_inv.det) ^ 2 := by ring
    _ = M.det * (D_inv.det) ^ 2 := by rw [← hdet]

/-- When the even/bosonic projector `P = fromBlocks 1 0 0 0` commutes with `M` (`[P, M] = 0`),
the off-diagonal odd blocks vanish and `blockBerezinian M D_inv` factors cleanly into
`det(toBlocks₁₁ M) * det(D_inv)` with zero Schur shift. -/
theorem blockBerezinian_of_commute
    (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) (D_inv : Matrix ι₁ ι₁ R)
    (hcomm : Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) 0 0 0 * M -
      M * Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) 0 0 0 = 0) :
    blockBerezinian M D_inv = (Matrix.toBlocks₁₁ M).det * D_inv.det := by
  have hM : M = Matrix.fromBlocks (Matrix.toBlocks₁₁ M) (Matrix.toBlocks₁₂ M)
      (Matrix.toBlocks₂₁ M) (Matrix.toBlocks₂₂ M) := (Matrix.fromBlocks_toBlocks M).symm
  rw [hM] at hcomm
  obtain ⟨_, _, hS⟩ := blockSchurComplement_of_commute (Matrix.toBlocks₁₁ M)
    (Matrix.toBlocks₁₂ M) (Matrix.toBlocks₂₁ M) (Matrix.toBlocks₂₂ M) D_inv hcomm
  dsimp [blockBerezinian]
  rw [hS]

/-- General block Berezinian homothety scaling law under `c • M` and `inv_c • D_inv` when
`c * inv_c = 1`: `Ber(c • M) = (c ^ |ι₀| * inv_c ^ |ι₁|) * Ber(M)`. -/
theorem blockBerezinian_smul
    (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) (D_inv : Matrix ι₁ ι₁ R)
    (c inv_c : R) (hc : c * inv_c = 1) :
    blockBerezinian (c • M) (inv_c • D_inv) =
      (c ^ Fintype.card ι₀ * inv_c ^ Fintype.card ι₁) * blockBerezinian M D_inv := by
  have hschur :
      blockSchurComplement (Matrix.toBlocks₁₁ (c • M)) (Matrix.toBlocks₁₂ (c • M))
          (Matrix.toBlocks₂₁ (c • M)) (inv_c • D_inv) =
        c • blockSchurComplement (Matrix.toBlocks₁₁ M) (Matrix.toBlocks₁₂ M)
          (Matrix.toBlocks₂₁ M) D_inv := by
    dsimp [blockSchurComplement]
    change (c • Matrix.toBlocks₁₁ M) - (c • Matrix.toBlocks₁₂ M) * (inv_c • D_inv) *
        (c • Matrix.toBlocks₂₁ M) =
      c • (Matrix.toBlocks₁₁ M - Matrix.toBlocks₁₂ M * D_inv * Matrix.toBlocks₂₁ M)
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, hc, one_smul, ← smul_sub]
  unfold blockBerezinian
  rw [hschur, Matrix.det_smul, Matrix.det_smul]
  rw [mul_assoc,
    mul_left_comm (blockSchurComplement (Matrix.toBlocks₁₁ M) (Matrix.toBlocks₁₂ M)
      (Matrix.toBlocks₂₁ M) D_inv).det (inv_c ^ Fintype.card ι₁) D_inv.det,
    ← mul_assoc]

/-- Balanced `(p | p)` block Berezinian homothety invariance: when `|ι₀| = |ι₁|`,
`blockBerezinian (c • M) (inv_c • D_inv) = blockBerezinian M D_inv`. -/
theorem blockBerezinian_smul_balanced
    (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) (D_inv : Matrix ι₁ ι₁ R)
    (hcard : Fintype.card ι₀ = Fintype.card ι₁) (c inv_c : R) (hc : c * inv_c = 1) :
    blockBerezinian (c • M) (inv_c • D_inv) = blockBerezinian M D_inv := by
  rw [blockBerezinian_smul M D_inv c inv_c hc, hcard,
    balanced_homothety_berezinian_eq_one (Fintype.card ι₁) c inv_c hc, one_mul]

/-- Unbalanced `(p + q | q)` block Berezinian projective scaling: when `|ι₀| = p + q` and
`|ι₁| = q`, `blockBerezinian (c • M) (inv_c • D_inv) = c ^ p * blockBerezinian M D_inv`. -/
theorem blockBerezinian_smul_unbalanced
    (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) (D_inv : Matrix ι₁ ι₁ R)
    (p q : ℕ) (hp : Fintype.card ι₀ = p + q) (hq : Fintype.card ι₁ = q)
    (c inv_c : R) (hc : c * inv_c = 1) :
    blockBerezinian (c • M) (inv_c • D_inv) = c ^ p * blockBerezinian M D_inv := by
  rw [blockBerezinian_smul M D_inv c inv_c hc, hp, hq,
    unbalanced_homothety_berezinian p q c inv_c hc]

/-- Index equivalence `(Fin 1 ⊕ Fin 1) ≃ Fin 2`. -/
private def fin1SumFin1EquivFin2 : (Fin 1 ⊕ Fin 1) ≃ Fin 2 where
  toFun
    | .inl _ => 0
    | .inr _ => 1
  invFun i := if i = 0 then .inl 0 else .inr 0
  left_inv x := by rcases x with a | a <;> fin_cases a <;> simp
  right_inv i := by fin_cases i <;> rfl

/-- `berezinianMat M inv_d` equals `blockBerezinian` on the `(Fin 1 ⊕ Fin 1)` reindexing of `M`. -/
theorem berezinianMat_eq_blockBerezinian
    (M : Matrix (Fin 2) (Fin 2) R) (inv_d : R) :
    berezinianMat M inv_d =
      blockBerezinian (M.submatrix fin1SumFin1EquivFin2 fin1SumFin1EquivFin2)
        (Matrix.of fun _ _ : Fin 1 => inv_d) := by
  dsimp [berezinianMat, berezinian2, blockBerezinian, blockSchurComplement]
  rw [Matrix.det_unique, Matrix.det_unique]
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
    Matrix.submatrix_apply, fin1SumFin1EquivFin2, Matrix.mul_apply, Fin.sum_univ_one]

/-- `berezinianMat M inv_d` coincides identically with `Berezinian.berezinian M inv_d`. -/
theorem berezinianMat_eq_berezinian
    (M : Matrix (Fin 2) (Fin 2) R) (inv_d : R) :
    berezinianMat M inv_d = Berezinian.berezinian M inv_d := by
  dsimp [berezinianMat, berezinian2, Berezinian.berezinian]

/-- Over a `[Field F]`, `berezinianMat M (M 1 1)⁻¹` coincides with `berezinianScalar`. -/
theorem berezinianMat_eq_berezinianScalar {F : Type*} [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) :
    berezinianMat M (M 1 1)⁻¹ = berezinianScalar (M 0 0) (M 1 1) (M 0 1) (M 1 0) := by
  dsimp [berezinianMat, berezinian2, berezinianScalar, schurComplement]
  rw [div_eq_mul_inv]

/-- The Feshbach effective Hamiltonian of the 5-graded deformation triad
`scaleMode σ + chiralMode B C + volumeMode A D` equals the block Schur complement
`blockSchurComplement (σ • 1 + A) B C D_inv`. -/
theorem deformationTriad_feshbach_eq_schurComplement
    (σ : R) (A : Matrix ι₀ ι₀ R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (D D_inv : Matrix ι₁ ι₁ R) :
    NuclearFeshbachReduction.effectiveHamiltonian (blockProjectorP ι₀ ι₁ R)
      (Matrix.toLinAlgEquiv'
        (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) σ + chiralMode B C + volumeMode A D))
      (Matrix.toLinAlgEquiv' (Matrix.fromBlocks 0 0 0 (-D_inv))) =
      Matrix.toLinAlgEquiv'
        (Matrix.fromBlocks (blockSchurComplement (σ • 1 + A) B C D_inv) 0 0 0) := by
  have htriad :
      scaleMode (ι₀ := ι₀) (ι₁ := ι₁) σ + chiralMode B C + volumeMode A D =
        Matrix.fromBlocks (σ • (1 : Matrix ι₀ ι₀ R) + A) B C (σ • (1 : Matrix ι₁ ι₁ R) + D) := by
    dsimp [scaleMode, chiralMode, volumeMode]
    rw [Matrix.fromBlocks_add, Matrix.fromBlocks_add]
    simp [add_assoc]
  rw [htriad]
  exact blockFeshbach_effectiveHamiltonian_eq_schurComplement (σ • 1 + A) B C (σ • 1 + D) D_inv

/-- Over a `[Field K]`, the pure Dirac supercharge operator `susyQ V + susyQ_dag V` has
vanishing `E = 0` Feshbach denominator (`denominator P (toLinAlgEquiv' (susyQ V + susyQ_dag V)) 0 = 0`). -/
theorem susyQ_dirac_denominator_zero_eq_zero {K : Type*} [Field K]
    (V : Matrix ι₀ ι₁ K) :
    NuclearFeshbachReduction.denominator (blockProjectorP ι₀ ι₁ K)
      (Matrix.toLinAlgEquiv' (susyQ V + susyQ_dag V)) 0 = 0 := by
  have h1P : 1 - blockProjectorP ι₀ ι₁ K =
      Matrix.toLinAlgEquiv' (Matrix.fromBlocks (0 : Matrix ι₀ ι₀ K) 0 0 (1 : Matrix ι₁ ι₁ K)) := by
    dsimp [blockProjectorP]
    rw [← map_one (Matrix.toLinAlgEquiv' (R := K) (n := ι₀ ⊕ ι₁)), ← map_sub,
      ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  have hdirac : susyQ V + susyQ_dag V = Matrix.fromBlocks 0 V Vᵀ 0 := by
    dsimp [susyQ, susyQ_dag]
    rw [Matrix.fromBlocks_add]
    simp
  dsimp [NuclearFeshbachReduction.denominator]
  rw [zero_smul, zero_sub, h1P, hdirac, ← map_mul, ← map_mul, ← map_neg,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Consequently, when `Nonempty ι₁` and `[Field K]`, no operator `R_op` can satisfy the
`E = 0` Feshbach denominator-inverse condition for pure `susyQ V + susyQ_dag V`. -/
theorem susyQ_dirac_no_E0_resolvent {K : Type*} [Field K] [Nonempty ι₁]
    (V : Matrix ι₀ ι₁ K) (R_op : Module.End K ((ι₀ ⊕ ι₁) → K)) :
    NuclearFeshbachReduction.denominator (blockProjectorP ι₀ ι₁ K)
      (Matrix.toLinAlgEquiv' (susyQ V + susyQ_dag V)) 0 * R_op ≠
      1 - blockProjectorP ι₀ ι₁ K := by
  intro h
  rw [susyQ_dirac_denominator_zero_eq_zero, zero_mul] at h
  obtain ⟨i₁⟩ := ‹Nonempty ι₁›
  have hv := LinearMap.congr_fun h (Pi.single (Sum.inr i₁) (1 : K))
  have hP0 : blockProjectorP ι₀ ι₁ K (Pi.single (Sum.inr i₁) (1 : K)) = 0 := by
    dsimp [blockProjectorP]
    ext x
    rcases x with a | b <;> simp [Matrix.mulVec_single]
  have h1 := congrFun hv (Sum.inr i₁)
  simp [hP0] at h1

/-- With the canonical `-1` Q-block regulator `H_reg V := susyQ V + susyQ_dag V - fromBlocks 0 0 0 1`,
`E = 0` Feshbach elimination onto the `P`-block produces `P * toLinAlgEquiv' (susyH V) * P`. -/
theorem susyH_feshbach_P_block (V : Matrix ι₀ ι₁ R) :
    let P := blockProjectorP ι₀ ι₁ R
    let H_reg := susyQ V + susyQ_dag V - Matrix.fromBlocks (0 : Matrix ι₀ ι₀ R) 0 0 1
    NuclearFeshbachReduction.effectiveHamiltonian P (Matrix.toLinAlgEquiv' H_reg) (1 - P) =
      P * Matrix.toLinAlgEquiv' (susyH V) * P := by
  intro P H_reg
  have h1P : 1 - P =
      Matrix.toLinAlgEquiv' (Matrix.fromBlocks (0 : Matrix ι₀ ι₀ R) 0 0 (1 : Matrix ι₁ ι₁ R)) := by
    dsimp [P, blockProjectorP]
    rw [← map_one (Matrix.toLinAlgEquiv' (R := R) (n := ι₀ ⊕ ι₁)), ← map_sub,
      ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  have hreg : H_reg = Matrix.fromBlocks 0 V Vᵀ (-1 : Matrix ι₁ ι₁ R) := by
    dsimp [H_reg, susyQ, susyQ_dag]
    rw [Matrix.fromBlocks_add, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  rw [h1P, hreg, show (Matrix.fromBlocks (0 : Matrix ι₀ ι₀ R) 0 0 (1 : Matrix ι₁ ι₁ R)) =
    Matrix.fromBlocks 0 0 0 (-(-1 : Matrix ι₁ ι₁ R)) from by simp]
  rw [blockFeshbach_effectiveHamiltonian_eq_schurComplement]
  dsimp [P, blockProjectorP, blockSchurComplement]
  rw [susyH_eq, ← map_mul, ← map_mul, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Symmetrically, eliminating the `P`-block with `(1 - P)`-projector onto the `Q`-block
produces `(1 - P) * toLinAlgEquiv' (susyH V) * (1 - P)`. -/
theorem susyH_feshbach_Q_block (V : Matrix ι₀ ι₁ R) :
    let P := blockProjectorP ι₀ ι₁ R
    let H_reg' := susyQ V + susyQ_dag V - Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) 0 0 0
    NuclearFeshbachReduction.effectiveHamiltonian (1 - P) (Matrix.toLinAlgEquiv' H_reg') P =
      (1 - P) * Matrix.toLinAlgEquiv' (susyH V) * (1 - P) := by
  intro P H_reg'
  have h1P : 1 - P =
      Matrix.toLinAlgEquiv' (Matrix.fromBlocks (0 : Matrix ι₀ ι₀ R) 0 0 (1 : Matrix ι₁ ι₁ R)) := by
    dsimp [P, blockProjectorP]
    rw [← map_one (Matrix.toLinAlgEquiv' (R := R) (n := ι₀ ⊕ ι₁)), ← map_sub,
      ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  have hreg' : H_reg' = Matrix.fromBlocks (-1 : Matrix ι₀ ι₀ R) V Vᵀ 0 := by
    dsimp [H_reg', susyQ, susyQ_dag]
    rw [Matrix.fromBlocks_add, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  dsimp [NuclearFeshbachReduction.effectiveHamiltonian]
  rw [h1P, hreg', susyH_eq]
  dsimp [P, blockProjectorP]
  simp only [← map_mul, ← map_add, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp

/-- Summing the two complementary Feshbach reductions recovers the full `susyH V` operator. -/
theorem susyH_eq_sum_feshbach (V : Matrix ι₀ ι₁ R) :
    let P := blockProjectorP ι₀ ι₁ R
    let H_reg := susyQ V + susyQ_dag V - Matrix.fromBlocks (0 : Matrix ι₀ ι₀ R) 0 0 1
    let H_reg' := susyQ V + susyQ_dag V - Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) 0 0 0
    NuclearFeshbachReduction.effectiveHamiltonian P (Matrix.toLinAlgEquiv' H_reg) (1 - P) +
      NuclearFeshbachReduction.effectiveHamiltonian (1 - P) (Matrix.toLinAlgEquiv' H_reg') P =
      Matrix.toLinAlgEquiv' (susyH V) := by
  intro P H_reg H_reg'
  rw [susyH_feshbach_P_block, susyH_feshbach_Q_block]
  have h1P : 1 - P =
      Matrix.toLinAlgEquiv' (Matrix.fromBlocks (0 : Matrix ι₀ ι₀ R) 0 0 (1 : Matrix ι₁ ι₁ R)) := by
    dsimp [P, blockProjectorP]
    rw [← map_one (Matrix.toLinAlgEquiv' (R := R) (n := ι₀ ⊕ ι₁)), ← map_sub,
      ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  rw [h1P, susyH_eq]
  dsimp [P, blockProjectorP]
  simp only [← map_mul, ← map_add, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp

/-- At `E = 1` over a `[Field K]`, the un-regulated off-diagonal supercharge sum
`H_dirac := susyQ V + susyQ_dag V` has invertible Feshbach denominator `1 - P` and
`effectiveHamiltonian P (toLinAlgEquiv' H_dirac) (1 - P) = P * toLinAlgEquiv' (susyH V) * P`. -/
theorem susyH_feshbach_E1 {K : Type*} [Field K] (V : Matrix ι₀ ι₁ K) :
    let P := blockProjectorP ι₀ ι₁ K
    let H_dirac := susyQ V + susyQ_dag V
    NuclearFeshbachReduction.denominator P (Matrix.toLinAlgEquiv' H_dirac) 1 * (1 - P) = 1 - P ∧
    NuclearFeshbachReduction.effectiveHamiltonian P (Matrix.toLinAlgEquiv' H_dirac) (1 - P) =
      P * Matrix.toLinAlgEquiv' (susyH V) * P := by
  intro P H_dirac
  have h1P : 1 - P =
      Matrix.toLinAlgEquiv' (Matrix.fromBlocks (0 : Matrix ι₀ ι₀ K) 0 0 (1 : Matrix ι₁ ι₁ K)) := by
    dsimp [P, blockProjectorP]
    rw [← map_one (Matrix.toLinAlgEquiv' (R := K) (n := ι₀ ⊕ ι₁)), ← map_sub,
      ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  have hdirac : H_dirac = Matrix.fromBlocks 0 V Vᵀ 0 := by
    dsimp [H_dirac, susyQ, susyQ_dag]
    rw [Matrix.fromBlocks_add]
    simp
  constructor
  · dsimp [NuclearFeshbachReduction.denominator]
    rw [one_smul, h1P, hdirac]
    have hmul : ∀ A B : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) K,
        Matrix.toLinAlgEquiv' A * Matrix.toLinAlgEquiv' B = Matrix.toLinAlgEquiv' (A * B) :=
      fun A B => (map_mul Matrix.toLinAlgEquiv' A B).symm
    have hsub : ∀ A B : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) K,
        Matrix.toLinAlgEquiv' A - Matrix.toLinAlgEquiv' B = Matrix.toLinAlgEquiv' (A - B) :=
      fun A B => (map_sub Matrix.toLinAlgEquiv' A B).symm
    simp only [hmul, hsub, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, sub_zero, Matrix.one_mul]
    rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_multiply]
    simp
  · dsimp [NuclearFeshbachReduction.effectiveHamiltonian]
    rw [h1P, hdirac, susyH_eq]
    dsimp [P, blockProjectorP]
    simp only [← map_mul, ← map_add, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    simp

/-- For arbitrary invertible Q-block `D` (`D * D_inv = 1`), Feshbach elimination of
`susyQ V + susyQ_dag V + fromBlocks 0 0 0 D` yields `fromBlocks (-V * D_inv * Vᵀ) 0 0 0`. -/
theorem susyH_feshbach_general_D
    (V : Matrix ι₀ ι₁ R) (D D_inv : Matrix ι₁ ι₁ R) :
    NuclearFeshbachReduction.effectiveHamiltonian (blockProjectorP ι₀ ι₁ R)
      (Matrix.toLinAlgEquiv' (susyQ V + susyQ_dag V + Matrix.fromBlocks 0 0 0 D))
      (Matrix.toLinAlgEquiv' (Matrix.fromBlocks 0 0 0 (-D_inv))) =
      Matrix.toLinAlgEquiv' (Matrix.fromBlocks (-V * D_inv * Vᵀ) 0 0 0) := by
  have hH : susyQ V + susyQ_dag V + Matrix.fromBlocks 0 0 0 D =
      Matrix.fromBlocks 0 V Vᵀ D := by
    dsimp [susyQ, susyQ_dag]
    rw [Matrix.fromBlocks_add, Matrix.fromBlocks_add]
    simp
  rw [hH, blockFeshbach_effectiveHamiltonian_eq_schurComplement]
  dsimp [blockSchurComplement]
  simp [Matrix.neg_mul]

end CommBlockBerezinian

end BerezinianFeshbachD2

end InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian
