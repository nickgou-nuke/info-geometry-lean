import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

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

variable {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
variable {R : Type*} [CommRing R]

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
  ring

/-- Scalar multiplication linearity of supertrace: `superTrace (c • M) = c * superTrace M`. -/
theorem superTrace_smul (c : R) (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    superTrace (c • M) = c * superTrace M := by
  dsimp [superTrace]
  rw [Matrix.trace_smul, Matrix.trace_smul]
  ring

/-- Negation linearity of supertrace: `superTrace (-M) = -superTrace M`. -/
theorem superTrace_neg (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R) :
    superTrace (-M) = -superTrace M := by
  dsimp [superTrace]
  rw [Matrix.trace_neg, Matrix.trace_neg]
  ring

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

/-- The Fundamental Real SUSY Vacuum Energy Cancellation:
    $\mathrm{STr}(H_{\mathrm{susy}}(V)) = \mathrm{Tr}(V Vᵀ) - \mathrm{Tr}(Vᵀ V) = 0$
    strictly by cyclic invariance of trace. -/
theorem superTrace_susyH (V : Matrix ι₀ ι₁ R) :
    superTrace (susyH V) = 0 := by
  rw [susyH_eq]
  dsimp [superTrace]
  rw [Matrix.trace_mul_comm V Vᵀ]
  ring

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
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rw [Matrix.trace_one, Matrix.trace_one]
  ring

/-- Balanced scale invariance: when `Fintype.card ι₀ = Fintype.card ι₁`, the scale mode supertrace vanishes. -/
theorem superTrace_scale_balanced (h : Fintype.card ι₀ = Fintype.card ι₁) (σ : R) :
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) (R := R) σ) = 0 := by
  rw [superTrace_scaleMode, h]
  ring

/-- Supertrace of the chiral mode operator vanishes identically: `superTrace (chiralMode B C) = 0`. -/
theorem superTrace_chiralMode (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R) :
    superTrace (chiralMode (ι₀ := ι₀) (ι₁ := ι₁) B C) = 0 := by
  dsimp [superTrace, chiralMode]
  rw [Matrix.trace_zero, Matrix.trace_zero]
  ring

/-- Supertrace of the volume mode operator vanishes when `Matrix.trace A = Matrix.trace D`. -/
theorem superTrace_volumeMode (A : Matrix ι₀ ι₀ R) (D : Matrix ι₁ ι₁ R)
    (h : Matrix.trace A = Matrix.trace D) :
    superTrace (volumeMode (ι₀ := ι₀) (ι₁ := ι₁) A D) = 0 := by
  dsimp [superTrace, volumeMode]
  rw [h]
  ring

/-- Multiplication of two chiral mode operators:
    `chiralMode B C * chiralMode B C = Matrix.fromBlocks (B * C) 0 0 (C * B)`. -/
theorem chiral_mode_mul (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R) :
    chiralMode B C * chiralMode B C = Matrix.fromBlocks (B * C) 0 0 (C * B) := by
  dsimp [chiralMode]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Supertrace of the square of any chiral operator vanishes identically by trace cyclicity:
    `superTrace ((chiralMode B C) * (chiralMode B C)) = 0`. -/
theorem superTrace_chiralSquare (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R) :
    superTrace ((chiralMode B C) * (chiralMode B C)) = 0 := by
  rw [chiral_mode_mul]
  dsimp [superTrace]
  rw [Matrix.trace_mul_comm B C]
  ring

/-- Total deformation splitting theorem:
    `superTrace (scaleMode σ + chiralMode B C + volumeMode A D) = ((Fintype.card ι₀ : R) - (Fintype.card ι₁ : R)) * σ`. -/
theorem total_deformation_superTrace (σ : R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (A : Matrix ι₀ ι₀ R) (D : Matrix ι₁ ι₁ R) (hvol : Matrix.trace A = Matrix.trace D) :
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) σ + chiralMode B C + volumeMode A D) =
      ((Fintype.card ι₀ : R) - (Fintype.card ι₁ : R)) * σ := by
  rw [superTrace_add, superTrace_add]
  rw [superTrace_scaleMode, superTrace_chiralMode, superTrace_volumeMode A D hvol]
  ring

/-! ### 4. Super-Grassmannian Berezinian & Homothety Invariance -/

/-- Berezinian for a 2x2 supermatrix with scalar entries `a, b, c, d` where `d` has specified inverse `inv_d`:
    $\mathrm{Ber} \begin{pmatrix} a & b \\ c & d \end{pmatrix} = (a - b \, d^{-1} \, c) \, d^{-1}$. -/
def berezinian2 (a b c d inv_d : R) : R :=
  (a - b * inv_d * c) * inv_d

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

/-- Berezinian on full 2x2 block matrix carrier `Matrix (Fin 2) (Fin 2) R`:
    evaluates `berezinian2` on matrix components. -/
def berezinianMat (M : Matrix (Fin 2) (Fin 2) R) (inv_d : R) : R :=
  berezinian2 (M 0 0) (M 0 1) (M 1 0) (M 1 1) inv_d

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
structure NuclearQuasiphononSuperGrassmannianCertificate : Prop where
  superTrace_add : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (M N : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R),
    superTrace (M + N) = superTrace M + superTrace N
  superTrace_smul : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (c : R) (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R),
    superTrace (c • M) = c * superTrace M
  superTrace_neg : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R),
    superTrace (-M) = -superTrace M
  superTrace_sub : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (M N : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R),
    superTrace (M - N) = superTrace M - superTrace N
  susyQ_sq : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (V : Matrix ι₀ ι₁ R),
    susyQ V * susyQ V = 0
  susyQ_dag_sq : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (V : Matrix ι₀ ι₁ R),
    susyQ_dag V * susyQ_dag V = 0
  susyH_eq : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (V : Matrix ι₀ ι₁ R),
    susyH V = Matrix.fromBlocks (V * Vᵀ) 0 0 (Vᵀ * V)
  superTrace_susyH : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (V : Matrix ι₀ ι₁ R),
    superTrace (susyH V) = 0
  superTrace_scaleMode : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (σ : R),
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) (R := R) σ) =
      ((Fintype.card ι₀ : R) - (Fintype.card ι₁ : R)) * σ
  superTrace_scale_balanced : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (h : Fintype.card ι₀ = Fintype.card ι₁) (σ : R),
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) (R := R) σ) = 0
  superTrace_chiralMode : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R),
    superTrace (chiralMode (ι₀ := ι₀) (ι₁ := ι₁) B C) = 0
  superTrace_volumeMode : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (A : Matrix ι₀ ι₀ R) (D : Matrix ι₁ ι₁ R)
    (h : Matrix.trace A = Matrix.trace D),
    superTrace (volumeMode (ι₀ := ι₀) (ι₁ := ι₁) A D) = 0
  chiral_mode_mul : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R),
    chiralMode B C * chiralMode B C = Matrix.fromBlocks (B * C) 0 0 (C * B)
  superTrace_chiralSquare : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R),
    superTrace ((chiralMode B C) * (chiralMode B C)) = 0
  total_deformation_superTrace : ∀ {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]
    {R : Type*} [CommRing R] (σ : R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (A : Matrix ι₀ ι₀ R) (D : Matrix ι₁ ι₁ R) (hvol : Matrix.trace A = Matrix.trace D),
    superTrace (scaleMode (ι₀ := ι₀) (ι₁ := ι₁) σ + chiralMode B C + volumeMode A D) =
      ((Fintype.card ι₀ : R) - (Fintype.card ι₁ : R)) * σ
  berezinian_homothety_balance : ∀ {R : Type*} [CommRing R] (a b c d inv_d scale inv_scale : R),
    scale * inv_scale = 1 → d * inv_d = 1 →
    berezinian2 (scale * a) (scale * b) (scale * c) (scale * d) (inv_scale * inv_d) =
      berezinian2 a b c d inv_d
  berezinianMat_smul : ∀ {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (inv_d scale inv_scale : R),
    scale * inv_scale = 1 → M 1 1 * inv_d = 1 →
    berezinianMat (scale • M) (inv_scale * inv_d) = berezinianMat M inv_d
  balanced_homothety_berezinian_eq_one : ∀ {R : Type*} [CommRing R] (p : ℕ) (c inv_c : R),
    c * inv_c = 1 → (c ^ p) * (inv_c ^ p) = 1
  unbalanced_homothety_berezinian_factor : ∀ {R : Type*} [CommRing R] (p q : ℕ) (c inv_c : R),
    (c ^ (p + q)) * (inv_c ^ q) = c ^ p * (c * inv_c) ^ q
  unbalanced_homothety_berezinian : ∀ {R : Type*} [CommRing R] (p q : ℕ) (c inv_c : R),
    c * inv_c = 1 → (c ^ (p + q)) * (inv_c ^ q) = c ^ p

/-- Verification theorem constructing the master certificate. -/
theorem compile_nuclear_quasiphonon_super_grassmannian :
    NuclearQuasiphononSuperGrassmannianCertificate where
  superTrace_add := fun M N => superTrace_add M N
  superTrace_smul := fun c M => superTrace_smul c M
  superTrace_neg := fun M => superTrace_neg M
  superTrace_sub := fun M N => superTrace_sub M N
  susyQ_sq := fun V => susyQ_sq V
  susyQ_dag_sq := fun V => susyQ_dag_sq V
  susyH_eq := fun V => susyH_eq V
  superTrace_susyH := fun V => superTrace_susyH V
  superTrace_scaleMode := fun σ => superTrace_scaleMode σ
  superTrace_scale_balanced := fun h σ => superTrace_scale_balanced h σ
  superTrace_chiralMode := fun B C => superTrace_chiralMode B C
  superTrace_volumeMode := fun A D h => superTrace_volumeMode A D h
  chiral_mode_mul := fun B C => chiral_mode_mul B C
  superTrace_chiralSquare := fun B C => superTrace_chiralSquare B C
  total_deformation_superTrace := fun σ B C A D h => total_deformation_superTrace σ B C A D h
  berezinian_homothety_balance := fun a b c d inv_d scale inv_scale hs hd =>
    berezinian_homothety_balance a b c d inv_d scale inv_scale hs hd
  berezinianMat_smul := fun M inv_d scale inv_scale hs hd =>
    berezinianMat_smul M inv_d scale inv_scale hs hd
  balanced_homothety_berezinian_eq_one := fun p c inv_c h =>
    balanced_homothety_berezinian_eq_one p c inv_c h
  unbalanced_homothety_berezinian_factor := fun p q c inv_c =>
    unbalanced_homothety_berezinian_factor p q c inv_c
  unbalanced_homothety_berezinian := fun p q c inv_c h =>
    unbalanced_homothety_berezinian p q c inv_c h

end InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian
