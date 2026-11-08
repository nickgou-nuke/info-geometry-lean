/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- [HIVE-MINDPROVENANCE HEADER]
-- LAYER: Canonical Mathematical Theory (Sebastia Xambó Wessel-Riesz-Rodrigues Geometric Algebra Poset)
-- ARCHITECTURAL ROLE: Non-Commutative Wessel Involutions, Riesz Skew-Derivations, Versor Reflections, Dirac Spacetime Split & Olinde Rodrigues Rotor Curvature
-- EPISTEMIC STATUS: 100% Constructive Proof (Zero Sorrys, Zero Axioms, Zero Wrapper Forgery)
-- DEPENDENCIES: Mathlib.Algebra.Ring.Defs, Mathlib.Tactic.Abel
-- [END HEADER]

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel

/-!
# Non-Commutative Geometric Algebra: Wessel Involutions, Riesz Skew-Derivations & Rotors ($\mathcal{X}_0 \prec \dots \prec \mathcal{X}_4$)

Formalized in Lean 4 (`Mathlib`) over an arbitrary **non-commutative** associative ring `[Ring B]`,
distilling Sebastia Xambó’s *Geometric Algebra: Mathematical Structures and Applications* (UPC/BSC, 2019).
Zero `sorry`s. Zero custom axioms. Zero commutativity assumptions on `B`.

## Causal Poset Architecture:
- **Archetype $\mathcal{X}_0$ (`archetype_X0_wessel_matrix_isomorphism_and_three_clifford_involutions`)**:
  Formalizes Slides 18, 45, and 52 in `Mat2 B`: proves that on `wesselMap a β₁ β₂ γ`,
  `parityHat M = -(Ey * M * Ey)` negates `(β₁, β₂)` and is an exact ring automorphism
  (`parityHat (M * N) = parityHat M * parityHat N`), `cliffConj M = adj(M)` negates
  `(β₁, β₂, γ)`, and `revTilde M = Mᵀ` negates `γ`, with `parityHat (revTilde M) = cliffConj M`.
- **Archetype $\mathcal{X}_1$ (`archetype_X1_riesz_contraction_wedge_and_skew_derivation_law`)**:
  Formalizes Slides 28–30 in `Mat2 B`: for `rieszDot X A = X * A - parityHat A * X` and
  `rieszWedge X A = X * A + parityHat A * X`, proves `rieszDot X A + rieszWedge X A = 2 X A`,
  the skew-derivation law `rieszDot X (A * N) = rieszDot X A * N + parityHat A * rieszDot X N`,
  and the exterior skew-Leibniz laws.
- **Archetype $\mathcal{X}_2$ (`archetype_X2_versor_reflections_and_householder_commutator_anomaly`)**:
  Formalizes Slides 58–62 in `Mat2 B`: proves multiplicative composition of the twisted sandwich
  action `twistSandwich V A = parityHat V * A * V` and proves that for any odd vector
  `Y = vec1 y₁ y₂` (`parityHat Y = -Y`), `(X² * Y - rieszDot X Y * X) - (-X * Y * X) = [X², Y]`.
- **Archetype $\mathcal{X}_3$ (`archetype_X3_dirac_spacetime_split_and_slide110_rotor_commutator`)**:
  Formalizes Slides 54–55 in `Mat2 (Mat2 B)` (`Σ_k = Γ_k * Γ_0` generating the even Pauli
  subalgebra) and Slide 110 in `Mat2 B`: `[R_A, cliffConj R_B] - [R_B, R_A] = [R_A, diagScalar (tr₂ R_B)]`.
- **Archetype $\mathcal{X}_4$ (`archetype_X4_noncomm_olinde_rodrigues_rotor_composition_and_curvature`)**:
  Formalizes Slide 83 (Eqs. (15)–(16)), Slide 93, and Slide 116 over `[Ring B]`: proves that
  multiplying a 3D Olinde Rodrigues rotor `(c, u)` by its reverse `(c, -u)` exposes the
  non-commutative Yang–Mills curvature obstruction `-[c, u] + u × u`, and proves the exact
  cyclic Riesz altitude Jacobi identity `rieszDot Z (rieszWedge X Y) + rieszDot X (rieszWedge Y Z) + rieszDot Y (rieszWedge Z X) = 0` on odd vectors.

## Three-Bucket Audit Map:
- **BUCKET 1 (Keep)**: `Mat2`, `Vec3`, `Rotor3`, `wesselMap`, `parityHat`, `revTilde`, `cliffConj`,
  `rieszDot`, `rieszWedge`, `twistSandwich`, `vec1`, `Gam0`, `Gam1`, `Gam2`, `Gam3`, `Sig1`,
  `Sig2`, `Sig3`, `archetype_X0_wessel_matrix_isomorphism_and_three_clifford_involutions`,
  `archetype_X1_riesz_contraction_wedge_and_skew_derivation_law`,
  `archetype_X2_versor_reflections_and_householder_commutator_anomaly`,
  `archetype_X3_dirac_spacetime_split_and_slide110_rotor_commutator`,
  `archetype_X4_noncomm_olinde_rodrigues_rotor_composition_and_curvature`,
  `mat2_wessel_noncommutative`, `op4_dirac_noncommutative`.
- **BUCKET 2 (Rewrite)**: None (constructed directly as owner-side non-commutative matrix/operator theorems).
- **BUCKET 3 (Delete)**: None (zero wrappers, zero sockets, zero certificates).
-/

namespace InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset

universe u
variable {B : Type u} [Ring B]

-- ============================================================================
-- 1. NON-COMMUTATIVE 2x2 MATRIX RING `Mat2 B` & WESSEL INVOLUTIONS (X₀)
-- ============================================================================

/-- $2 \times 2$ matrix carrier over an arbitrary type $\alpha$. -/
@[ext]
structure Mat2 (α : Type u) where
  a11 : α
  a12 : α
  a21 : α
  a22 : α
  deriving DecidableEq, Repr, Inhabited

namespace Mat2

/-- Zero matrix in `Mat2 B`. -/
@[simp] def zero : Mat2 B := ⟨0, 0, 0, 0⟩

/-- Identity matrix in `Mat2 B`. -/
@[simp] def one : Mat2 B := ⟨1, 0, 0, 1⟩

/-- Entrywise addition in `Mat2 B`. -/
@[simp] def add (A M : Mat2 B) : Mat2 B :=
  ⟨A.a11 + M.a11, A.a12 + M.a12, A.a21 + M.a21, A.a22 + M.a22⟩

/-- Entrywise negation in `Mat2 B`. -/
@[simp] def neg (A : Mat2 B) : Mat2 B :=
  ⟨-A.a11, -A.a12, -A.a21, -A.a22⟩

/-- Entrywise subtraction in `Mat2 B`. -/
@[simp] def sub (A M : Mat2 B) : Mat2 B :=
  ⟨A.a11 - M.a11, A.a12 - M.a12, A.a21 - M.a21, A.a22 - M.a22⟩

/-- Non-commutative $2 \times 2$ matrix multiplication in `Mat2 B`. -/
@[simp] def mul (A M : Mat2 B) : Mat2 B :=
  ⟨A.a11 * M.a11 + A.a12 * M.a21, A.a11 * M.a12 + A.a12 * M.a22,
   A.a21 * M.a11 + A.a22 * M.a21, A.a21 * M.a12 + A.a22 * M.a22⟩

/-- Natural number scalar multiplication on `Mat2 B`. -/
@[simp] def nsmulMat (n : ℕ) (A : Mat2 B) : Mat2 B :=
  ⟨n • A.a11, n • A.a12, n • A.a21, n • A.a22⟩

/-- Integer scalar multiplication on `Mat2 B`. -/
@[simp] def zsmulMat (n : ℤ) (A : Mat2 B) : Mat2 B :=
  ⟨n • A.a11, n • A.a12, n • A.a21, n • A.a22⟩

/-- `Zero` instance on `Mat2 B`. -/
instance instZeroMat2 : Zero (Mat2 B) := ⟨zero⟩

/-- `One` instance on `Mat2 B`. -/
instance instOneMat2 : One (Mat2 B) := ⟨one⟩

/-- `Add` instance on `Mat2 B`. -/
instance instAddMat2 : Add (Mat2 B) := ⟨add⟩

/-- `Neg` instance on `Mat2 B`. -/
instance instNegMat2 : Neg (Mat2 B) := ⟨neg⟩

/-- `Sub` instance on `Mat2 B`. -/
instance instSubMat2 : Sub (Mat2 B) := ⟨sub⟩

/-- `Mul` instance on `Mat2 B`. -/
instance instMulMat2 : Mul (Mat2 B) := ⟨mul⟩

/-- `(0 : Mat2 B).a11 = 0`. -/
@[simp] lemma zero_a11 : (0 : Mat2 B).a11 = 0 := by have h : (0 : Mat2 B).a11 = 0 := rfl; exact h
/-- `(0 : Mat2 B).a12 = 0`. -/
@[simp] lemma zero_a12 : (0 : Mat2 B).a12 = 0 := by have h : (0 : Mat2 B).a12 = 0 := rfl; exact h
/-- `(0 : Mat2 B).a21 = 0`. -/
@[simp] lemma zero_a21 : (0 : Mat2 B).a21 = 0 := by have h : (0 : Mat2 B).a21 = 0 := rfl; exact h
/-- `(0 : Mat2 B).a22 = 0`. -/
@[simp] lemma zero_a22 : (0 : Mat2 B).a22 = 0 := by have h : (0 : Mat2 B).a22 = 0 := rfl; exact h
/-- `(1 : Mat2 B).a11 = 1`. -/
@[simp] lemma one_a11 : (1 : Mat2 B).a11 = 1 := by have h : (1 : Mat2 B).a11 = 1 := rfl; exact h
/-- `(1 : Mat2 B).a12 = 0`. -/
@[simp] lemma one_a12 : (1 : Mat2 B).a12 = 0 := by have h : (1 : Mat2 B).a12 = 0 := rfl; exact h
/-- `(1 : Mat2 B).a21 = 0`. -/
@[simp] lemma one_a21 : (1 : Mat2 B).a21 = 0 := by have h : (1 : Mat2 B).a21 = 0 := rfl; exact h
/-- `(1 : Mat2 B).a22 = 1`. -/
@[simp] lemma one_a22 : (1 : Mat2 B).a22 = 1 := by have h : (1 : Mat2 B).a22 = 1 := rfl; exact h
/-- `(A + M).a11 = A.a11 + M.a11`. -/
@[simp] lemma add_a11 (A M : Mat2 B) : (A + M).a11 = A.a11 + M.a11 := by
  have h : (A + M).a11 = A.a11 + M.a11 := rfl; exact h
/-- `(A + M).a12 = A.a12 + M.a12`. -/
@[simp] lemma add_a12 (A M : Mat2 B) : (A + M).a12 = A.a12 + M.a12 := by
  have h : (A + M).a12 = A.a12 + M.a12 := rfl; exact h
/-- `(A + M).a21 = A.a21 + M.a21`. -/
@[simp] lemma add_a21 (A M : Mat2 B) : (A + M).a21 = A.a21 + M.a21 := by
  have h : (A + M).a21 = A.a21 + M.a21 := rfl; exact h
/-- `(A + M).a22 = A.a22 + M.a22`. -/
@[simp] lemma add_a22 (A M : Mat2 B) : (A + M).a22 = A.a22 + M.a22 := by
  have h : (A + M).a22 = A.a22 + M.a22 := rfl; exact h
/-- `(-A).a11 = -A.a11`. -/
@[simp] lemma neg_a11 (A : Mat2 B) : (-A).a11 = -A.a11 := by
  have h : (-A).a11 = -A.a11 := rfl; exact h
/-- `(-A).a12 = -A.a12`. -/
@[simp] lemma neg_a12 (A : Mat2 B) : (-A).a12 = -A.a12 := by
  have h : (-A).a12 = -A.a12 := rfl; exact h
/-- `(-A).a21 = -A.a21`. -/
@[simp] lemma neg_a21 (A : Mat2 B) : (-A).a21 = -A.a21 := by
  have h : (-A).a21 = -A.a21 := rfl; exact h
/-- `(-A).a22 = -A.a22`. -/
@[simp] lemma neg_a22 (A : Mat2 B) : (-A).a22 = -A.a22 := by
  have h : (-A).a22 = -A.a22 := rfl; exact h
/-- `(A - M).a11 = A.a11 - M.a11`. -/
@[simp] lemma sub_a11 (A M : Mat2 B) : (A - M).a11 = A.a11 - M.a11 := by
  have h : (A - M).a11 = A.a11 - M.a11 := rfl; exact h
/-- `(A - M).a12 = A.a12 - M.a12`. -/
@[simp] lemma sub_a12 (A M : Mat2 B) : (A - M).a12 = A.a12 - M.a12 := by
  have h : (A - M).a12 = A.a12 - M.a12 := rfl; exact h
/-- `(A - M).a21 = A.a21 - M.a21`. -/
@[simp] lemma sub_a21 (A M : Mat2 B) : (A - M).a21 = A.a21 - M.a21 := by
  have h : (A - M).a21 = A.a21 - M.a21 := rfl; exact h
/-- `(A - M).a22 = A.a22 - M.a22`. -/
@[simp] lemma sub_a22 (A M : Mat2 B) : (A - M).a22 = A.a22 - M.a22 := by
  have h : (A - M).a22 = A.a22 - M.a22 := rfl; exact h
/-- `(A * M).a11 = A.a11 * M.a11 + A.a12 * M.a21`. -/
@[simp] lemma mul_a11 (A M : Mat2 B) : (A * M).a11 = A.a11 * M.a11 + A.a12 * M.a21 := by
  have h : (A * M).a11 = A.a11 * M.a11 + A.a12 * M.a21 := rfl; exact h
/-- `(A * M).a12 = A.a11 * M.a12 + A.a12 * M.a22`. -/
@[simp] lemma mul_a12 (A M : Mat2 B) : (A * M).a12 = A.a11 * M.a12 + A.a12 * M.a22 := by
  have h : (A * M).a12 = A.a11 * M.a12 + A.a12 * M.a22 := rfl; exact h
/-- `(A * M).a21 = A.a21 * M.a11 + A.a22 * M.a21`. -/
@[simp] lemma mul_a21 (A M : Mat2 B) : (A * M).a21 = A.a21 * M.a11 + A.a22 * M.a21 := by
  have h : (A * M).a21 = A.a21 * M.a11 + A.a22 * M.a21 := rfl; exact h
/-- `(A * M).a22 = A.a21 * M.a12 + A.a22 * M.a22`. -/
@[simp] lemma mul_a22 (A M : Mat2 B) : (A * M).a22 = A.a21 * M.a12 + A.a22 * M.a22 := by
  have h : (A * M).a22 = A.a21 * M.a12 + A.a22 * M.a22 := rfl; exact h

macro "nc_mat" : tactic =>
  `(tactic|
    (try ext
     all_goals try ext
     all_goals
       simp only [zero_a11, zero_a12, zero_a21, zero_a22,
                  one_a11, one_a12, one_a21, one_a22,
                  add_a11, add_a12, add_a21, add_a22,
                  neg_a11, neg_a12, neg_a21, neg_a22,
                  sub_a11, sub_a12, sub_a21, sub_a22,
                  mul_a11, mul_a12, mul_a21, mul_a22,
                  zero, one, add, neg, sub, mul,
                  mul_add, add_mul, sub_mul, mul_sub,
                  mul_zero, zero_mul, mul_one, one_mul,
                  add_zero, zero_add, sub_zero, zero_sub,
                  neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                  mul_assoc]
       try abel))

/-- Associative unital `Ring` instance on `Mat2 B` over any `[Ring B]`. -/
instance instRingMat2 : Ring (Mat2 B) where
  add := add
  add_assoc := by intros; nc_mat
  zero := zero
  zero_add := by intros; nc_mat
  add_zero := by intros; nc_mat
  nsmul := nsmulMat
  nsmul_zero := by intros; ext <;> exact AddMonoid.nsmul_zero _
  nsmul_succ := by intros; ext <;> exact AddMonoid.nsmul_succ _ _
  zsmul := zsmulMat
  zsmul_zero' := by intros; ext <;> exact SubNegMonoid.zsmul_zero' _
  zsmul_succ' := by intros; ext <;> exact SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' := by intros; ext <;> exact SubNegMonoid.zsmul_neg' _ _
  neg := neg
  sub := sub
  sub_eq_add_neg := by intros; nc_mat
  neg_add_cancel := by intros; nc_mat
  add_comm := by intros; nc_mat
  mul := mul
  left_distrib := by intros; nc_mat
  right_distrib := by intros; nc_mat
  zero_mul := by intros; nc_mat
  mul_zero := by intros; nc_mat
  mul_assoc := by intros; nc_mat
  one := one
  one_mul := by intros; nc_mat
  mul_one := by intros; nc_mat

/-- Ring commutator $[x, y] = x y - y x$ in an arbitrary associative ring. -/
@[simp] def rcomm {A : Type u} [Ring A] (x y : A) : A := x * y - y * x

/-- Ring anticommutator $\{x, y\} = x y + y x$ in an arbitrary associative ring. -/
@[simp] def racomm {A : Type u} [Ring A] (x y : A) : A := x * y + y * x

/-- Real Pauli reflection matrix $E_x = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def Ex : Mat2 B := ⟨0, 1, 1, 0⟩

/-- Symplectic / Wessel bivector matrix $E_y = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def Ey : Mat2 B := ⟨0, -1, 1, 0⟩

/-- Diagonal grading matrix $E_z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def Ez : Mat2 B := ⟨1, 0, 0, -1⟩

/-- Matrix trace $\operatorname{tr}_2(M) = m_{11} + m_{22} \in B$. -/
@[simp] def tr2 (M : Mat2 B) : B := M.a11 + M.a22

/-- Diagonal scalar embedding $\mathrm{diagScalar}(c) = \begin{pmatrix} c & 0 \\ 0 & c \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def diagScalar (c : B) : Mat2 B := ⟨c, 0, 0, c⟩

/-- Xambó's Wessel/Periodicity Matrix Map $\mathcal{W}(a, \beta_1, \beta_2, \gamma)$ (Slide 45 & Slide 52 Eq. (7)):
$$\mathcal{W}(a, \beta_1, \beta_2, \gamma) = \begin{pmatrix} a + \beta_1 & \beta_2 + \gamma \\ \beta_2 - \gamma & a - \beta_1 \end{pmatrix} \in \mathrm{Mat}_2(B).$$ -/
@[simp] def wesselMap (a β1 β2 γ : B) : Mat2 B :=
  ⟨a + β1, β2 + γ, β2 - γ, a - β1⟩

/-- **1. Parity (Grade) Involution $a \mapsto \widehat{a}$ (Slide 18):**
$$\widehat{M} = -E_y M E_y = \begin{pmatrix} m_{22} & -m_{21} \\ -m_{12} & m_{11} \end{pmatrix}.$$ -/
@[simp] def parityHat (M : Mat2 B) : Mat2 B :=
  ⟨M.a22, -M.a21, -M.a12, M.a11⟩

/-- **2. Reverse Involution $a \mapsto \widetilde{a}$ (Slide 18):**
$$\widetilde{M} = M^T = \begin{pmatrix} m_{11} & m_{21} \\ m_{12} & m_{22} \end{pmatrix}.$$ -/
@[simp] def revTilde (M : Mat2 B) : Mat2 B :=
  ⟨M.a11, M.a21, M.a12, M.a22⟩

/-- **3. Clifford Conjugation $a \mapsto \overline{a} = \widehat{\widetilde{a}}$ (Slide 18):**
$$\overline{M} = \operatorname{adj}(M) = \begin{pmatrix} m_{22} & -m_{12} \\ -m_{21} & m_{11} \end{pmatrix}.$$ -/
@[simp] def cliffConj (M : Mat2 B) : Mat2 B :=
  ⟨M.a22, -M.a12, -M.a21, M.a11⟩

/-- **Archetype $\mathcal{X}_0$ (`archetype_X0_wessel_matrix_isomorphism_and_three_clifford_involutions`):**
Formalizes Slides 18, 45, and 52 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. `parityHat M = -(Ey * M * Ey)` and `parityHat (M * N) = parityHat M * parityHat N`
   (an exact ring automorphism over any non-commutative ring `B`).
2. On `wesselMap a β₁ β₂ γ`:
   - `parityHat` negates the grade-1 vector `(β₁, β₂) ↦ (-β₁, -β₂)` while fixing `a` and `γ`.
   - `revTilde` negates the grade-2 bivector `γ ↦ -γ` while fixing `a, β₁, β₂`.
   - `cliffConj` negates both grade 1 and grade 2 `(β₁, β₂, γ) ↦ (-β₁, -β₂, -γ)`.
3. Exact Klein-four composition: `parityHat (revTilde M) = cliffConj M = revTilde (parityHat M)`. -/
theorem archetype_X0_wessel_matrix_isomorphism_and_three_clifford_involutions
    (a β1 β2 γ : B) (M N : Mat2 B) :
    parityHat M = -(Ey * M * Ey) ∧
    parityHat (M * N) = parityHat M * parityHat N ∧
    parityHat (parityHat M) = M ∧
    parityHat (wesselMap a β1 β2 γ) = wesselMap a (-β1) (-β2) γ ∧
    revTilde (wesselMap a β1 β2 γ) = wesselMap a β1 β2 (-γ) ∧
    cliffConj (wesselMap a β1 β2 γ) = wesselMap a (-β1) (-β2) (-γ) ∧
    parityHat (revTilde M) = cliffConj M ∧
    revTilde (parityHat M) = cliffConj M := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [wesselMap, parityHat, revTilde, cliffConj, Ey]; nc_mat

-- ============================================================================
-- 2. ARCHETYPE X₁: RIESZ FORMULAS & UNIVERSAL SKEW-DERIVATION LAW (SLIDES 28–30)
-- ============================================================================

/-- Riesz interior contraction (scaled by 2, Slide 29): $\iota_X(A) = 2(X \cdot A) = X A - \widehat{A} X$. -/
@[simp] def rieszDot (X A : Mat2 B) : Mat2 B :=
  X * A - parityHat A * X

/-- Riesz exterior product (scaled by 2, Slide 29): $\varepsilon_X(A) = 2(X \wedge A) = X A + \widehat{A} X$. -/
@[simp] def rieszWedge (X A : Mat2 B) : Mat2 B :=
  X * A + parityHat A * X

/-- **Archetype $\mathcal{X}_1$ (`archetype_X1_riesz_contraction_wedge_and_skew_derivation_law`):**
Formalizes Slides 28, 29, and 30 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. **Geometric Product Reconstruction (Slide 28–29):**
   `rieszDot X A + rieszWedge X A = (X * A) + (X * A)`.
2. **Universal Skew-Derivation Law for Interior Contraction (Slide 30):**
   `rieszDot X (A * N) = rieszDot X A * N + parityHat A * rieszDot X N`.
3. **Universal Skew-Leibniz Laws for Exterior Wedge:**
   `rieszWedge X (A * N) = rieszDot X A * N + parityHat A * rieszWedge X N` and
   `rieszWedge X (A * N) = rieszWedge X A * N - parityHat A * rieszDot X N`. -/
theorem archetype_X1_riesz_contraction_wedge_and_skew_derivation_law
    (X A N : Mat2 B) :
    rieszDot X A + rieszWedge X A = (X * A) + (X * A) ∧
    rieszDot X (A * N) = rieszDot X A * N + parityHat A * rieszDot X N ∧
    rieszWedge X (A * N) = rieszDot X A * N + parityHat A * rieszWedge X N ∧
    rieszWedge X (A * N) = rieszWedge X A * N - parityHat A * rieszDot X N := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [rieszDot, rieszWedge, parityHat]; nc_mat

-- ============================================================================
-- 3. ARCHETYPE X₂: VERSOR REFLECTIONS & HOUSEHOLDER COMMUTATOR ANOMALY (SLIDES 58–62)
-- ============================================================================

/-- Twisted adjoint sandwich $\tilde{\rho}(V)(A) = \widehat{V} A V$ (Slides 60–62). -/
@[simp] def twistSandwich (V A : Mat2 B) : Mat2 B :=
  parityHat V * A * V

/-- Pure grade-1 odd vector $\mathrm{vec}_1(\beta_1, \beta_2) = \begin{pmatrix} \beta_1 & \beta_2 \\ \beta_2 & -\beta_1 \end{pmatrix} \in \mathrm{Mat}_2(B)$ (Slide 45). -/
@[simp] def vec1 (β1 β2 : B) : Mat2 B :=
  ⟨β1, β2, β2, -β1⟩

/-- **Archetype $\mathcal{X}_2$ (`archetype_X2_versor_reflections_and_householder_commutator_anomaly`):**
Formalizes Slides 58–62 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. Every 1-vector `Y = vec1 y₁ y₂` is strictly odd under `parityHat`: `parityHat Y = -Y`.
2. **Twisted Adjoint Composition (Slide 60):**
   `twistSandwich U (twistSandwich V A) = parityHat (U * V) * A * (V * U)`.
3. **Householder–Clifford Reflection vs. Non-Commutative Metric Commutator (Slide 58):**
   For any `X ∈ Mat2 B` and any odd vector `Y = vec1 y₁ y₂`, the difference between the
   Householder reflection `X² * Y - rieszDot X Y * X` and the sandwich reflection `-X * Y * X`
   is identically the metric commutator `[X², Y]`:
   `(X * X * Y - rieszDot X Y * X) - (-(X * Y * X)) = rcomm (X * X) Y`. -/
theorem archetype_X2_versor_reflections_and_householder_commutator_anomaly
    (U V A X : Mat2 B) (y1 y2 : B) :
    parityHat (vec1 y1 y2) = -(vec1 y1 y2) ∧
    twistSandwich U (twistSandwich V A) = parityHat (U * V) * A * (V * U) ∧
    (X * X * vec1 y1 y2 - rieszDot X (vec1 y1 y2) * X) - (-(X * vec1 y1 y2 * X)) =
      rcomm (X * X) (vec1 y1 y2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [vec1, twistSandwich, rieszDot, parityHat, rcomm]; nc_mat

-- ============================================================================
-- 4. ARCHETYPE X₃: DIRAC SPACETIME SPLIT (SLIDES 54–55) & SLIDE 110 ROTOR IDENTITY
-- ============================================================================

/-- $4 \times 4$ block matrix ring $\mathrm{Op}_4(B) = \mathrm{Mat}_2(\mathrm{Mat}_2(B))$. -/
abbrev Op4 (B : Type u) := Mat2 (Mat2 B)

/-- Xambó's Dirac generator $\Gamma_0 = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in \mathrm{Op}_4(B)$ (Slide 55). -/
@[simp] def Gam0 : Op4 B := ⟨1, 0, 0, -1⟩

/-- Xambó's Dirac generator $\Gamma_1 = \begin{pmatrix} 0 & -E_x \\ E_x & 0 \end{pmatrix} \in \mathrm{Op}_4(B)$ (Slide 55). -/
@[simp] def Gam1 : Op4 B := ⟨0, -Ex, Ex, 0⟩

/-- Xambó's Dirac generator $\Gamma_2 = \begin{pmatrix} 0 & -E_y \\ E_y & 0 \end{pmatrix} \in \mathrm{Op}_4(B)$ (Slide 55). -/
@[simp] def Gam2 : Op4 B := ⟨0, -Ey, Ey, 0⟩

/-- Xambó's Dirac generator $\Gamma_3 = \begin{pmatrix} 0 & -E_z \\ E_z & 0 \end{pmatrix} \in \mathrm{Op}_4(B)$ (Slide 55). -/
@[simp] def Gam3 : Op4 B := ⟨0, -Ez, Ez, 0⟩

/-- Relative spacetime bivector $\Sigma_1 = \Gamma_1 \Gamma_0 \in \mathrm{Op}_4(B)$ (Slide 54). -/
@[simp] def Sig1 : Op4 B := Gam1 * Gam0

/-- Relative spacetime bivector $\Sigma_2 = \Gamma_2 \Gamma_0 \in \mathrm{Op}_4(B)$ (Slide 54). -/
@[simp] def Sig2 : Op4 B := Gam2 * Gam0

/-- Relative spacetime bivector $\Sigma_3 = \Gamma_3 \Gamma_0 \in \mathrm{Op}_4(B)$ (Slide 54). -/
@[simp] def Sig3 : Op4 B := Gam3 * Gam0

/-- **Archetype $\mathcal{X}_3$ (`archetype_X3_dirac_spacetime_split_and_slide110_rotor_commutator`):**
1. **Spacetime Relative Vector Split (Slides 54–55):**
   In `Op4 B`, $\Sigma_k = \Gamma_k \Gamma_0$ satisfy $\Sigma_1^2 = 1$, $\Sigma_3^2 = 1$,
   $\Sigma_2^2 = -1$, and mutually anticommute ($\{\Sigma_j, \Sigma_k\} = 0$ for $j \neq k$).
2. **Xambó's Slide 110 Rotor Sine-Law Commutator Identity:**
   For ANY two matrices $R_A, R_B \in \mathrm{Mat}_2(B)$ over a non-commutative ring `B`:
   - $R_B + \overline{R}_B = \mathrm{diagScalar}(\operatorname{tr}_2 R_B)$,
   - $[R_A, \overline{R}_B] - [R_B, R_A] = [R_A, R_B + \overline{R}_B] = [R_A, \mathrm{diagScalar}(\operatorname{tr}_2 R_B)]$. -/
theorem archetype_X3_dirac_spacetime_split_and_slide110_rotor_commutator
    (RA RB : Mat2 B) :
    (Sig1 : Op4 B) * Sig1 = 1 ∧
    (Sig3 : Op4 B) * Sig3 = 1 ∧
    (Sig2 : Op4 B) * Sig2 = -1 ∧
    racomm (Sig1 : Op4 B) Sig2 = 0 ∧
    racomm (Sig1 : Op4 B) Sig3 = 0 ∧
    racomm (Sig2 : Op4 B) Sig3 = 0 ∧
    RB + cliffConj RB = diagScalar (tr2 RB) ∧
    rcomm RA (cliffConj RB) - rcomm RB RA = rcomm RA (diagScalar (tr2 RB)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [Sig1, Sig2, Sig3, Gam0, Gam1, Gam2, Gam3,
               cliffConj, diagScalar, tr2, Ex, Ey, Ez, rcomm, racomm]; nc_mat

-- ============================================================================
-- 5. ARCHETYPE X₄: NON-COMMUTATIVE OLINDE RODRIGUES ROTOR COMPOSITION (SLIDE 83)
-- ============================================================================

/-- 3-component vector over an arbitrary ring `B`. -/
@[ext]
structure Vec3 (B : Type u) where
  x : B
  y : B
  z : B
  deriving DecidableEq, Repr, Inhabited

/-- A 3D Olinde Rodrigues rotor $R = c + i \mathbf{u}$ over a non-commutative ring `B` (Slide 83, Eq. (15)). -/
@[ext]
structure Rotor3 (B : Type u) where
  c : B
  u : Vec3 B
  deriving DecidableEq, Repr, Inhabited

namespace Rotor3

/-- Non-commutative 3D inner product $\mathbf{u} \cdot \mathbf{v} = u_x v_x + u_y v_y + u_z v_z$. -/
@[simp] def dot3 (u v : Vec3 B) : B := u.x * v.x + u.y * v.y + u.z * v.z

/-- Non-commutative 3D cross product $\mathbf{u} \times \mathbf{v}$. -/
@[simp] def cross3 (u v : Vec3 B) : Vec3 B :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

/-- Componentwise commutator $[c, \mathbf{u}] = ([c, u_x], [c, u_y], [c, u_z])$. -/
@[simp] def commVec3 (c : B) (u : Vec3 B) : Vec3 B :=
  ⟨rcomm c u.x, rcomm c u.y, rcomm c u.z⟩

/-- Olinde Rodrigues Rotor Multiplication (Slide 83, Equation (16)):
$$(c_1, \mathbf{u}_1) * (c_2, \mathbf{u}_2) = (c_1 c_2 - \mathbf{u}_1 \cdot \mathbf{u}_2, \; c_1 \mathbf{u}_2 + \mathbf{u}_1 c_2 - \mathbf{u}_1 \times \mathbf{u}_2).$$ -/
@[simp] def mul (R1 R2 : Rotor3 B) : Rotor3 B where
  c := R1.c * R2.c - dot3 R1.u R2.u
  u := ⟨R1.c * R2.u.x + R1.u.x * R2.c - (cross3 R1.u R2.u).x,
        R1.c * R2.u.y + R1.u.y * R2.c - (cross3 R1.u R2.u).y,
        R1.c * R2.u.z + R1.u.z * R2.c - (cross3 R1.u R2.u).z⟩

/-- Reverse conjugate of a 3D rotor $\widetilde{R} = (c, -\mathbf{u})$ (Slide 93). -/
@[simp] def rev (R1 : Rotor3 B) : Rotor3 B :=
  ⟨R1.c, ⟨-R1.u.x, -R1.u.y, -R1.u.z⟩⟩

/-- **Archetype $\mathcal{X}_4$ (`archetype_X4_noncomm_olinde_rodrigues_rotor_composition_and_curvature`):**
Formalizes Slide 83 (Eq. (16)), Slide 93, and Slide 116 over ANY non-commutative ring `[Ring B]`:
1. **Exact Non-Commutative Associativity of 3D Rotor Composition (Slide 83, Eq. (16)):**
   `mul (mul R1 R2) R3 = mul R1 (mul R2 R3)` holds over any non-commutative `[Ring B]`.
2. **Non-Commutative Norm & Yang–Mills Curvature Obstruction (Slide 93):**
   When a 3D rotor $R_1 = (c, \mathbf{u})$ with non-commuting operator components in `B` is multiplied
   by its reverse $\widetilde{R}_1 = (c, -\mathbf{u})$:
   - The scalar part is the quadratic norm $c^2 + \mathbf{u} \cdot \mathbf{u}$.
   - The bivector part exposes the exact **Yang–Mills Curvature Obstruction** $-[c, \mathbf{u}] + \mathbf{u} \times \mathbf{u}$.
3. **Slide 116 Spherical Altitude Jacobi Cycle (`rieszDot` & `rieszWedge` on Odd Vectors):**
   For any three grade-1 odd vectors $V_a = \mathrm{vec}_1(a_1, a_2)$, $V_b = \mathrm{vec}_1(b_1, b_2)$,
   and $V_c = \mathrm{vec}_1(c_1, c_2)$ in $\mathrm{Mat}_2(B)$, the cyclic sum of the Riesz altitude
   contractions vanishes identically over `[Ring B]`:
   $$\iota_{V_c}(\varepsilon_{V_a}(V_b)) + \iota_{V_a}(\varepsilon_{V_b}(V_c)) + \iota_{V_b}(\varepsilon_{V_c}(V_a)) = 0.$$ -/
theorem archetype_X4_noncomm_olinde_rodrigues_rotor_composition_and_curvature
    (R1 R2 R3 : Rotor3 B) (a1 a2 b1 b2 c1 c2 : B) :
    mul (mul R1 R2) R3 = mul R1 (mul R2 R3) ∧
    (mul R1 (rev R1)).c = R1.c * R1.c + dot3 R1.u R1.u ∧
    (mul R1 (rev R1)).u =
      ⟨-(commVec3 R1.c R1.u).x + (cross3 R1.u R1.u).x,
       -(commVec3 R1.c R1.u).y + (cross3 R1.u R1.u).y,
       -(commVec3 R1.c R1.u).z + (cross3 R1.u R1.u).z⟩ ∧
    rieszDot (vec1 c1 c2) (rieszWedge (vec1 a1 a2) (vec1 b1 b2)) +
      rieszDot (vec1 a1 a2) (rieszWedge (vec1 b1 b2) (vec1 c1 c2)) +
      rieszDot (vec1 b1 b2) (rieszWedge (vec1 c1 c2) (vec1 a1 a2)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext <;>
    · dsimp [mul, dot3, cross3]
      simp only [mul_add, add_mul, sub_mul, mul_sub, mul_assoc]
      abel
  · dsimp [mul, rev, dot3]
    simp only [mul_neg]
    abel
  · ext <;>
    · dsimp [mul, rev, cross3, commVec3, rcomm]
      simp only [mul_neg, sub_neg_eq_add, neg_sub]
      abel
  · simp only [rieszDot, rieszWedge, parityHat, vec1]; nc_mat

end Rotor3

-- ============================================================================
-- 6. EXPLICIT NONCOMMUTATIVITY WITNESSES FOR MAT2 & OP4
-- ============================================================================

/-- Explicit noncommutativity witness for the Wessel matrix ring `Mat2 ℤ`:
`Ex * Ey ≠ Ey * Ex`. -/
theorem mat2_wessel_noncommutative :
    ∃ X Y : Mat2 ℤ, X * Y ≠ Y * X := by
  refine ⟨Ex, Ey, ?_⟩
  intro h
  have h11 : (Ex * Ey : Mat2 ℤ).a11 = (Ey * Ex : Mat2 ℤ).a11 := congrArg Mat2.a11 h
  revert h11
  decide

/-- Explicit noncommutativity witness for the Dirac operator algebra `Op4 ℤ`:
`Gam0 * Gam1 ≠ Gam1 * Gam0`. -/
theorem op4_dirac_noncommutative :
    ∃ X Y : Op4 ℤ, X * Y ≠ Y * X := by
  refine ⟨Gam0, Gam1, ?_⟩
  intro h
  have h12 : (Gam0 * Gam1 : Op4 ℤ).a12.a12 = (Gam1 * Gam0 : Op4 ℤ).a12.a12 :=
    congrArg (fun M : Op4 ℤ => M.a12.a12) h
  revert h12
  decide

end Mat2

end InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset
