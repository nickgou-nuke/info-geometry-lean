/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- [HIVE-MINDPROVENANCE HEADER]
-- LAYER: Canonical Mathematical Theory (Yakir Aharonov Two-State Weak-Value & Modular Shift Poset)
-- ARCHITECTURAL ROLE: Non-Commutative Two-Idempotent Sandwiches, Weak-Value Amplification, Weyl Shift Phase Sensitivity & Aharonov-Bohm Holonomy
-- EPISTEMIC STATUS: 100% Constructive Proof (Zero Sorrys, Zero Axioms, Zero Wrapper Forgery)
-- DEPENDENCIES: Mathlib.Algebra.Ring.Defs, Mathlib.Tactic.Abel
-- [END HEADER]

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel

/-!
# Two-State Sandwich Algebras, Weak-Value Amplification & Non-Local Weyl Shift Commutators ($\mathcal{A}_0 \prec \dots \prec \mathcal{A}_4$)

Formalized in Lean 4 (`Mathlib`) over an arbitrary **non-commutative** associative ring `[Ring B]`,
distilling Yakir Aharonov’s lecture on the Two-State Vector Formalism (TSVF), weak-value
amplification, modular momentum, and Aharonov–Bohm holonomy.
Zero `sorry`s. Zero custom axioms. Zero commutativity assumptions on `B`.

## Causal Poset Architecture:
- **Archetype $\mathcal{A}_0$ (`archetype_A0_two_state_transition_sandwich_and_overlap`)**:
  For any two non-commuting idempotents `P₁² = P₁` and `P₂² = P₂` in `B`, proves boundary
  absorption `P₂ * W₂₁(A) = W₂₁(A) * P₁ = W₂₁(A)` and `(P₂ * P₁)² = P₂ * (P₁ * P₂ * P₁)`.
- **Archetype $\mathcal{A}_1$ (`archetype_A1_spin_half_weak_value_amplification_identity` & `archetype_A1_mat2_pauli_weak_value_amplification`)**:
  For any anticommuting involutions `σx² = 1, σy² = 1, {σx, σy} = 0` in `B` (and unconditionally
  for `Ex, Ez ∈ Mat2 B`), proves that while `(σx + σy)² = 2 • 1`, sandwiching `σx + σy` between
  `Py = 1 + σy` and `Px = 1 + σx` yields `Py * (σx + σy) * Px = 2 • (Py * Px)` (weak-value
  amplification) and `Py * (σx - σy) * Px = 0` (orthogonal extinction).
- **Archetype $\mathcal{A}_2$ (`archetype_A2_local_moment_blindness_vs_modular_shift_sensitivity`)**:
  In `Mat2 B`, proves that `tr₂(ρ * D_loc)` and `tr₂(ρ * D_loc²)` are completely blind to the
  off-diagonal interference entries `(u_+, u_-)` of `ρ = [[d₁, u_+], [u_-, d₂]]`, whereas the
  Weyl shift operator `T_L = [[0, τ_+], [τ_-, 0]]` extracts `tr₂(ρ * T_L) = u_+ τ_- + u_- τ_+`.
- **Archetype $\mathcal{A}_3$ (`archetype_A3_nonlocal_heisenberg_commutator_for_modular_shift`)**:
  In `Mat2 B`, proves the exact finite-difference Heisenberg commutator formulas:
  `[E₀₁, V_pot(V₁, V₂)] = [[0, V₂ - V₁], [0, 0]] = diagScalar (V₂ - V₁) * E₀₁` and
  `[Ex, V_pot(V₁, V₂)] = -diagScalar (V₂ - V₁) * Ey`.
- **Archetype $\mathcal{A}_4$ (`archetype_A4_aharonov_bohm_gauge_covariant_modular_velocity`)**:
  In `Mat2 B`, proves that under local gauge conjugation by `G = diag(g₁, g₂)`, the Wilson-dressed
  modular shift `T_AB(W₁₂, W₂₁) = [[0, W₁₂], [W₂₁, 0]]` transforms covariantly as
  `T_AB(g₁ W₁₂ g₂⁻¹, g₂ W₂₁ g₁⁻¹)` and squares to the closed holonomy loop `diag(W₁₂ W₂₁, W₂₁ W₁₂)`.

## Three-Bucket Audit Map:
- **BUCKET 1 (Keep)**: `twoStateSandwich`, `archetype_A0_two_state_transition_sandwich_and_overlap`,
  `archetype_A1_spin_half_weak_value_amplification_identity`, `Mat2`, `twoPacketState`,
  `localObs`, `modularShift`, `gaugeDiag`, `archetype_A1_mat2_pauli_weak_value_amplification`,
  `archetype_A2_local_moment_blindness_vs_modular_shift_sensitivity`,
  `archetype_A3_nonlocal_heisenberg_commutator_for_modular_shift`,
  `archetype_A4_aharonov_bohm_gauge_covariant_modular_velocity`,
  `mat2_aharonov_noncommutative`.
- **BUCKET 2 (Rewrite)**: None (constructed directly as owner-side non-commutative ring/matrix theorems).
- **BUCKET 3 (Delete)**: None (zero wrappers, zero sockets, zero certificates).
-/

namespace InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset

universe u
variable {B : Type u} [Ring B]

/-- Ring commutator $[x, y] = x y - y x$ in an arbitrary associative ring. -/
@[simp] def rcomm {A : Type u} [Ring A] (x y : A) : A := x * y - y * x

/-- Ring anticommutator $\{x, y\} = x y + y x$ in an arbitrary associative ring. -/
@[simp] def racomm {A : Type u} [Ring A] (x y : A) : A := x * y + y * x

-- ============================================================================
-- 1. ARCHETYPES A₀ & A₁: TWO-IDEMPOTENT SANDWICHES & WEAK-VALUE AMPLIFICATION
-- ============================================================================

/-- Bilateral two-state transition sandwich $W_{21}(P_2, P_1, A) = P_2 A P_1$. -/
@[simp] def twoStateSandwich (P2 P1 A : B) : B := P2 * A * P1

/-- **Archetype $\mathcal{A}_0$ (`archetype_A0_two_state_transition_sandwich_and_overlap`):**
For ANY two (generally non-commuting) idempotents $P_1^2 = P_1$ and $P_2^2 = P_2$ in `[Ring B]`:
1. Left post-selection absorption: `P₂ * twoStateSandwich P₂ P₁ A = twoStateSandwich P₂ P₁ A`.
2. Right pre-selection absorption: `twoStateSandwich P₂ P₁ A * P₁ = twoStateSandwich P₂ P₁ A`.
3. Overlap square factorization through the Fubini–Study transition core $P_1 P_2 P_1$:
   `(P₂ * P₁) * (P₂ * P₁) = twoStateSandwich P₂ P₁ (P₁ * P₂ * P₁)`.
4. Linear decomposition of `twoStateSandwich`:
   `twoStateSandwich P₂ P₁ (A + C) = twoStateSandwich P₂ P₁ A + twoStateSandwich P₂ P₁ C`. -/
theorem archetype_A0_two_state_transition_sandwich_and_overlap
    {P1 P2 : B} (hP1 : P1 * P1 = P1) (hP2 : P2 * P2 = P2) (A C : B) :
    P2 * twoStateSandwich P2 P1 A = twoStateSandwich P2 P1 A ∧
    twoStateSandwich P2 P1 A * P1 = twoStateSandwich P2 P1 A ∧
    (P2 * P1) * (P2 * P1) = twoStateSandwich P2 P1 (P1 * P2 * P1) ∧
    twoStateSandwich P2 P1 (A + C) = twoStateSandwich P2 P1 A + twoStateSandwich P2 P1 C := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [twoStateSandwich]
    rw [← mul_assoc P2 P2 A, ← mul_assoc (P2 * P2) A P1, hP2]
  · dsimp [twoStateSandwich]
    rw [mul_assoc (P2 * A) P1 P1, hP1]
  · dsimp [twoStateSandwich]
    simp only [mul_assoc]
    rw [← mul_assoc P1 P1 (P2 * P1), hP1]
  · dsimp [twoStateSandwich]
    simp only [mul_add, add_mul]

/-- **Archetype $\mathcal{A}_1$ (`archetype_A1_spin_half_weak_value_amplification_identity`):**
Let $\sigma_x, \sigma_y \in B$ be any two anticommuting involutions ($\sigma_x^2 = 1$, $\sigma_y^2 = 1$,
$\{\sigma_x, \sigma_y\} = 0$), with pre-selection projector $P_x = 1 + \sigma_x$ and post-selection
projector $P_y = 1 + \sigma_y$. Then:
1. **Quadratic Spectral Bound:** $(\sigma_x + \sigma_y)^2 = 1 + 1$ and $(\sigma_x - \sigma_y)^2 = 1 + 1$.
2. **Eigen-Absorption:** $\sigma_x (1 + \sigma_x) = 1 + \sigma_x$ and $(1 + \sigma_y) \sigma_y = 1 + \sigma_y$.
3. **Weak-Value Amplification Identity (Transcript 00:25:27–00:29:18):**
   $$(1 + \sigma_y)(\sigma_x + \sigma_y)(1 + \sigma_x) = (1 + \sigma_y)(1 + \sigma_x) + (1 + \sigma_y)(1 + \sigma_x).$$
4. **Orthogonal Weak-Value Extinction:**
   $$(1 + \sigma_y)(\sigma_x - \sigma_y)(1 + \sigma_x) = 0.$$ -/
theorem archetype_A1_spin_half_weak_value_amplification_identity
    {σx σy : B} (hx : σx * σx = 1) (hy : σy * σy = 1) (hxy : racomm σx σy = 0) :
    (σx + σy) * (σx + σy) = 1 + 1 ∧
    (σx - σy) * (σx - σy) = 1 + 1 ∧
    σx * (1 + σx) = 1 + σx ∧
    (1 + σy) * σy = 1 + σy ∧
    (1 + σy) * (σx + σy) * (1 + σx) = ((1 + σy) * (1 + σx)) + ((1 + σy) * (1 + σx)) ∧
    (1 + σy) * (σx - σy) * (1 + σx) = 0 := by
  have h_anti : σx * σy + σy * σx = 0 := hxy
  have h_abs_x : σx * (1 + σx) = 1 + σx := by
    rw [mul_add, mul_one, hx, add_comm]
  have h_abs_y : (1 + σy) * σy = 1 + σy := by
    rw [add_mul, one_mul, hy, add_comm]
  refine ⟨?_, ?_, h_abs_x, h_abs_y, ?_, ?_⟩
  · calc (σx + σy) * (σx + σy)
      _ = σx * σx + σy * σy + (σx * σy + σy * σx) := by
          simp only [mul_add, add_mul]; abel
      _ = 1 + 1 := by rw [hx, hy, h_anti, add_zero]
  · calc (σx - σy) * (σx - σy)
      _ = σx * σx + σy * σy - (σx * σy + σy * σx) := by
          simp only [mul_sub, sub_mul]; abel
      _ = 1 + 1 := by rw [hx, hy, h_anti, sub_zero]
  · calc (1 + σy) * (σx + σy) * (1 + σx)
      _ = (1 + σy) * (σx * (1 + σx)) + ((1 + σy) * σy) * (1 + σx) := by
          simp only [mul_add, add_mul, mul_assoc]
      _ = ((1 + σy) * (1 + σx)) + ((1 + σy) * (1 + σx)) := by rw [h_abs_x, h_abs_y]
  · calc (1 + σy) * (σx - σy) * (1 + σx)
      _ = (1 + σy) * (σx * (1 + σx)) - ((1 + σy) * σy) * (1 + σx) := by
          simp only [mul_sub, sub_mul, mul_assoc]
      _ = ((1 + σy) * (1 + σx)) - ((1 + σy) * (1 + σx)) := by rw [h_abs_x, h_abs_y]
      _ = 0 := sub_self ((1 + σy) * (1 + σx))

-- ============================================================================
-- 2. 2x2 MATRIX OPERATOR ALGEBRA `Mat2 B`: ARCHETYPES A₂, A₃, A₄
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
@[simp] def add (M N : Mat2 B) : Mat2 B :=
  ⟨M.a11 + N.a11, M.a12 + N.a12, M.a21 + N.a21, M.a22 + N.a22⟩

/-- Entrywise negation in `Mat2 B`. -/
@[simp] def neg (M : Mat2 B) : Mat2 B :=
  ⟨-M.a11, -M.a12, -M.a21, -M.a22⟩

/-- Entrywise subtraction in `Mat2 B`. -/
@[simp] def sub (M N : Mat2 B) : Mat2 B :=
  ⟨M.a11 - N.a11, M.a12 - N.a12, M.a21 - N.a21, M.a22 - N.a22⟩

/-- Non-commutative $2 \times 2$ matrix multiplication in `Mat2 B`. -/
@[simp] def mul (M N : Mat2 B) : Mat2 B :=
  ⟨M.a11 * N.a11 + M.a12 * N.a21, M.a11 * N.a12 + M.a12 * N.a22,
   M.a21 * N.a11 + M.a22 * N.a21, M.a21 * N.a12 + M.a22 * N.a22⟩

/-- Natural-number scalar multiplication on `Mat2 B`. -/
@[simp] def nsmulMat (n : ℕ) (M : Mat2 B) : Mat2 B :=
  ⟨n • M.a11, n • M.a12, n • M.a21, n • M.a22⟩

/-- Integer scalar multiplication on `Mat2 B`. -/
@[simp] def zsmulMat (n : ℤ) (M : Mat2 B) : Mat2 B :=
  ⟨n • M.a11, n • M.a12, n • M.a21, n • M.a22⟩

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
/-- `(M + N).a11 = M.a11 + N.a11`. -/
@[simp] lemma add_a11 (M N : Mat2 B) : (M + N).a11 = M.a11 + N.a11 := by
  have h : (M + N).a11 = M.a11 + N.a11 := rfl; exact h
/-- `(M + N).a12 = M.a12 + N.a12`. -/
@[simp] lemma add_a12 (M N : Mat2 B) : (M + N).a12 = M.a12 + N.a12 := by
  have h : (M + N).a12 = M.a12 + N.a12 := rfl; exact h
/-- `(M + N).a21 = M.a21 + N.a21`. -/
@[simp] lemma add_a21 (M N : Mat2 B) : (M + N).a21 = M.a21 + N.a21 := by
  have h : (M + N).a21 = M.a21 + N.a21 := rfl; exact h
/-- `(M + N).a22 = M.a22 + N.a22`. -/
@[simp] lemma add_a22 (M N : Mat2 B) : (M + N).a22 = M.a22 + N.a22 := by
  have h : (M + N).a22 = M.a22 + N.a22 := rfl; exact h
/-- `(-M).a11 = -M.a11`. -/
@[simp] lemma neg_a11 (M : Mat2 B) : (-M).a11 = -M.a11 := by
  have h : (-M).a11 = -M.a11 := rfl; exact h
/-- `(-M).a12 = -M.a12`. -/
@[simp] lemma neg_a12 (M : Mat2 B) : (-M).a12 = -M.a12 := by
  have h : (-M).a12 = -M.a12 := rfl; exact h
/-- `(-M).a21 = -M.a21`. -/
@[simp] lemma neg_a21 (M : Mat2 B) : (-M).a21 = -M.a21 := by
  have h : (-M).a21 = -M.a21 := rfl; exact h
/-- `(-M).a22 = -M.a22`. -/
@[simp] lemma neg_a22 (M : Mat2 B) : (-M).a22 = -M.a22 := by
  have h : (-M).a22 = -M.a22 := rfl; exact h
/-- `(M - N).a11 = M.a11 - N.a11`. -/
@[simp] lemma sub_a11 (M N : Mat2 B) : (M - N).a11 = M.a11 - N.a11 := by
  have h : (M - N).a11 = M.a11 - N.a11 := rfl; exact h
/-- `(M - N).a12 = M.a12 - N.a12`. -/
@[simp] lemma sub_a12 (M N : Mat2 B) : (M - N).a12 = M.a12 - N.a12 := by
  have h : (M - N).a12 = M.a12 - N.a12 := rfl; exact h
/-- `(M - N).a21 = M.a21 - N.a21`. -/
@[simp] lemma sub_a21 (M N : Mat2 B) : (M - N).a21 = M.a21 - N.a21 := by
  have h : (M - N).a21 = M.a21 - N.a21 := rfl; exact h
/-- `(M - N).a22 = M.a22 - N.a22`. -/
@[simp] lemma sub_a22 (M N : Mat2 B) : (M - N).a22 = M.a22 - N.a22 := by
  have h : (M - N).a22 = M.a22 - N.a22 := rfl; exact h
/-- `(M * N).a11 = M.a11 * N.a11 + M.a12 * N.a21`. -/
@[simp] lemma mul_a11 (M N : Mat2 B) : (M * N).a11 = M.a11 * N.a11 + M.a12 * N.a21 := by
  have h : (M * N).a11 = M.a11 * N.a11 + M.a12 * N.a21 := rfl; exact h
/-- `(M * N).a12 = M.a11 * N.a12 + M.a12 * N.a22`. -/
@[simp] lemma mul_a12 (M N : Mat2 B) : (M * N).a12 = M.a11 * N.a12 + M.a12 * N.a22 := by
  have h : (M * N).a12 = M.a11 * N.a12 + M.a12 * N.a22 := rfl; exact h
/-- `(M * N).a21 = M.a21 * N.a11 + M.a22 * N.a21`. -/
@[simp] lemma mul_a21 (M N : Mat2 B) : (M * N).a21 = M.a21 * N.a11 + M.a22 * N.a21 := by
  have h : (M * N).a21 = M.a21 * N.a11 + M.a22 * N.a21 := rfl; exact h
/-- `(M * N).a22 = M.a21 * N.a12 + M.a22 * N.a22`. -/
@[simp] lemma mul_a22 (M N : Mat2 B) : (M * N).a22 = M.a21 * N.a12 + M.a22 * N.a22 := by
  have h : (M * N).a22 = M.a21 * N.a12 + M.a22 * N.a22 := rfl; exact h

macro "nc_mat2" : tactic =>
  `(tactic|
    (try ext
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
  add_assoc := by intros; nc_mat2
  zero := zero
  zero_add := by intros; nc_mat2
  add_zero := by intros; nc_mat2
  nsmul := nsmulMat
  nsmul_zero := by intros; ext <;> exact AddMonoid.nsmul_zero _
  nsmul_succ := by intros; ext <;> exact AddMonoid.nsmul_succ _ _
  zsmul := zsmulMat
  zsmul_zero' := by intros; ext <;> exact SubNegMonoid.zsmul_zero' _
  zsmul_succ' := by intros; ext <;> exact SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' := by intros; ext <;> exact SubNegMonoid.zsmul_neg' _ _
  neg := neg
  sub := sub
  sub_eq_add_neg := by intros; nc_mat2
  neg_add_cancel := by intros; nc_mat2
  add_comm := by intros; nc_mat2
  mul := mul
  left_distrib := by intros; nc_mat2
  right_distrib := by intros; nc_mat2
  zero_mul := by intros; nc_mat2
  mul_zero := by intros; nc_mat2
  mul_assoc := by intros; nc_mat2
  one := one
  one_mul := by intros; nc_mat2
  mul_one := by intros; nc_mat2

/-- Matrix trace $\operatorname{tr}_2(M) = m_{11} + m_{22} \in B$. -/
@[simp] def tr2 (M : Mat2 B) : B := M.a11 + M.a22

/-- Diagonal scalar embedding $\mathrm{diagScalar}(c) = \begin{pmatrix} c & 0 \\ 0 & c \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def diagScalar (c : B) : Mat2 B := ⟨c, 0, 0, c⟩

/-- Symmetric Pauli shift matrix $E_x = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def Ex : Mat2 B := ⟨0, 1, 1, 0⟩

/-- Symplectic bivector matrix $E_y = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def Ey : Mat2 B := ⟨0, -1, 1, 0⟩

/-- Diagonal Pauli grading matrix $E_z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def Ez : Mat2 B := ⟨1, 0, 0, -1⟩

/-- Forward nilpotent shift matrix $E_{01} = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def E01 : Mat2 B := ⟨0, 1, 0, 0⟩

/-- Two-slit state matrix $\rho(d_1, d_2, u_+, u_-) = \begin{pmatrix} d_1 & u_+ \\ u_- & d_2 \end{pmatrix}$ with off-diagonal coherences. -/
@[simp] def twoPacketState (d1 d2 u_plus u_minus : B) : Mat2 B :=
  ⟨d1, u_plus, u_minus, d2⟩

/-- Local support-preserving observable $D_{\mathrm{loc}}(f_1, f_2) = \begin{pmatrix} f_1 & 0 \\ 0 & f_2 \end{pmatrix}$. -/
@[simp] def localObs (f1 f2 : B) : Mat2 B :=
  ⟨f1, 0, 0, f2⟩

/-- Non-local Weyl shift / modular translation operator $T_L(\tau_+, \tau_-) = \begin{pmatrix} 0 & \tau_+ \\ \tau_- & 0 \end{pmatrix}$. -/
@[simp] def modularShift (τ_plus τ_minus : B) : Mat2 B :=
  ⟨0, τ_plus, τ_minus, 0⟩

/-- Local diagonal gauge transformation $G(g_1, g_2) = \begin{pmatrix} g_1 & 0 \\ 0 & g_2 \end{pmatrix}$. -/
@[simp] def gaugeDiag (g1 g2 : B) : Mat2 B :=
  ⟨g1, 0, 0, g2⟩

/-- **Unconditional Pauli Matrix Realization of Archetype $\mathcal{A}_1$ (`archetype_A1_mat2_pauli_weak_value_amplification`):**
In `Mat2 B` over ANY non-commutative ring `[Ring B]`, the concrete involutions $E_x$ and $E_z$
satisfy $E_x^2 = 1$, $E_z^2 = 1$, $\{E_x, E_z\} = 0$, $(E_x + E_z)^2 = 2 \cdot 1$, the bilateral
weak-value amplification $(1 + E_z)(E_x + E_z)(1 + E_x) = 2(1 + E_z)(1 + E_x)$, and orthogonal
extinction $(1 + E_z)(E_x - E_z)(1 + E_x) = 0$. -/
theorem archetype_A1_mat2_pauli_weak_value_amplification :
    (Ex : Mat2 B) * Ex = 1 ∧
    (Ez : Mat2 B) * Ez = 1 ∧
    racomm (Ex : Mat2 B) Ez = 0 ∧
    ((Ex : Mat2 B) + Ez) * (Ex + Ez) = 1 + 1 ∧
    ((1 : Mat2 B) + Ez) * (Ex + Ez) * (1 + Ex) =
      (((1 : Mat2 B) + Ez) * (1 + Ex)) + (((1 : Mat2 B) + Ez) * (1 + Ex)) ∧
    ((1 : Mat2 B) + Ez) * (Ex - Ez) * (1 + Ex) = 0 := by
  have hx : (Ex : Mat2 B) * Ex = 1 := by simp only [Ex]; nc_mat2
  have hz : (Ez : Mat2 B) * Ez = 1 := by simp only [Ez]; nc_mat2
  have hxz : racomm (Ex : Mat2 B) Ez = 0 := by simp only [racomm, Ex, Ez]; nc_mat2
  obtain ⟨h_sq, _, _, _, h_amp, h_ext⟩ :=
    archetype_A1_spin_half_weak_value_amplification_identity hx hz hxz
  exact ⟨hx, hz, hxz, h_sq, h_amp, h_ext⟩

/-- **Archetype $\mathcal{A}_2$ (`archetype_A2_local_moment_blindness_vs_modular_shift_sensitivity`):**
Formalizes Transcript 00:40:40–00:44:21 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. **Blindness of Local Polynomial Moments:**
   For any $\rho = \mathrm{twoPacketState}(d_1, d_2, u_+, u_-)$ and $D = \mathrm{localObs}(f_1, f_2)$,
   both $\operatorname{tr}_2(\rho D)$ and $\operatorname{tr}_2(\rho D^2)$ depend ONLY on $(d_1, d_2)$
   and are completely independent of the interference coherences $(u_+, u_-)$:
   `tr2 (twoPacketState d1 d2 u_plus u_minus * D) = tr2 (twoPacketState d1 d2 0 0 * D)`.
2. **Phase Sensitivity of the Modular Shift Operator $T_L$:**
   `tr2 (twoPacketState d1 d2 u_plus u_minus * modularShift τ_plus τ_minus) = u_plus * τ_minus + u_minus * τ_plus`,
   annihilating $(d_1, d_2)$ and directly extracting the interference phase. -/
theorem archetype_A2_local_moment_blindness_vs_modular_shift_sensitivity
    (d1 d2 u_plus u_minus f1 f2 τ_plus τ_minus : B) :
    tr2 (twoPacketState d1 d2 u_plus u_minus * localObs f1 f2) = d1 * f1 + d2 * f2 ∧
    tr2 (twoPacketState d1 d2 u_plus u_minus * localObs f1 f2) =
      tr2 (twoPacketState d1 d2 0 0 * localObs f1 f2) ∧
    tr2 (twoPacketState d1 d2 u_plus u_minus * (localObs f1 f2 * localObs f1 f2)) =
      tr2 (twoPacketState d1 d2 0 0 * (localObs f1 f2 * localObs f1 f2)) ∧
    tr2 (twoPacketState d1 d2 u_plus u_minus * modularShift τ_plus τ_minus) =
      u_plus * τ_minus + u_minus * τ_plus ∧
    tr2 (twoPacketState d1 d2 0 0 * modularShift τ_plus τ_minus) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [twoPacketState, localObs, modularShift, tr2]; nc_mat2

/-- **Archetype $\mathcal{A}_3$ (`archetype_A3_nonlocal_heisenberg_commutator_for_modular_shift`):**
Formalizes Transcript 00:45:28–00:48:48 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. **Forward Weyl Shift Commutator ($[e^{i p L / \hbar}, V(x)] = (V(x + L) - V(x)) e^{i p L / \hbar}$):**
   For $V_{\mathrm{pot}} = \mathrm{localObs}(V_1, V_2)$, the Heisenberg commutator with $E_{01}$ is:
   `E01 * V_pot - V_pot * E01 = ⟨0, V2 - V1, 0, 0⟩ = diagScalar (V2 - V1) * E01`.
2. **General Modular Shift Commutator:**
   `modularShift τ_plus τ_minus * V_pot - V_pot * modularShift τ_plus τ_minus = ⟨0, τ_plus * V2 - V1 * τ_plus, τ_minus * V1 - V2 * τ_minus, 0⟩`.
3. **Symmetric Shift Commutator ($E_x$):**
   `Ex * V_pot - V_pot * Ex = -(diagScalar (V2 - V1) * Ey)`. -/
theorem archetype_A3_nonlocal_heisenberg_commutator_for_modular_shift
    (V1 V2 τ_plus τ_minus : B) :
    E01 * localObs V1 V2 - localObs V1 V2 * E01 = ⟨0, V2 - V1, 0, 0⟩ ∧
    E01 * localObs V1 V2 - localObs V1 V2 * E01 = diagScalar (V2 - V1) * E01 ∧
    modularShift τ_plus τ_minus * localObs V1 V2 - localObs V1 V2 * modularShift τ_plus τ_minus =
      ⟨0, τ_plus * V2 - V1 * τ_plus, τ_minus * V1 - V2 * τ_minus, 0⟩ ∧
    Ex * localObs V1 V2 - localObs V1 V2 * Ex = -(diagScalar (V2 - V1) * Ey) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [localObs, modularShift, diagScalar, E01, Ex, Ey]; nc_mat2

/-- **Archetype $\mathcal{A}_4$ (`archetype_A4_aharonov_bohm_gauge_covariant_modular_velocity`):**
Formalizes Transcript 00:55:56–00:57:55 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. **Gauge-Covariant Modular Velocity Transformation:**
   Under local gauge transformations $G = \mathrm{gaugeDiag}(g_1, g_2)$ and $G_{\mathrm{inv}} = \mathrm{gaugeDiag}(g_{1,\mathrm{inv}}, g_{2,\mathrm{inv}})$,
   the Wilson-dressed modular shift $T_{\mathrm{AB}} = \mathrm{modularShift}(W_{12}, W_{21})$ transforms as:
   `G * T_AB * G_inv = modularShift (g1 * W12 * g2_inv) (g2 * W21 * g1_inv)`.
2. **Closed Aharonov–Bohm Holonomy Loop:**
   `T_AB * T_AB = localObs (W12 * W21) (W21 * W12)`, and when `g2_inv * g2 = 1` and `g1_inv * g1 = 1`,
   `(G * T_AB * G_inv)² = localObs (g1 * W12 * W21 * g1_inv) (g2 * W21 * W12 * g2_inv)`. -/
theorem archetype_A4_aharonov_bohm_gauge_covariant_modular_velocity
    (g1 g2 g1_inv g2_inv W12 W21 : B)
    (hg1 : g1_inv * g1 = 1) (hg2 : g2_inv * g2 = 1) :
    gaugeDiag g1 g2 * modularShift W12 W21 * gaugeDiag g1_inv g2_inv =
      modularShift (g1 * W12 * g2_inv) (g2 * W21 * g1_inv) ∧
    modularShift W12 W21 * modularShift W12 W21 = localObs (W12 * W21) (W21 * W12) ∧
    (gaugeDiag g1 g2 * modularShift W12 W21 * gaugeDiag g1_inv g2_inv) *
      (gaugeDiag g1 g2 * modularShift W12 W21 * gaugeDiag g1_inv g2_inv) =
      localObs (g1 * W12 * W21 * g1_inv) (g2 * W21 * W12 * g2_inv) := by
  have h1 : gaugeDiag g1 g2 * modularShift W12 W21 * gaugeDiag g1_inv g2_inv =
      modularShift (g1 * W12 * g2_inv) (g2 * W21 * g1_inv) := by
    simp only [gaugeDiag, modularShift]; nc_mat2
  have h2 : modularShift W12 W21 * modularShift W12 W21 = localObs (W12 * W21) (W21 * W12) := by
    simp only [modularShift, localObs]; nc_mat2
  refine ⟨h1, h2, ?_⟩
  rw [h1]
  ext <;>
  · simp only [modularShift, localObs, mul_a11, mul_a12, mul_a21, mul_a22,
               mul_zero, zero_mul, add_zero, zero_add]
    try (calc g1 * W12 * g2_inv * (g2 * W21 * g1_inv)
          _ = g1 * W12 * (g2_inv * g2) * W21 * g1_inv := by simp only [mul_assoc]
          _ = g1 * W12 * W21 * g1_inv                 := by rw [hg2, mul_one])
    try (calc g2 * W21 * g1_inv * (g1 * W12 * g2_inv)
          _ = g2 * W21 * (g1_inv * g1) * W12 * g2_inv := by simp only [mul_assoc]
          _ = g2 * W21 * W12 * g2_inv                 := by rw [hg1, mul_one])

/-- Explicit noncommutativity witness for `Mat2 ℤ`:
`Ex * Ez ≠ Ez * Ex`. -/
theorem mat2_aharonov_noncommutative :
    ∃ X Y : Mat2 ℤ, X * Y ≠ Y * X := by
  refine ⟨Ex, Ez, ?_⟩
  intro h
  have h12 : (Ex * Ez : Mat2 ℤ).a12 = (Ez * Ex : Mat2 ℤ).a12 := congrArg Mat2.a12 h
  revert h12
  decide

end Mat2

end InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset
