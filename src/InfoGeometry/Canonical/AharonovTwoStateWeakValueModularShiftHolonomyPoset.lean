/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- [HIVE-MINDPROVENANCE HEADER]
-- LAYER: Canonical Finite Algebraic Model (Two-Boundary Sandwich and Modular Shifts)
-- ARCHITECTURAL ROLE: Noncommutative Ring Identities and Explicit Finite Matrix Readouts
-- EPISTEMIC STATUS: Algebraic identities only; physical interpretation requires separate structures
-- DEPENDENCIES: Mathlib.Algebra.Ring.Defs, Mathlib.Tactic.Abel
-- [END HEADER]

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel

/-!
# Two-Boundary Sandwich Identities and Finite Matrix Readouts

The ring-level results are identities over an arbitrary associative noncommutative
`[Ring B]`. The matrix results are finite `Mat2 B` identities. They do not define
normalized Hilbert-space states, an inner product, probabilities, or a weak-value
quotient; physical terminology below records motivation rather than a proved
physical interpretation.

## Causal Poset Architecture:
- **Archetype $\mathcal{A}_0$ (`archetype_A0_two_state_transition_sandwich_and_overlap`)**:
  For any two non-commuting idempotents `P₁² = P₁` and `P₂² = P₂` in `B`, proves boundary
  absorption `P₂ * W₂₁(A) = W₂₁(A) * P₁ = W₂₁(A)` and `(P₂ * P₁)² = P₂ * (P₁ * P₂ * P₁)`.
- **Archetype $\mathcal{A}_1$ (`archetype_A1_spin_half_weak_value_amplification_identity` & `archetype_A1_mat2_pauli_weak_value_amplification`)**:
  For any anticommuting involutions `σx² = 1, σy² = 1, {σx, σy} = 0` in `B` (and unconditionally
  for `Ex, Ez ∈ Mat2 B`), proves an unnormalized boundary-sandwich identity. The factors
  `1 + σx` and `1 + σy` are quasi-idempotent with square twice themselves, not idempotent
  projectors in general; no weak-value quotient or normalization is formed here.
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
- **Archetype $\mathcal{A}_5$ (`archetype_A5_quantum_cheshire_cat_two_state_decoupling`)**:
  In `Mat2 B`, proves a two-arm operator decoupling identity. The theorem does not
  supply normalized states or measurement semantics.

- **Scope note:** these declarations certify only the displayed ring and finite-matrix
  equalities under their Lean hypotheses. They do not establish a physical experiment,
  a weak-value limit, or an Aharonov–Bohm measurement model.

## Three-Bucket Audit Map:
- **BUCKET 1 (Keep)**: `twoStateSandwich`, `archetype_A0_two_state_transition_sandwich_and_overlap`,
  `archetype_A1_spin_half_weak_value_amplification_identity`, `Mat2`, `twoPacketState`,
  `localObs`, `modularShift`, `gaugeDiag`, `PsiEnt`, `PhiEnt`, `PsiDiag`, `PhiDiag`,
  `archetype_A1_mat2_pauli_weak_value_amplification`,
  `archetype_A2_local_moment_blindness_vs_modular_shift_sensitivity`,
  `archetype_A3_nonlocal_heisenberg_commutator_for_modular_shift`,
  `archetype_A4_aharonov_bohm_gauge_covariant_modular_velocity`,
  `archetype_A5_quantum_cheshire_cat_two_state_decoupling`,
  `archetype_G0_clifford_intertwining_and_entangled_quasiprojectors`,
  `archetype_G1_entangled_corner_channel_decoupling`,
  `archetype_G2_widom_hankel_toeplitz_cancellation_of_joint_product`,
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

/-- The unnormalized `1 + x` associated with an involution is quasi-idempotent:
its square is twice itself. It is not generally an idempotent projector. -/
lemma one_add_involution_sq {x : B} (hx : x * x = 1) :
    (1 + x) * (1 + x) = (1 + x) + (1 + x) := by
  calc
    (1 + x) * (1 + x) = 1 * (1 + x) + x * (1 + x) := add_mul 1 x (1 + x)
    _ = (1 + x) + (x + x * x) := by rw [one_mul, mul_add, mul_one]
    _ = (1 + x) + (x + 1) := by rw [hx]
    _ = (1 + x) + (1 + x) := by rw [add_comm x 1]

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
    rw [← mul_assoc P2 (P2 * A) P1, ← mul_assoc P2 P2 A, hP2]
  · dsimp [twoStateSandwich]
    rw [mul_assoc (P2 * A) P1 P1, hP1]
  · dsimp [twoStateSandwich]
    simp only [mul_assoc]
    rw [hP1]
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
  · rw [mul_add (1 + σy) σx σy, add_mul, mul_assoc (1 + σy) σx (1 + σx), h_abs_x, h_abs_y]
  · rw [mul_sub (1 + σy) σx σy, sub_mul, mul_assoc (1 + σy) σx (1 + σx), h_abs_x, h_abs_y, sub_self]

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

/-- Diagonal multiplication law for `localObs`. -/
@[simp] lemma localObs_mul (f1 f2 g1 g2 : B) :
    localObs f1 f2 * localObs g1 g2 = localObs (f1 * g1) (f2 * g2) := by
  ext <;> simp [localObs]

/-- **Archetype $\mathcal{A}_5$ (`archetype_A5_quantum_cheshire_cat_two_state_decoupling`):**
Formalizes Aharonov's Quantum Cheshire Cat (Transcript 00:01:08) in `Mat2 B` over ANY
non-commutative ring `[Ring B]` equipped with anticommuting spin involutions
$\sigma_x^2 = 1$, $\sigma_z^2 = 1$, $\{\sigma_x, \sigma_z\} = 0$:
For the pre-selection operator $\Psi_{\mathrm{cat}} = \mathrm{localObs}(1 + \sigma_x, (1 - \sigma_x)\sigma_z)$,
post-selection operator $\Phi_{\mathrm{cat}} = \mathrm{localObs}(1 + \sigma_x, 1 + \sigma_x)$,
left/right spatial path projectors $P_{\mathrm{left}} = \mathrm{localObs}(1, 0)$,
$P_{\mathrm{right}} = \mathrm{localObs}(0, 1)$, and spin observable $S_z = \mathrm{diagScalar}(\sigma_z)$:
1. **Particle Presence in Left Arm Only:**
   $\Phi_{\mathrm{cat}} P_{\mathrm{left}} \Psi_{\mathrm{cat}} = \mathrm{localObs}((1 + \sigma_x) + (1 + \sigma_x), 0)$
   and $\Phi_{\mathrm{cat}} P_{\mathrm{right}} \Psi_{\mathrm{cat}} = 0$.
2. **Spin Presence in Right Arm Only (Spatial Separation of Spin from Particle):**
   $\Phi_{\mathrm{cat}} (P_{\mathrm{left}} S_z) \Psi_{\mathrm{cat}} = 0$ and
   $\Phi_{\mathrm{cat}} (P_{\mathrm{right}} S_z) \Psi_{\mathrm{cat}} = \mathrm{localObs}(0, (1 + \sigma_x) + (1 + \sigma_x))$. -/
theorem archetype_A5_quantum_cheshire_cat_two_state_decoupling
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Qplus   := 1 + σx
    let Qminus  := 1 - σx
    let Ψ_cat   := localObs Qplus (Qminus * σz)
    let Φ_cat   := localObs Qplus Qplus
    let P_left  := localObs (1 : B) 0
    let P_right := localObs (0 : B) 1
    let S_z     := diagScalar σz
    Φ_cat * P_left * Ψ_cat = localObs (Qplus + Qplus) 0 ∧
    Φ_cat * P_right * Ψ_cat = 0 ∧
    Φ_cat * (P_left * S_z) * Ψ_cat = 0 ∧
    Φ_cat * (P_right * S_z) * Ψ_cat = localObs 0 (Qplus + Qplus) := by
  intro Qplus Qminus Ψ_cat Φ_cat P_left P_right S_z
  have h_anti : σx * σz + σz * σx = 0 := hxz
  have hQ_sq : Qplus * Qplus = Qplus + Qplus := by
    dsimp [Qplus]
    exact one_add_involution_sq hx
  have hQ_orth : Qplus * (Qminus * σz) = 0 := by
    have hQM : Qplus * Qminus = 0 := by
      calc Qplus * Qminus
        _ = 1 - σx * σx := by
            dsimp [Qplus, Qminus]; (simp only [mul_sub, add_mul, mul_one, one_mul]); abel
        _ = 0 := by rw [hx, sub_self]
    rw [← mul_assoc, hQM, zero_mul]
  have hQ_flip : Qplus * σz = σz * Qminus := by
    calc Qplus * σz
      _ = σz * (1 - σx) + (σx * σz + σz * σx) := by
          dsimp [Qplus]; (simp only [add_mul, mul_sub, one_mul, mul_one]); abel
      _ = σz * Qminus := by dsimp [Qminus]; rw [h_anti, add_zero]
  have hQ_flip2 : Qminus * σz = σz * Qplus := by
    calc Qminus * σz
      _ = σz * (1 + σx) - (σx * σz + σz * σx) := by
          dsimp [Qminus]; (simp only [sub_mul, mul_add, one_mul, mul_one]); abel
      _ = σz * Qplus := by dsimp [Qplus]; rw [h_anti, sub_zero]
  have hQzQplus : Qplus * σz * Qplus = 0 := by
    have hMQ : Qminus * Qplus = 0 := by
      calc Qminus * Qplus
        _ = 1 - σx * σx := by
            dsimp [Qplus, Qminus]; (simp only [sub_mul, mul_add, mul_one, one_mul]); abel
        _ = 0 := by rw [hx, sub_self]
    rw [hQ_flip, mul_assoc, hMQ, mul_zero]
  have hQzQminus : Qplus * σz * (Qminus * σz) = Qplus + Qplus := by
    rw [hQ_flip2, mul_assoc Qplus σz (σz * Qplus), ← mul_assoc σz σz Qplus, hz, one_mul, hQ_sq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change localObs Qplus Qplus * localObs 1 0 * localObs Qplus (Qminus * σz) =
      localObs (Qplus + Qplus) 0
    rw [localObs_mul, localObs_mul]
    simp only [mul_one, zero_mul, mul_zero]
    rw [hQ_sq]
  · change localObs Qplus Qplus * localObs 0 1 * localObs Qplus (Qminus * σz) = 0
    rw [localObs_mul, localObs_mul]
    simp only [mul_zero, zero_mul, mul_one]
    rw [hQ_orth]
    ext <;> exact Eq.refl _
  · change localObs Qplus Qplus * (localObs 1 0 * diagScalar σz) *
      localObs Qplus (Qminus * σz) = 0
    rw [show diagScalar σz = localObs σz σz from Eq.refl _, localObs_mul, localObs_mul, localObs_mul]
    simp only [mul_zero, zero_mul, one_mul]
    rw [hQzQplus]
    ext <;> exact Eq.refl _
  · change localObs Qplus Qplus * (localObs 0 1 * diagScalar σz) *
      localObs Qplus (Qminus * σz) = localObs 0 (Qplus + Qplus)
    rw [show diagScalar σz = localObs σz σz from Eq.refl _, localObs_mul, localObs_mul, localObs_mul]
    simp only [mul_zero, zero_mul, one_mul]
    rw [hQzQminus]

-- ============================================================================
-- 3. ENTANGLED 2x2 QUASI-PROJECTOR DECOUPLING & WIDOM–HANKEL–TOEPLITZ CANCELLATION
-- ============================================================================

/-- Left spatial corner projector $P_{\mathrm{left}} = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def P_left : Mat2 B := ⟨1, 0, 0, 0⟩

/-- Right spatial corner projector $P_{\mathrm{right}} = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix} \in \mathrm{Mat}_2(B)$. -/
@[simp] def P_right : Mat2 B := ⟨0, 0, 0, 1⟩

/-- Full non-diagonal entangled pre-selection quasi-projector in `Mat2 B`:
$$\Psi_{\mathrm{ent}}(\sigma_x, \sigma_z) = \begin{pmatrix} 1 + \sigma_x & (1 + \sigma_x)\sigma_z \\ \sigma_z(1 + \sigma_x) & 1 - \sigma_x \end{pmatrix}.$$ -/
@[simp] def PsiEnt (σx σz : B) : Mat2 B :=
  ⟨1 + σx, (1 + σx) * σz,
   σz * (1 + σx), 1 - σx⟩

/-- Full non-diagonal entangled post-selection quasi-projector in `Mat2 B`:
$$\Phi_{\mathrm{ent}}(\sigma_x) = \begin{pmatrix} 1 + \sigma_x & 1 + \sigma_x \\ 1 + \sigma_x & 1 + \sigma_x \end{pmatrix}.$$ -/
@[simp] def PhiEnt (σx : B) : Mat2 B :=
  ⟨1 + σx, 1 + σx,
   1 + σx, 1 + σx⟩

/-- Diagonal pre-selection state $\Psi_{\mathrm{diag}}(\sigma_x, \sigma_z) = \mathrm{localObs}(1 + \sigma_x, (1 - \sigma_x)\sigma_z)$. -/
@[simp] def PsiDiag (σx σz : B) : Mat2 B :=
  localObs (1 + σx) ((1 - σx) * σz)

/-- Diagonal post-selection state $\Phi_{\mathrm{diag}}(\sigma_x) = \mathrm{localObs}(1 + \sigma_x, 1 + \sigma_x)$. -/
@[simp] def PhiDiag (σx : B) : Mat2 B :=
  localObs (1 + σx) (1 + σx)

/-- Helper lemma: $\sigma_z \sigma_x = -(\sigma_x \sigma_z)$ from $\mathrm{racomm}(\sigma_x, \sigma_z) = 0$. -/
lemma comm_flip_of_anticomm {σx σz : B} (hxz : racomm σx σz = 0) :
    σz * σx = -(σx * σz) := by
  unfold racomm at hxz
  calc σz * σx
    _ = (σx * σz + σz * σx) - σx * σz := by abel
    _ = 0 - σx * σz                   := by rw [hxz]
    _ = -(σx * σz)                    := by abel

/-- Helper lemma for right-associated multi-factor products containing $\sigma_z \sigma_x$. -/
lemma mul_comm_flip_of_anticomm {σx σz : B} (hxz : racomm σx σz = 0) (Y : B) :
    σz * (σx * Y) = -(σx * (σz * Y)) := by
  rw [← mul_assoc σz σx Y, comm_flip_of_anticomm hxz, neg_mul, mul_assoc]

/-- Helper lemma: $\sigma (\sigma Y) = Y$ when $\sigma^2 = 1$. -/
lemma sq_left_of_sq_one {σ : B} (h : σ * σ = 1) (Y : B) :
    σ * (σ * Y) = Y := by
  rw [← mul_assoc, h, one_mul]

/-- **Archetype $\mathcal{G}_0$ (`archetype_G0_clifford_intertwining_and_entangled_quasiprojectors`):**
For ANY anticommuting involutions $\sigma_x^2 = 1$, $\sigma_z^2 = 1$, $\{\sigma_x, \sigma_z\} = 0$ in `[Ring B]`:
1. **Peirce Intertwining:** $(1 + \sigma_x)\sigma_z = \sigma_z(1 - \sigma_x)$, $(1 + \sigma_x)\sigma_z(1 + \sigma_x) = 0$,
   and $(1 + \sigma_x)\sigma_z(1 - \sigma_x)\sigma_z = 2(1 + \sigma_x)$.
2. **Entangled Quasi-Projector Idempotency ($\Psi_{\mathrm{ent}}^2 = 4\Psi_{\mathrm{ent}}$ and $\Phi_{\mathrm{ent}}^2 = 4\Phi_{\mathrm{ent}}$):**
   Both full $2 \times 2$ entangled matrices $\Psi_{\mathrm{ent}}$ and $\Phi_{\mathrm{ent}}$ satisfy $M^2 = 4 \cdot M$. -/
theorem archetype_G0_clifford_intertwining_and_entangled_quasiprojectors
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Ψ := PsiEnt σx σz
    let Φ := PhiEnt σx
    (1 + σx) * σz = σz * (1 - σx) ∧
    (1 + σx) * σz * (1 + σx) = 0 ∧
    (1 + σx) * σz * (1 - σx) * σz = (1 + σx) + (1 + σx) ∧
    Ψ * Ψ = Ψ + Ψ + Ψ + Ψ ∧
    Φ * Φ = Φ + Φ + Φ + Φ := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hxY := sq_left_of_sq_one hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [add_mul, mul_sub, one_mul, mul_one, hflip]; abel
  · simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc, hflip, hxY, mul_neg]; abel
  · simp only [add_mul, mul_sub, sub_mul, one_mul, mul_one, mul_assoc, hflip, hz, hxY, mul_neg, neg_mul]; abel
  · ext <;>
    · dsimp [PsiEnt]
      simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                 add_a11, add_a12, add_a21, add_a22,
                 mul_add, add_mul, sub_mul, mul_sub,
                 mul_one, one_mul, mul_assoc,
                 hflip, hflipY, hx, hz, hxY,
                 neg_mul, mul_neg, neg_add_rev, neg_neg]
      try abel
  · ext <;>
    · dsimp [PhiEnt]
      simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                 add_a11, add_a12, add_a21, add_a22,
                 mul_add, add_mul, mul_one, one_mul, hx]
      try abel

/-- **Archetype $\mathcal{G}_1$ (`archetype_G1_entangled_corner_channel_decoupling`):**
Proves BOTH the full entangled $2 \times 2$ decoupling ($\Psi_{\mathrm{ent}}, \Phi_{\mathrm{ent}}$)
AND the diagonal decoupling ($\Psi_{\mathrm{diag}}, \Phi_{\mathrm{diag}}$) in `Mat2 B` over ANY
non-commutative ring `[Ring B]`:
1. **Full Entangled Quasi-Projector Decoupling:**
   - Identity channel is 100% in the Left corner: $\Phi_{\mathrm{ent}} P_{\mathrm{left}} \Psi_{\mathrm{ent}} = \Phi_{\mathrm{ent}} \Psi_{\mathrm{ent}}$
     and $\Phi_{\mathrm{ent}} P_{\mathrm{right}} \Psi_{\mathrm{ent}} = 0$.
   - $S_z$-twisted channel is 100% in the Right corner: $\Phi_{\mathrm{ent}} (P_{\mathrm{left}} S_z) \Psi_{\mathrm{ent}} = 0$
     and $\Phi_{\mathrm{ent}} (P_{\mathrm{right}} S_z) \Psi_{\mathrm{ent}} = \Phi_{\mathrm{ent}} \Psi_{\mathrm{ent}}$.
2. **Diagonal Specialization (`archetype_A5_quantum_cheshire_cat_two_state_decoupling`):**
   - $\Phi_{\mathrm{diag}} P_{\mathrm{left}} \Psi_{\mathrm{diag}} = \mathrm{localObs}(2(1 + \sigma_x), 0)$
     and $\Phi_{\mathrm{diag}} P_{\mathrm{right}} \Psi_{\mathrm{diag}} = 0$,
   - $\Phi_{\mathrm{diag}} (P_{\mathrm{left}} S_z) \Psi_{\mathrm{diag}} = 0$ and
     $\Phi_{\mathrm{diag}} (P_{\mathrm{right}} S_z) \Psi_{\mathrm{diag}} = \mathrm{localObs}(0, 2(1 + \sigma_x))$. -/
theorem archetype_G1_entangled_corner_channel_decoupling
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Sz     := diagScalar σz
    let Ψ_e    := PsiEnt σx σz
    let Φ_e    := PhiEnt σx
    let Ψ_d    := PsiDiag σx σz
    let Φ_d    := PhiDiag σx
    let twoPiP := (1 + σx) + (1 + σx)
    Φ_e * P_left * Ψ_e         = Φ_e * Ψ_e ∧
    Φ_e * P_right * Ψ_e        = 0 ∧
    Φ_e * (P_left * Sz) * Ψ_e  = 0 ∧
    Φ_e * (P_right * Sz) * Ψ_e = Φ_e * Ψ_e ∧
    Φ_d * P_left * Ψ_d         = localObs twoPiP 0 ∧
    Φ_d * P_right * Ψ_d        = 0 ∧
    Φ_d * (P_left * Sz) * Ψ_d  = 0 ∧
    Φ_d * (P_right * Sz) * Ψ_d = localObs 0 twoPiP := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hxY := sq_left_of_sq_one hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext <;>
    · dsimp [PsiEnt, PhiEnt, PsiDiag, PhiDiag, P_left, P_right, diagScalar, localObs]
      simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                 zero_a11, zero_a12, zero_a21, zero_a22,
                 mul_add, add_mul, sub_mul, mul_sub,
                 mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
                 mul_assoc, hflip, hflipY, hx, hz, hxY,
                 mul_neg, neg_add_rev, neg_neg]
      try abel

/-- **Archetype $\mathcal{G}_2$ (`archetype_G2_widom_hankel_toeplitz_cancellation_of_joint_product`):**
Resolves why the joint product $P_{\mathrm{left}} (P_{\mathrm{right}} S_z) = 0$ vanishes while both
individual sandwiches equal $\Phi_{\mathrm{ent}} \Psi_{\mathrm{ent}}$:
Splitting across $\Phi_{\mathrm{ent}}$ ($\Phi_{\mathrm{ent}}^2 = 4 \Phi_{\mathrm{ent}}$) and its
complementary quasi-projector $\Phi_{\mathrm{comp}} = 4 \cdot 1 - \Phi_{\mathrm{ent}}$
($\Phi_{\mathrm{comp}}^2 = 4 \Phi_{\mathrm{comp}}$), the non-zero Toeplitz product
$+8(\Phi_{\mathrm{ent}} \Psi_{\mathrm{ent}}) = 16 \begin{pmatrix} \Pi_+ & \Pi_+ \sigma_z \\ \Pi_+ & \Pi_+ \sigma_z \end{pmatrix}$
is identically canceled by the Hankel excursion
$-8(\Phi_{\mathrm{ent}} \Psi_{\mathrm{ent}}) = -16 \begin{pmatrix} \Pi_+ & \Pi_+ \sigma_z \\ \Pi_+ & \Pi_+ \sigma_z \end{pmatrix}$
through the orthogonal complement $\Phi_{\mathrm{comp}}$. -/
theorem archetype_G2_widom_hankel_toeplitz_cancellation_of_joint_product
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Sz       := diagScalar σz
    let Ψ        := PsiEnt σx σz
    let Φ        := PhiEnt σx
    let Φ_comp   := (1 + 1 + 1 + 1 : Mat2 B) - Φ
    let overlap4 := (Φ * Ψ) + (Φ * Ψ) + (Φ * Ψ) + (Φ * Ψ)
    let overlap8 := overlap4 + overlap4
    P_left * (P_right * Sz) = 0 ∧
    (Φ * P_left * Φ) * (Φ * (P_right * Sz) * Ψ) = overlap8 ∧
    (Φ * P_left * Φ_comp) * (Φ_comp * (P_right * Sz) * Ψ) = -overlap8 ∧
    (Φ * P_left * Φ) * (Φ * (P_right * Sz) * Ψ) +
    (Φ * P_left * Φ_comp) * (Φ_comp * (P_right * Sz) * Ψ) = 0 := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hxY := sq_left_of_sq_one hx
  let Sz       := diagScalar σz
  let Ψ        := PsiEnt σx σz
  let Φ        := PhiEnt σx
  let Φ_comp   := (1 + 1 + 1 + 1 : Mat2 B) - Φ
  let overlap4 := (Φ * Ψ) + (Φ * Ψ) + (Φ * Ψ) + (Φ * Ψ)
  let overlap8 := overlap4 + overlap4
  have hToeplitz : (Φ * P_left * Φ) * (Φ * (P_right * Sz) * Ψ) = overlap8 := by
    ext <;>
    · dsimp [Sz, Ψ, Φ, overlap8, overlap4, PsiEnt, PhiEnt, P_left, P_right, diagScalar]
      simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                 add_a11, add_a12, add_a21, add_a22,
                 mul_add, add_mul, mul_sub,
                 mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
                 mul_assoc, hflip, hflipY, hx, hz, hxY,
                 mul_neg, neg_add_rev, neg_neg]
      try abel
  have hHankel : (Φ * P_left * Φ_comp) * (Φ_comp * (P_right * Sz) * Ψ) = -overlap8 := by
    ext <;>
    · dsimp [Sz, Ψ, Φ, Φ_comp, overlap8, overlap4, PsiEnt, PhiEnt, P_left, P_right, diagScalar, one]
      simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                 add_a11, add_a12, add_a21, add_a22,
                 sub_a11, sub_a12, sub_a21, sub_a22,
                 neg_a11, neg_a12, neg_a21, neg_a22,
                 mul_add, add_mul, sub_mul, mul_sub,
                 mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
                 mul_assoc, hflip, hflipY, hx, hz, hxY,
                 mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg]
      try abel
  refine ⟨by simp only [P_left, P_right, diagScalar]; nc_mat2, hToeplitz, hHankel, ?_⟩
  rw [hToeplitz, hHankel, add_neg_cancel]

-- ============================================================================
-- 4. ARCHETYPES R₀, R₁, R₂, R₃, R₄: REPRESENTATION-THEORETIC CONSEQUENCES
--    (MINIMAL IDEAL SPINORS, WALSH–HADAMARD DUALITY & HALMOS TRIGONOMETRY)
-- ============================================================================

/-- Walsh–Hadamard / Cayley transform matrix $H_{\mathrm{W}} = E_z + E_x = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$. -/
@[simp] def H_Walsh : Mat2 B := Ez + Ex

/-- Skew-symmetric off-diagonal Morita transition current $J(W_{12}, W_{21}) = \begin{pmatrix} 0 & W_{12} \\ -W_{21} & 0 \end{pmatrix}$. -/
@[simp] def matJ (W12 W21 : B) : Mat2 B := ⟨0, W12, -W21, 0⟩

/-- Total diagonal Morita holonomy metric $V(W_{12}, W_{21}) = \begin{pmatrix} W_{12} W_{21} & 0 \\ 0 & W_{21} W_{12} \end{pmatrix}$. -/
@[simp] def matV (W12 W21 : B) : Mat2 B := ⟨W12 * W21, 0, 0, W21 * W12⟩

/-- Chiral diagonal Morita dipole $\Sigma(W_{12}, W_{21}) = \begin{pmatrix} W_{12} W_{21} & 0 \\ 0 & -W_{21} W_{12} \end{pmatrix}$. -/
@[simp] def matSig (W12 W21 : B) : Mat2 B := ⟨W12 * W21, 0, 0, -(W21 * W12)⟩

/-- **Archetype $\mathcal{R}_0$ (`archetype_R0_minimal_ideal_spinor_reconstruction_and_corner_homomorphism`):**
1. **Spinor Ideal Reconstruction:** Every operator $M \in \mathrm{Mat}_2(B)$ is reconstructed purely
   from its projections into the single minimal left ideal $\mathrm{Mat}_2(B) P_{\mathrm{left}}$:
   $M = M P_{\mathrm{left}} + (M E_x P_{\mathrm{left}}) E_x$.
2. **Weyl-Conjugated Complementary Corner:** $P_{\mathrm{right}} = E_x P_{\mathrm{left}} E_x$.
3. **Bra-Ket Corner Sandwich:** Pairing a bra $P_{\mathrm{left}} Y$ in the right ideal with a ket
   $X P_{\mathrm{left}}$ in the left ideal lands strictly in the upper-left corner ring
   $P_{\mathrm{left}} \mathrm{Mat}_2(B) P_{\mathrm{left}} \cong B$:
   $(P_{\mathrm{left}} Y) M (X P_{\mathrm{left}}) = \langle (Y M X)_{11}, 0, 0, 0 \rangle$. -/
theorem archetype_R0_minimal_ideal_spinor_reconstruction_and_corner_homomorphism
    (M X Y : Mat2 B) :
    M = M * P_left + (M * Ex * P_left) * Ex ∧
    (P_right : Mat2 B) = Ex * P_left * Ex ∧
    (P_left * Y) * M * (X * P_left) = ⟨(Y * M * X).a11, 0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [P_left, P_right, Ex]; nc_mat2

/-- **Archetype $\mathcal{R}_1$ (`archetype_R1_walsh_hadamard_localization_shift_duality`):**
Proves that diagonal localization ($E_z$, `localObs`) and off-diagonal modular shift ($E_x$, `modularShift`)
are dual Cartan subalgebras intertwined by the Walsh–Hadamard reflection $H_{\mathrm{W}} = E_z + E_x$:
1. $H_{\mathrm{W}}^2 = 2 \cdot 1$.
2. $H_{\mathrm{W}} E_z H_{\mathrm{W}} = 2 E_x$ (conjugates localization $E_z$ into modular shift $E_x$).
3. $H_{\mathrm{W}} E_x H_{\mathrm{W}} = 2 E_z$ (conjugates modular shift $E_x$ into localization $E_z$).
4. $H_{\mathrm{W}} E_y H_{\mathrm{W}} = -2 E_y$ (inverts the symplectic bivector $E_y$).
5. $H_{\mathrm{W}} \, \mathrm{localObs}(d_1, d_2) \, H_{\mathrm{W}} = \mathrm{diagScalar}(d_1 + d_2) + \mathrm{modularShift}(d_1 - d_2, d_1 - d_2)$. -/
theorem archetype_R1_walsh_hadamard_localization_shift_duality
    (d1 d2 : B) :
    (H_Walsh : Mat2 B) * H_Walsh = 1 + 1 ∧
    (H_Walsh : Mat2 B) * Ez * H_Walsh = Ex + Ex ∧
    (H_Walsh : Mat2 B) * Ex * H_Walsh = Ez + Ez ∧
    (H_Walsh : Mat2 B) * Ey * H_Walsh = -(Ey + Ey) ∧
    (H_Walsh : Mat2 B) * localObs d1 d2 * H_Walsh =
      diagScalar (d1 + d2) + modularShift (d1 - d2) (d1 - d2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [H_Walsh, localObs, diagScalar, modularShift, Ex, Ey, Ez]; nc_mat2

/-- Left-associated idempotent absorption $P (P Z) = P Z$ when $P^2 = P$. -/
lemma idem_assoc {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/-- **Archetype $\mathcal{R}_2$ (`archetype_R2_halmos_two_idempotent_trigonometry_and_contextuality`):**
Halmos's Universal Two-Idempotent Theorem in ANY non-commutative associative ring `[Ring B]`:
For any two (generally non-commuting) idempotents $P_1^2 = P_1$ and $P_2^2 = P_2$ in $B$, let
$\Delta_{21} = (P_2 - P_1)^2$ be the Chordal Distance Operator ($\sin^2\theta$) and
$C_{21} = [P_2, P_1]$ be the Contextuality Commutator:
1. **Centrality of the Chordal Distance:** $[\Delta_{21}, P_1] = 0$ and $[\Delta_{21}, P_2] = 0$.
2. **Born Transition Probability Law ($\cos^2\theta = 1 - \sin^2\theta$):**
   $P_1 P_2 P_1 = P_1 (1 - \Delta_{21})$ and $P_2 P_1 P_2 = P_2 (1 - \Delta_{21})$.
3. **Universal Contextuality–Metric Identity ($-[P_2, P_1]^2 = \sin^2\theta \cos^2\theta$):**
   $-(C_{21} C_{21}) = \Delta_{21} (1 - \Delta_{21})$. -/
theorem archetype_R2_halmos_two_idempotent_trigonometry_and_contextuality
    {P1 P2 : B} (hP1 : P1 * P1 = P1) (hP2 : P2 * P2 = P2) :
    let Δ21 := (P2 - P1) * (P2 - P1)
    let C21 := rcomm P2 P1
    rcomm Δ21 P1 = 0 ∧
    rcomm Δ21 P2 = 0 ∧
    P1 * P2 * P1 = P1 * (1 - Δ21) ∧
    P2 * P1 * P2 = P2 * (1 - Δ21) ∧
    -(C21 * C21) = Δ21 * (1 - Δ21) := by
  intro Δ21 C21
  dsimp [Δ21, C21, rcomm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [sub_mul, mul_sub, mul_assoc, hP1, hP2, idem_assoc hP1]; abel
  · simp only [sub_mul, mul_sub, mul_assoc, hP1, hP2, idem_assoc hP2]; abel
  · simp only [sub_mul, mul_sub, mul_one, mul_assoc, hP1, hP2, idem_assoc hP1]; abel
  · simp only [sub_mul, mul_sub, mul_one, mul_assoc, hP1, hP2, idem_assoc hP2]; abel
  · simp only [sub_mul, mul_sub, mul_one, mul_assoc, hP1, hP2, idem_assoc hP1, idem_assoc hP2]; abel

/-- **Lineage $\mathcal{L}_0$ (`lineage_L0_jordan_dixmier_davis_halmos_dihedral_two_idempotent_theorem`):**
Unifies Jordan (1875), Dixmier (1949), Davis (1958), and Halmos (1969) over ANY non-commutative
associative ring `[Ring B]`:
For any two idempotents $P_1^2 = P_1$ and $P_2^2 = P_2$ in $B$, define the difference operator
$D = P_2 - P_1$ ($\sin\theta$) and the Davis reflection operator $\Sigma = P_1 + P_2 - 1$ ($\cos\theta$):
1. **Chiral Factorizations of the Commutator $[P_2, P_1]$:**
   $D \Sigma = [P_2, P_1]$ and $\Sigma D = -[P_2, P_1]$.
2. **Strict Anticommutation:** $\{D, \Sigma\} = 0$ and $[D, \Sigma] = 2[P_2, P_1]$.
3. **Universal Operator Pythagorean Identity ($\sin^2\theta + \cos^2\theta = 1$):**
   $D^2 + \Sigma^2 = 1$.
4. **Exact Subspace Intertwining:**
   $P_1 \Sigma = P_1 P_2$, $\Sigma P_2 = P_1 P_2$, $P_1 \Sigma = \Sigma P_2$, and $D P_1 = (1 - P_2) D$.
5. **Halmos Transition & Contextuality Identities:**
   $P_1 P_2 P_1 = P_1 \Sigma^2 = P_1(1 - D^2)$ and $-[P_2, P_1]^2 = D^2 \Sigma^2 = D^2(1 - D^2)$. -/
theorem lineage_L0_jordan_dixmier_davis_halmos_dihedral_two_idempotent_theorem
    {P1 P2 : B} (hP1 : P1 * P1 = P1) (hP2 : P2 * P2 = P2) :
    let D   := P2 - P1
    let Sig := P1 + P2 - 1
    let C   := rcomm P2 P1
    D * Sig = C ∧
    Sig * D = -C ∧
    racomm D Sig = 0 ∧
    rcomm D Sig  = C + C ∧
    D * D + Sig * Sig = 1 ∧
    P1 * Sig = P1 * P2 ∧
    Sig * P2 = P1 * P2 ∧
    P1 * Sig = Sig * P2 ∧
    D * P1 = (1 - P2) * D ∧
    P1 * P2 * P1 = P1 * (Sig * Sig) ∧
    P1 * P2 * P1 = P1 * (1 - D * D) ∧
    -(C * C)     = (D * D) * (Sig * Sig) ∧
    -(C * C)     = (D * D) * (1 - D * D) := by
  intro D Sig C
  dsimp [D, Sig, C, rcomm, racomm]
  have h1 : (P2 - P1) * (P1 + P2 - 1) = P2 * P1 - P1 * P2 := by
    simp only [sub_mul, mul_sub, mul_add, mul_one, hP1, hP2]; abel
  have h2 : (P1 + P2 - 1) * (P2 - P1) = -(P2 * P1 - P1 * P2) := by
    simp only [sub_mul, mul_sub, add_mul, one_mul, hP1, hP2]; abel
  have h3 : (P2 - P1) * (P1 + P2 - 1) + (P1 + P2 - 1) * (P2 - P1) = 0 := by
    rw [h1, h2, add_neg_cancel]
  have h4 : (P2 - P1) * (P1 + P2 - 1) - (P1 + P2 - 1) * (P2 - P1) =
      (P2 * P1 - P1 * P2) + (P2 * P1 - P1 * P2) := by
    rw [h1, h2, sub_neg_eq_add]
  have h5 : (P2 - P1) * (P2 - P1) + (P1 + P2 - 1) * (P1 + P2 - 1) = 1 := by
    simp only [sub_mul, mul_sub, add_mul, mul_add, mul_one, one_mul, hP1, hP2]; abel
  have h6 : P1 * (P1 + P2 - 1) = P1 * P2 := by
    simp only [mul_sub, mul_add, mul_one, hP1]; abel
  have h7 : (P1 + P2 - 1) * P2 = P1 * P2 := by
    simp only [sub_mul, add_mul, one_mul, hP2]; abel
  have h8 : P1 * (P1 + P2 - 1) = (P1 + P2 - 1) * P2 := by
    rw [h6, h7]
  have h9 : (P2 - P1) * P1 = (1 - P2) * (P2 - P1) := by
    simp only [sub_mul, mul_sub, one_mul, hP1, hP2]; abel
  have hR2 := archetype_R2_halmos_two_idempotent_trigonometry_and_contextuality hP1 hP2
  have h11 : P1 * P2 * P1 = P1 * (1 - (P2 - P1) * (P2 - P1)) := hR2.2.2.1
  have h13 : -((P2 * P1 - P1 * P2) * (P2 * P1 - P1 * P2)) =
      ((P2 - P1) * (P2 - P1)) * (1 - (P2 - P1) * (P2 - P1)) := hR2.2.2.2.2
  have hSigma2 : (P1 + P2 - 1) * (P1 + P2 - 1) = 1 - (P2 - P1) * (P2 - P1) := by
    calc (P1 + P2 - 1) * (P1 + P2 - 1)
      _ = ((P2 - P1) * (P2 - P1) + (P1 + P2 - 1) * (P1 + P2 - 1)) - (P2 - P1) * (P2 - P1) := by abel
      _ = 1 - (P2 - P1) * (P2 - P1) := by rw [h5]
  have h10 : P1 * P2 * P1 = P1 * ((P1 + P2 - 1) * (P1 + P2 - 1)) := by
    rw [hSigma2, h11]
  have h12 : -((P2 * P1 - P1 * P2) * (P2 * P1 - P1 * P2)) =
      ((P2 - P1) * (P2 - P1)) * ((P1 + P2 - 1) * (P1 + P2 - 1)) := by
    rw [hSigma2, h13]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- **Archetypes $\mathcal{R}_3$ & $\mathcal{R}_4$ (`archetype_R3_R4_morita_signature_split_and_entangled_routing`):**
1. **Lorentzian Signature Split from Morita Bimodule Transition $(W_{12}, W_{21})$ ($\mathcal{R}_3$):**
   $\Phi^2 = +V$, $J^2 = -V$, $\{\Phi, J\} = 0$, $[\Phi, J] = -2\Sigma$, and $-[\Phi, [\Phi, J]] = -4 V J$.
2. **Orthogonal Corner Routing of Identity vs. Twisted Observables ($\mathcal{R}_4$):**
   $\Phi_{\mathrm{ent}} P_{\mathrm{left}} \Psi_{\mathrm{ent}} = \Phi_{\mathrm{ent}} (P_{\mathrm{right}} S_z) \Psi_{\mathrm{ent}} = \Phi_{\mathrm{ent}} \Psi_{\mathrm{ent}}$,
   while $\Phi_{\mathrm{ent}} P_{\mathrm{right}} \Psi_{\mathrm{ent}} = 0$ and $\Phi_{\mathrm{ent}} (P_{\mathrm{left}} S_z) \Psi_{\mathrm{ent}} = 0$. -/
theorem archetype_R3_R4_morita_signature_split_and_entangled_routing
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0)
    (W12 W21 : B) :
    let Phi := modularShift W12 W21
    let J   := matJ W12 W21
    let V   := matV W12 W21
    let Sig := matSig W12 W21
    let V4  := V + V + V + V
    let Sz  := diagScalar σz
    let Ψ   := PsiEnt σx σz
    let Φ   := PhiEnt σx
    Phi * Phi = V ∧
    J * J     = -V ∧
    racomm Phi J = 0 ∧
    rcomm Phi J  = -(Sig + Sig) ∧
    -rcomm Phi (rcomm Phi J) = -(V4 * J) ∧
    Φ * P_left * Ψ         = Φ * Ψ ∧
    Φ * P_right * Ψ        = 0 ∧
    Φ * (P_left * Sz) * Ψ  = 0 ∧
    Φ * (P_right * Sz) * Ψ = Φ * Ψ := by
  have hG1 := archetype_G1_entangled_corner_channel_decoupling hx hz hxz
  refine ⟨by simp only [modularShift, matV]; nc_mat2,
          by simp only [matJ, matV]; nc_mat2,
          by simp only [modularShift, matJ, racomm]; nc_mat2,
          by simp only [modularShift, matJ, matSig, rcomm]; nc_mat2,
          by simp only [modularShift, matJ, matV, rcomm]; nc_mat2,
          hG1.1, hG1.2.1, hG1.2.2.1, hG1.2.2.2.1⟩

/-- **Lineage $\mathcal{L}_4$ (`lineage_L4_widom_kirkwood_dirac_aharonov_toeplitz_hankel_decoupling`):**
Unifies Kirkwood (1933), Dirac (1945), Widom (1976), and Aharonov–Albert–Vaidman (1988/2013):
1. Kirkwood–Dirac trace marginalization: $\operatorname{tr}_2(P_2 M P_1) + \operatorname{tr}_2((1 - P_2) M P_1) = \operatorname{tr}_2(M P_1)$.
2. Entangled corner routing of $1$ vs. $S_z$:
   $\Phi_{\mathrm{ent}} P_{\mathrm{left}} \Psi_{\mathrm{ent}} = \Phi_{\mathrm{ent}} (P_{\mathrm{right}} S_z) \Psi_{\mathrm{ent}} = \Phi_{\mathrm{ent}} \Psi_{\mathrm{ent}}$,
   while $\Phi_{\mathrm{ent}} P_{\mathrm{right}} \Psi_{\mathrm{ent}} = 0$ and $\Phi_{\mathrm{ent}} (P_{\mathrm{left}} S_z) \Psi_{\mathrm{ent}} = 0$.
3. Widom Toeplitz–Hankel cancellation of the joint product $P_{\mathrm{left}} (P_{\mathrm{right}} S_z) = 0$
   across $\Phi_{\mathrm{ent}}$ and $\Phi_{\mathrm{comp}} = 4 \cdot 1 - \Phi_{\mathrm{ent}}$. -/
theorem lineage_L4_widom_kirkwood_dirac_aharonov_toeplitz_hankel_decoupling
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0)
    (P2 P1 M : Mat2 B) :
    let Sz     := diagScalar σz
    let Ψ      := PsiEnt σx σz
    let Φ      := PhiEnt σx
    let Φ_comp := (1 + 1 + 1 + 1 : Mat2 B) - Φ
    tr2 (P2 * M * P1) + tr2 ((1 - P2) * M * P1) = tr2 (M * P1) ∧
    Φ * P_left * Ψ         = Φ * Ψ ∧
    Φ * P_right * Ψ        = 0 ∧
    Φ * (P_left * Sz) * Ψ  = 0 ∧
    Φ * (P_right * Sz) * Ψ = Φ * Ψ ∧
    (Φ * P_left * Φ) * (Φ * (P_right * Sz) * Ψ) +
    (Φ * P_left * Φ_comp) * (Φ_comp * (P_right * Sz) * Ψ) = 0 := by
  have hG1 := archetype_G1_entangled_corner_channel_decoupling hx hz hxz
  have hG2 := archetype_G2_widom_hankel_toeplitz_cancellation_of_joint_product hx hz hxz
  have hKD : tr2 (P2 * M * P1) + tr2 ((1 - P2) * M * P1) = tr2 (M * P1) := by
    simp only [tr2]; nc_mat2
  exact ⟨hKD, hG1.1, hG1.2.1, hG1.2.2.1, hG1.2.2.2.1, hG2.2.2.2⟩

-- ============================================================================
-- 5. THE THREE-IDEMPOTENT BARGMANN–WIDOM–NAMBU CALCULUS N₀ ≺ N₁ ≺ N₂ ≺ N₃ ≺ N₄
-- ============================================================================

/-- Davis reflection operator `Σ_{ij} = P_i + P_j - 1` (`cos θ_{ij}`). -/
@[simp] def davisSigma {A : Type u} [Ring A] (Pi Pj : A) : A := Pi + Pj - 1

/-- Chordal difference operator `D_{ij} = P_i - P_j` (`sin θ_{ij}`). -/
@[simp] def davisDiff {A : Type u} [Ring A] (Pi Pj : A) : A := Pi - Pj

/-- Cartan involution `S_i = 2 P_i - 1 = P_i - (1 - P_i)`. -/
@[simp] def cartanS {A : Type u} [Ring A] (Pi : A) : A := Pi + Pi - 1

/-- 3-step Bargmann–Davis reflection holonomy `B_{123} = Σ₁₂ * Σ₂₃ * Σ₃₁`. -/
@[simp] def bargmannHolonomy {A : Type u} [Ring A] (P1 P2 P3 : A) : A :=
  davisSigma P1 P2 * davisSigma P2 P3 * davisSigma P3 P1

/-- Yoichiro Nambu's ternary bracket `[X₁, X₂, X₃]_Nambu = ∑_{σ ∈ S₃} sgn(σ) X_{σ(1)} X_{σ(2)} X_{σ(3)}`. -/
@[simp] def nambu3 {A : Type u} [Ring A] (X1 X2 X3 : A) : A :=
  (X1 * X2 * X3 + X2 * X3 * X1 + X3 * X1 * X2) -
  (X1 * X3 * X2 + X2 * X1 * X3 + X3 * X2 * X1)

macro "idem3_calc" h1:term "," h2:term "," h3:term : tactic =>
  `(tactic| (
    (try simp only [mul_add, add_mul, sub_mul, mul_sub,
                    mul_one, one_mul, mul_zero, zero_mul,
                    neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg,
                    mul_assoc, $h1:term, $h2:term, $h3:term,
                    idem_assoc $h1, idem_assoc $h2, idem_assoc $h3])
    abel))

/-- **Archetype $\mathcal{N}_0$ (`archetype_N0_operator_double_angle_euler_identities`):**
For ANY two idempotents `P₁² = P₁` and `P₂² = P₂` in ANY non-commutative ring `[Ring B]`:
1. `S₁ = Σ₁₂ + D₁₂` and `S₂ = Σ₁₂ - D₁₂`, with `S₁² = 1` and `S₂² = 1`.
2. **Operator Euler Double-Angle Identity (`e^{2iθ} = cos(2θ) + i sin(2θ)`):**
   `S₁ * S₂ = (Σ₁₂² - D₁₂²) + 2 • (D₁₂ * Σ₁₂) = (1 - 2 • D₁₂²) + 2 • [P₁, P₂]`.
3. **Symmetric `cos(2θ)` and Skew `sin(2θ)` Projections:**
   `{S₁, S₂} = 2 • (1 - 2 • D₁₂²)` and `[S₁, S₂] = 4 • [P₁, P₂]`. -/
theorem archetype_N0_operator_double_angle_euler_identities
    {P1 P2 : B} (hP1 : P1 * P1 = P1) (hP2 : P2 * P2 = P2) :
    let Sig12 := davisSigma P1 P2
    let D12   := davisDiff P1 P2
    let S1    := cartanS P1
    let S2    := cartanS P2
    let C12   := rcomm P1 P2
    S1 = Sig12 + D12 ∧
    S2 = Sig12 - D12 ∧
    S1 * S1 = 1 ∧
    S2 * S2 = 1 ∧
    S1 * S2 = (Sig12 * Sig12 - D12 * D12) + (D12 * Sig12 + D12 * Sig12) ∧
    S1 * S2 = (1 - (D12 * D12 + D12 * D12)) + (C12 + C12) ∧
    racomm S1 S2 = (1 - (D12 * D12 + D12 * D12)) + (1 - (D12 * D12 + D12 * D12)) ∧
    rcomm S1 S2  = C12 + C12 + C12 + C12 := by
  intro Sig12 D12 S1 S2 C12
  dsimp [Sig12, D12, S1, S2, C12, davisSigma, davisDiff, cartanS, rcomm, racomm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> idem3_calc hP1, hP2, hP2

/-- **Archetype $\mathcal{N}_1$ (`archetype_N1_two_step_davis_reflection_and_widom_hankel_split`):**
For ANY three idempotents `P₁² = P₁, P₂² = P₂, P₃² = P₃` in `[Ring B]`:
1. **Orthogonal Consciousness/Shadow Channel Splitting:**
   `Σ₁₂ * Σ₂₃ = P₁ * P₂ * P₃ + (1 - P₁) * (1 - P₂) * (1 - P₃)` (zero cross-channel mixing).
2. **Widom Toeplitz vs. Hankel Path Projection:**
   - `P₁ * (Σ₁₂ * Σ₂₃) * P₃ = P₁ * P₂ * P₃` (pure Toeplitz path through `P₂`),
   - `P₁ * (Σ₁₃ - Σ₁₂ * Σ₂₃) * P₃ = P₁ * (1 - P₂) * P₃` (pure Hankel excursion through `1 - P₂`). -/
theorem archetype_N1_two_step_davis_reflection_and_widom_hankel_split
    {P1 P2 P3 : B} (hP1 : P1 * P1 = P1) (hP2 : P2 * P2 = P2) (hP3 : P3 * P3 = P3) :
    let Sig12 := davisSigma P1 P2
    let Sig23 := davisSigma P2 P3
    let Sig13 := davisSigma P1 P3
    Sig12 * Sig23 = P1 * P2 * P3 + (1 - P1) * (1 - P2) * (1 - P3) ∧
    P1 * (Sig12 * Sig23) * P3 = P1 * P2 * P3 ∧
    P1 * (Sig13 - Sig12 * Sig23) * P3 = P1 * (1 - P2) * P3 := by
  intro Sig12 Sig23 Sig13
  dsimp [Sig12, Sig23, Sig13, davisSigma]
  refine ⟨?_, ?_, ?_⟩ <;> idem3_calc hP1, hP2, hP3

/-- **Archetype $\mathcal{N}_2$ (`archetype_N2_three_step_bargmann_holonomy_and_linear_reduction`):**
For ANY three idempotents `P₁² = P₁, P₂² = P₂, P₃² = P₃` in `[Ring B]`:
1. **Conscious-Minus-Shadow Loop Decomposition:**
   `B₁₂₃ = Σ₁₂ * Σ₂₃ * Σ₃₁ = P₁ P₂ P₃ P₁ - (1 - P₁)(1 - P₂)(1 - P₃)(1 - P₁)`.
2. **Exact Centrality at the Base Vertex `P₁`:**
   `[B₁₂₃, P₁] = 0` and `P₁ * B₁₂₃ = P₁ * P₂ * P₃ * P₁`.
3. **Cancellation of 4th-Degree Terms in the Orientation Curvature `B₁₂₃ - B₁₃₂`:**
   `B₁₂₃ - B₁₃₂ = P₁ * [P₂, P₃] * P₁ - (1 - P₁) * [P₂, P₃] * (1 - P₁) = {P₁, [P₂, P₃]} - [P₂, P₃]`. -/
theorem archetype_N2_three_step_bargmann_holonomy_and_linear_reduction
    {P1 P2 P3 : B} (hP1 : P1 * P1 = P1) (hP2 : P2 * P2 = P2) (hP3 : P3 * P3 = P3) :
    let B123 := bargmannHolonomy P1 P2 P3
    let B132 := bargmannHolonomy P1 P3 P2
    B123 = P1 * P2 * P3 * P1 - (1 - P1) * (1 - P2) * (1 - P3) * (1 - P1) ∧
    rcomm B123 P1 = 0 ∧
    P1 * B123 = P1 * P2 * P3 * P1 ∧
    B123 - B132 = P1 * rcomm P2 P3 * P1 - (1 - P1) * rcomm P2 P3 * (1 - P1) ∧
    B123 - B132 = racomm P1 (rcomm P2 P3) - rcomm P2 P3 := by
  intro B123 B132
  dsimp [B123, B132, bargmannHolonomy, davisSigma, rcomm, racomm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> idem3_calc hP1, hP2, hP3

/-- **Archetype $\mathcal{N}_3$ (`archetype_N3_bargmann_nambu_ternary_curvature_theorem`):**
**The Bargmann–Nambu Theorem:**
For ANY three idempotents `P₁² = P₁, P₂² = P₂, P₃² = P₃` in ANY non-commutative ring `[Ring B]`:
1. The boundary commutator sum `[P₁, P₂] + [P₂, P₃] + [P₃, P₁]` equals the chordal difference
   commutator `[D₁₂, D₂₃] = [P₁ - P₂, P₂ - P₃]`.
2. Summing the Bargmann orientation curvature `B_{ijk} - B_{ikj}` cyclically over all three
   vertices `(1, 2, 3) + (2, 3, 1) + (3, 1, 2)` yields twice **Yoichiro Nambu's Ternary Bracket**
   `2 • [P₁, P₂, P₃]_Nambu` minus the boundary commutator sum `[D₁₂, D₂₃]`:
   `(B₁₂₃ - B₁₃₂) + (B₂₃₁ - B₂₁₃) + (B₃₁₂ - B₃₂₁) + [D₁₂, D₂₃] = 2 • [P₁, P₂, P₃]_Nambu`. -/
theorem archetype_N3_bargmann_nambu_ternary_curvature_theorem
    {P1 P2 P3 : B} (hP1 : P1 * P1 = P1) (hP2 : P2 * P2 = P2) (hP3 : P3 * P3 = P3) :
    let Om1  := bargmannHolonomy P1 P2 P3 - bargmannHolonomy P1 P3 P2
    let Om2  := bargmannHolonomy P2 P3 P1 - bargmannHolonomy P2 P1 P3
    let Om3  := bargmannHolonomy P3 P1 P2 - bargmannHolonomy P3 P2 P1
    let D12  := davisDiff P1 P2
    let D23  := davisDiff P2 P3
    let N123 := nambu3 P1 P2 P3
    rcomm P1 P2 + rcomm P2 P3 + rcomm P3 P1 = rcomm D12 D23 ∧
    (Om1 + Om2 + Om3) + rcomm D12 D23 = N123 + N123 := by
  intro Om1 Om2 Om3 D12 D23 N123
  dsimp [Om1, Om2, Om3, D12, D23, N123, bargmannHolonomy, davisSigma, davisDiff, nambu3, rcomm]
  refine ⟨?_, ?_⟩ <;> idem3_calc hP1, hP2, hP3

/-- Vertex 1 idempotent `idem1 = [[1, 0], [0, 0]]` in `Mat2 B`. -/
@[simp] def idem1 : Mat2 B := ⟨1, 0, 0, 0⟩

/-- Vertex 2 shear idempotent `idem2(a) = [[1, a], [0, 0]]` in `Mat2 B`. -/
@[simp] def idem2 (a : B) : Mat2 B := ⟨1, a, 0, 0⟩

/-- Vertex 3 opposite-shear idempotent `idem3(c) = [[0, 0], [c, 1]]` in `Mat2 B`. -/
@[simp] def idem3 (c : B) : Mat2 B := ⟨0, 0, c, 1⟩

/-- **Archetype $\mathcal{N}_4$ (`archetype_N4_idempotent_triangle_generates_bimetric_dipole`):**
Over ANY non-commutative ring `[Ring B]` and ANY `a, c ∈ B`:
1. `idem1`, `idem2 a`, and `idem3 c` are exact idempotents in `Mat2 B` (requiring no division by 2).
2. Clockwise 3-reflection Bargmann holonomy `B₁₂₃ = localObs (a * c) 0` and counterclockwise
   holonomy `B₁₃₂ = localObs 0 (-(c * a))`.
3. **Symmetric Sum IS the Bimetric Dipole `matSig a c` and Orientation Difference IS `matV a c`:**
   `B₁₂₃ + B₁₃₂ = matSig a c = [[a c, 0], [0, -c a]]` and
   `B₁₂₃ - B₁₃₂ = matV a c = [[a c, 0], [0, c a]]`.
4. **Nambu 3-Bracket of the Idempotent Triangle:**
   `nambu3 idem1 (idem2 a) (idem3 c) = ⟨a * c + a * c, a, 0, c * a⟩`. -/
theorem archetype_N4_idempotent_triangle_generates_bimetric_dipole (a c : B) :
    let P1 := (idem1 : Mat2 B)
    let P2 := idem2 a
    let P3 := idem3 c
    P1 * P1 = P1 ∧
    P2 * P2 = P2 ∧
    P3 * P3 = P3 ∧
    bargmannHolonomy P1 P2 P3 = localObs (a * c) 0 ∧
    bargmannHolonomy P1 P3 P2 = localObs 0 (-(c * a)) ∧
    bargmannHolonomy P1 P2 P3 + bargmannHolonomy P1 P3 P2 = matSig a c ∧
    bargmannHolonomy P1 P2 P3 - bargmannHolonomy P1 P3 P2 = matV a c ∧
    nambu3 P1 P2 P3 = ⟨a * c + a * c, a, 0, c * a⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [bargmannHolonomy, davisSigma, nambu3, idem1, idem2, idem3, localObs, matSig, matV]
    nc_mat2

-- ============================================================================
-- 6. CHIRAL MODULAR GENESIS, BOHM MASS–SPIN TRANSDUCTION & CHIRAL GAUGE VALVE
--    (C₀ ≺ C₁ ≺ C₂ ≺ C₃ ≺ C₄)
-- ============================================================================

/-- Upper chiral nilpotent `N_+(σz) = [[0, σz], [0, 0]]` in `Mat2 B`. -/
@[simp] def chiralNPlus (σz : B) : Mat2 B := ⟨0, σz, 0, 0⟩

/-- Lower chiral nilpotent `N_- = [[0, 0], [1, 0]]` in `Mat2 B`. -/
@[simp] def chiralNMinus : Mat2 B := ⟨0, 0, 1, 0⟩

/-- Chiral modular shift `Φ_c(σz) = modularShift σz 1 = [[0, σz], [1, 0]]` in `Mat2 B`. -/
@[simp] def chiralPhi (σz : B) : Mat2 B := modularShift σz 1

/-- Inter-sheet spin dipole `D_spin(σz) = (P_left - P_right) * diagScalar σz = [[σz, 0], [0, -σz]]`. -/
@[simp] def spinDipole (σz : B) : Mat2 B := ⟨σz, 0, 0, -σz⟩

/-- Bohm double-commutator curvature `bohmCurvature(Φ, Z) = -[Φ, [Φ, Z]]` in `Mat2 B`. -/
@[simp] def bohmCurvature (Φ Z : Mat2 B) : Mat2 B := -rcomm Φ (rcomm Φ Z)

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{C}_0$ (`archetype_C0_chiral_modular_shift_bimetric_spin_identity`):**
For ANY involution `σz * σz = 1` in `[Ring B]`:
1. Upper bimetric sheet metric `Q_+ = N_+ * N_- = P_left * Sz` (Left-arm spin operator).
2. Lower bimetric sheet metric `Q_- = N_- * N_+ = P_right * Sz` (Right-arm spin operator).
3. Bimetric dipole `Q_+ - Q_- = spinDipole σz` (inter-arm spin dipole).
4. Total bimetric metric `Φ_c² = Q_+ + Q_- = Sz` (global spin operator), with `Φ_c⁴ = 1`. -/
theorem archetype_C0_chiral_modular_shift_bimetric_spin_identity
    {σz : B} (hz : σz * σz = 1) :
    let Np := chiralNPlus σz
    let Nm := chiralNMinus (B := B)
    let Φc := chiralPhi σz
    let Sz := diagScalar σz
    Np * Nm = P_left * Sz ∧
    Nm * Np = P_right * Sz ∧
    Np * Nm - Nm * Np = spinDipole σz ∧
    Φc * Φc = Sz ∧
    (Φc * Φc) * (Φc * Φc) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [chiralNPlus, chiralNMinus, P_left, diagScalar]; nc_mat2
  · dsimp only [chiralNPlus, chiralNMinus, P_right, diagScalar]; nc_mat2
  · dsimp only [chiralNPlus, chiralNMinus, spinDipole]; nc_mat2
  · dsimp only [chiralPhi, modularShift, diagScalar]; nc_mat2
  · dsimp only [chiralPhi, modularShift]
    ext <;>
    · simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                 one_a11, one_a12, one_a21, one_a22,
                 mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, hz]

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{C}_1$ (`archetype_C1_cheshire_cat_chiral_intertwiner_genesis`):**
For ANY `σx, σz ∈ B` with `σz * σz = 1` and `racomm σx σz = 0`:
1. **Diagonal Cheshire Cat Intertwiner:**
   `Φ_c * Ψ_diag * Ex = Φ_diag` and `Sz * Φ_c * Φ_diag * Ex = Ψ_diag`.
2. **Full 2×2 Entangled Quasi-Projector Similarity Conjugation:**
   With `Φ_c⁻¹ = Ex * Φ_c * Ex = modularShift 1 σz` (`Φ_c * Φ_c⁻¹ = 1`),
   `Φ_c * Ψ_ent * (Ex * Φ_c * Ex) = Φ_ent` and `(Ex * Φ_c * Ex) * Φ_ent * Φ_c = Ψ_ent`. -/
theorem archetype_C1_cheshire_cat_chiral_intertwiner_genesis
    {σx σz : B} (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Φc     := chiralPhi σz
    let Φc_inv := Ex * Φc * Ex
    let Sz     := diagScalar σz
    let Ψ_d    := PsiDiag σx σz
    let Φ_d    := PhiDiag σx
    let Ψ_e    := PsiEnt σx σz
    let Φ_e    := PhiEnt σx
    Φc * Φc_inv = 1 ∧
    Φc * Ψ_d * Ex = Φ_d ∧
    Sz * Φc * Φ_d * Ex = Ψ_d ∧
    Φc * Ψ_e * Φc_inv = Φ_e ∧
    Φc_inv * Φ_e * Φc = Ψ_e := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hzY := sq_left_of_sq_one hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext <;>
    · dsimp only [chiralPhi, modularShift, Ex, diagScalar, PsiDiag, PhiDiag, PsiEnt, PhiEnt, localObs]
      simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                 one_a11, one_a12, one_a21, one_a22,
                 mul_add, add_mul, sub_mul, mul_sub,
                 mul_zero, zero_mul, mul_one, one_mul,
                 add_zero, zero_add, sub_zero, zero_sub,
                 neg_mul, mul_neg, neg_neg, mul_assoc,
                 hflip, hflipY, hz, hzY]
      try abel

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{C}_2$ (`archetype_C2_bohm_curvature_transduces_mass_and_spin_dipoles`):**
Under the chiral modular shift `Φ_c(σz) = [[0, σz], [1, 0]]` with `σz * σz = 1`:
1. The Bohm double-commutator curvature `-[Φ_c, [Φ_c, D_mass]]` of the mass dipole
   `D_mass = Ez = P_left - P_right` equals `-4 • D_spin(σz)`.
2. The Bohm double-commutator curvature `-[Φ_c, [Φ_c, D_spin(σz)]]` of the spin dipole
   equals `-4 • D_mass`.
3. The 4th-order Bohm bi-curvature satisfies the eigenvalue identity
   `[Φ_c, [Φ_c, [Φ_c, [Φ_c, D_mass]]]] = 16 • D_mass`. -/
theorem archetype_C2_bohm_curvature_transduces_mass_and_spin_dipoles
    {σz : B} (hz : σz * σz = 1) :
    let Φc   := chiralPhi σz
    let Dm   := (Ez : Mat2 B)
    let Ds   := spinDipole σz
    let Ds4  := (Ds + Ds) + (Ds + Ds)
    let Dm4  := (Dm + Dm) + (Dm + Dm)
    let Dm16 := (Dm4 + Dm4) + (Dm4 + Dm4)
    bohmCurvature Φc Dm = -Ds4 ∧
    bohmCurvature Φc Ds = -Dm4 ∧
    bohmCurvature Φc (bohmCurvature Φc Dm) = Dm16 := by
  have hzY := sq_left_of_sq_one hz
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext <;>
    · dsimp only [bohmCurvature, rcomm, chiralPhi, modularShift, Ez, spinDipole]
      simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                 add_a11, add_a12, add_a21, add_a22,
                 sub_a11, sub_a12, sub_a21, sub_a22,
                 neg_a11, neg_a12, neg_a21, neg_a22,
                 mul_add, add_mul, sub_mul, mul_sub,
                 mul_zero, zero_mul, mul_one, one_mul,
                 add_zero, zero_add, sub_zero, zero_sub,
                 neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                 mul_assoc, hz, hzY]
      try abel

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{C}_3$ (`archetype_C3_cheshire_cat_chiral_modular_valve`):**
**The Non-Reciprocal Chiral Cheshire Cat Gauge Valve:**
For ANY `σx, σz, w ∈ B` with `σx² = 1, σz² = 1, {σx, σz} = 0`, and `[w, σx] = 0`:
1. **Parity-Even (Scalar) Shift `T_even = modularShift w w`:**
   Inside `Φ_diag * T_even * Ψ_diag`, the Right `→` Left `(1,2)` channel is blocked (`= 0`),
   while the Left `→` Right `(2,1)` channel conducts `2 • (w * (1 + σx))`.
2. **Parity-Odd (Spin-Active) Shift `T_odd = modularShift (w * σz) (w * σz)`:**
   Inside `Φ_diag * T_odd * Ψ_diag`, the Left `→` Right `(2,1)` channel is blocked (`= 0`),
   while the Right `→` Left `(1,2)` channel conducts `2 • (w * (1 + σx))`. -/
theorem archetype_C3_cheshire_cat_chiral_modular_valve
    {σx σz w : B} (hx : σx * σx = 1) (hz : σz * σz = 1)
    (hxz : racomm σx σz = 0) (hw : rcomm w σx = 0) :
    let Ψ      := PsiDiag σx σz
    let Φ      := PhiDiag σx
    let Teven  := modularShift w w
    let Todd   := modularShift (w * σz) (w * σz)
    let wP     := w * (1 + σx)
    let twoWP  := wP + wP
    Φ * Teven * Ψ = modularShift 0 twoWP ∧
    Φ * Todd * Ψ  = modularShift twoWP 0 := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hxY := sq_left_of_sq_one hx
  have hzY := sq_left_of_sq_one hz
  have hw_flip : σx * w = w * σx := (sub_eq_zero.mp hw).symm
  have hw_flipY (Y : B) : σx * (w * Y) = w * (σx * Y) := by
    rw [← mul_assoc, hw_flip, mul_assoc]
  refine ⟨?_, ?_⟩ <;>
  · ext <;>
    · dsimp only [PsiDiag, PhiDiag, localObs, modularShift]
      simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                 add_a11, add_a12, add_a21, add_a22,
                 mul_add, add_mul, sub_mul, mul_sub,
                 mul_zero, zero_mul, mul_one, one_mul,
                 add_zero, zero_add, sub_zero, zero_sub,
                 neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                 mul_assoc, hflip, hflipY, hx, hxY, hz, hzY, hw_flip, hw_flipY]
      try abel

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{C}_4$ (`archetype_C4_cheshire_cat_sheet_exchange_swaps_cat_and_grin`):**
Conjugating `Ψ_diag` by `Ex` (`Ψ_swap = Ex * Ψ_diag * Ex`) swaps the spatial localization of
particle presence and spin `Sz` between the Left and Right arms:
1. `Φ_diag * P_left * Ψ_swap = 0` and `Φ_diag * P_right * Ψ_swap = localObs 0 (2(1 + σx))`.
2. `Φ_diag * (P_left * Sz) * Ψ_swap = localObs (2(1 + σx)) 0` and `Φ_diag * (P_right * Sz) * Ψ_swap = 0`. -/
theorem archetype_C4_cheshire_cat_sheet_exchange_swaps_cat_and_grin
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Ψswap  := Ex * PsiDiag σx σz * Ex
    let Φ      := PhiDiag σx
    let Sz     := diagScalar σz
    let twoPiP := (1 + σx) + (1 + σx)
    Φ * P_left * Ψswap         = 0 ∧
    Φ * P_right * Ψswap        = localObs 0 twoPiP ∧
    Φ * (P_left * Sz) * Ψswap  = localObs twoPiP 0 ∧
    Φ * (P_right * Sz) * Ψswap = 0 := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hxY := sq_left_of_sq_one hx
  have hzY := sq_left_of_sq_one hz
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext <;>
    · dsimp only [Ex, PsiDiag, PhiDiag, P_left, P_right, diagScalar, localObs]
      simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                 zero_a11, zero_a12, zero_a21, zero_a22,
                 mul_add, add_mul, sub_mul, mul_sub,
                 mul_zero, zero_mul, mul_one, one_mul,
                 add_zero, zero_add, sub_zero, zero_sub,
                 neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                 mul_assoc, hflip, hflipY, hx, hxY, hz, hzY]
      try abel

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{C}_5$ (`archetype_C5_cheshire_cat_bargmann_berry_holonomy_generates_spin_dipole_and_grin`):**
**The 3-Idempotent Bargmann–Berry Phase of the Quantum Cheshire Cat ($\mathcal{N}_0\text{–}\mathcal{N}_4 \bowtie \mathcal{C}_0\text{–}\mathcal{C}_4$):**
For ANY `σx, σz ∈ B` with `σx * σx = 1`, `σz * σz = 1`, and `racomm σx σz = 0`, consider the
division-free 3-idempotent triangle `P1 = idem1 = P_left`, `P2 = idem2 σz = [[1, σz], [0, 0]]`,
and `P3 = idem3 1 = [[0, 0], [1, 1]]`:
1. `(P2 - P1) + (P3 - P_right) = chiralPhi σz`.
2. `bargmannHolonomy P1 P2 P3 = P_left * diagScalar σz` and `bargmannHolonomy P1 P3 P2 = -(P_right * diagScalar σz)`.
3. `bargmannHolonomy P1 P2 P3 + bargmannHolonomy P1 P3 P2 = spinDipole σz` and
   `bargmannHolonomy P1 P2 P3 - bargmannHolonomy P1 P3 P2 = diagScalar σz`.
4. `PhiDiag σx * bargmannHolonomy P1 P2 P3 * PsiDiag σx σz = 0` and
   `PhiDiag σx * (-bargmannHolonomy P1 P3 P2) * PsiDiag σx σz = localObs 0 (2(1 + σx))`. -/
theorem archetype_C5_cheshire_cat_bargmann_berry_holonomy_generates_spin_dipole_and_grin
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let P1    := idem1 (B := B)
    let P2    := idem2 σz
    let P3    := idem3 (1 : B)
    let B123  := bargmannHolonomy P1 P2 P3
    let B132  := bargmannHolonomy P1 P3 P2
    let Sz    := diagScalar σz
    let Φ_d   := PhiDiag σx
    let Ψ_d   := PsiDiag σx σz
    let twoP  := (1 + σx) + (1 + σx)
    (P2 - P1) + (P3 - P_right) = chiralPhi σz ∧
    B123 = P_left * Sz ∧
    B132 = -(P_right * Sz) ∧
    B123 + B132 = spinDipole σz ∧
    B123 - B132 = Sz ∧
    Φ_d * B123 * Ψ_d = 0 ∧
    Φ_d * (-B132) * Ψ_d = localObs 0 twoP := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hxY := sq_left_of_sq_one hx
  have hzY := sq_left_of_sq_one hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext <;>
    · dsimp only [idem1, idem2, idem3, bargmannHolonomy, davisSigma,
                  P_left, P_right, chiralPhi, modularShift, diagScalar, spinDipole,
                  PhiDiag, PsiDiag, localObs]
      simp only [zero_a11, zero_a12, zero_a21, zero_a22,
                 one_a11, one_a12, one_a21, one_a22,
                 add_a11, add_a12, add_a21, add_a22,
                 neg_a11, neg_a12, neg_a21, neg_a22,
                 sub_a11, sub_a12, sub_a21, sub_a22,
                 mul_a11, mul_a12, mul_a21, mul_a22,
                 mul_add, add_mul, sub_mul, mul_sub,
                 mul_zero, zero_mul, mul_one, one_mul,
                 add_zero, zero_add, sub_zero, zero_sub,
                 neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                 mul_assoc, hflip, hflipY, hx, hxY, hz, hzY]
      try abel

/-- **Archetype C₆ (full entangled boundary link readout).**
For arbitrary block entries `u` and `v`, without a commutativity assumption,
this computes the full matrix sandwich between the entangled boundary
operators. The products retain their order, so this identity does not infer a
channel vanishing from the separate diagonal-boundary valve theorem.
-/
theorem archetype_C6_entangled_boundary_link_readout (x z u v : B) :
    let q := 1 + x
    let m := 1 - x
    PhiEnt x * modularShift u v * PsiEnt x z =
      ⟨q * v * q + q * u * z * q,
        q * v * q * z + q * u * m,
        q * v * q + q * u * z * q,
        q * v * q * z + q * u * m⟩ := by
  dsimp only [PhiEnt, PsiEnt, modularShift]
  ext <;> simp [mul_a11, mul_a12, mul_a21, mul_a22, mul_assoc] <;> abel

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
