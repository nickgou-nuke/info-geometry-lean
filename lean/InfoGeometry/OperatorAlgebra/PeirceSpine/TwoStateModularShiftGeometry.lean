/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Formalization Team
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.PeirceSpine.BimetricSheetGeometry
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich

/-!
# Two-State Sandwich Algebras, Weak-Value Amplification & Non-Local Weyl Shift Commutators (A₀ ≺ ... ≺ A₄)

Formalized in Lean 4 (`Mathlib`) over an arbitrary **non-commutative** associative ring `[Ring B]`.
Zero `sorry`s. Zero custom axioms. Zero commutativity assumptions on `B`.

## Three-Bucket Audit Map
- **BUCKET 1 (Established Mathematical Target & Existing Owners)**:
  * `Mathlib.Algebra.Ring.Defs`, `Mathlib.Tactic.Abel`.
  * `InfoGeometry.OperatorAlgebra.PeirceSpine.BimetricSheetGeometry`:
    Non-commutative 2×2 block matrices `Mat2 B`, off-diagonal bridge `matPhi`, and corner
    metric `matV`.
  * `InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich`:
    Ordered two-chart Peirce sandwiches `(P - N₊) * X * (P + N₋)`.
- **BUCKET 2 (Deconfabulation & Translation Dictionary)**:
  * Strips physical narrative from Yakir Aharonov's two-state vector and modular variable
    formalism and replaces wave-function collapse / scalar weak-value prose with exact
    ring-level operator identities over `[Ring B]`:
    - Pre- and post-selected two-state transition (00:13:51–00:21:36, 00:34:20–00:39:44)
      $\mapsto$ bilateral two-idempotent sandwich `twoStateSandwich P2 P1 A = P2 * A * P1`
      and Fubini–Study transition core `(P2 * P1)^2 = P2 * (P1 * P2 * P1) * P1`.
    - Spin-1/2 anomalous weak-value amplification $\frac{\sigma_x + \sigma_y}{\sqrt{2}} \to \sqrt{2}$
      (00:22:24–00:29:58) $\mapsto$ Clifford anticommutator sandwich identity showing that
      while $(\sigma_x + \sigma_y)^2 = 2 \cdot 1$, the bilateral sandwich between
      $P_y = 1 + \sigma_y$ and $P_x = 1 + \sigma_x$ satisfies
      $P_y (\sigma_x + \sigma_y) P_x = 2 P_y P_x$ and $P_y (\sigma_x - \sigma_y) P_x = 0$.
    - Vanishing of polynomial moments $\langle x^m p^n \rangle$ vs. modular momentum
      $e^{i p L / \hbar}$ phase sensitivity (00:40:40–00:45:28) $\mapsto$ block-diagonal
      trace blindness $\operatorname{tr}_2(\rho D_{\text{loc}}^n) = d_1 f_1^n + d_2 f_2^n$
      vs. off-diagonal Weyl shift phase extraction
      $\operatorname{tr}_2(\rho T_L) = u_+ \tau_- + u_- \tau_+$.
    - Non-local Heisenberg equation $[e^{i p L / \hbar}, V(x)] = (V(x + L) - V(x))e^{i p L / \hbar}$
      (00:45:28–00:48:48) $\mapsto$ finite-difference commutator
      $[E_{01}, V_{\text{pot}}] = \mathrm{diagScalar}(V_2 - V_1) E_{01}$ and
      $[E_x, V_{\text{pot}}] = -\mathrm{diagScalar}(V_2 - V_1) E_y$.
    - Aharonov–Bohm gauge-invariant modular velocity (00:55:56–00:57:55) $\mapsto$
      Wilson-dressed shift covariance $G T_{\text{AB}} G^{-1} = T_{\text{AB}}(g_1 W_{12} g_2^{-1}, g_2 W_{21} g_1^{-1})$
      and closed holonomy loop $T_{\text{AB}}^2 = \mathrm{localObs}(W_{12} W_{21}, W_{21} W_{12})$.
- **BUCKET 3 (Constructive Lean 4 Theorems Proved Here)**:
  * `TwoStateModularShiftPosetStage` ($\mathcal{A}_0 \prec \mathcal{A}_1 \prec \mathcal{A}_2 \prec \mathcal{A}_3 \prec \mathcal{A}_4$)
    and `TwoStateModularShiftPosetStage.toNat_injective`.
  * `archetype_A0_two_state_transition_sandwich_and_overlap`
  * `archetype_A1_spin_half_weak_value_amplification_identity`
  * `archetype_A1_mat2_pauli_weak_value_amplification`
  * `archetype_A2_local_moment_blindness_vs_modular_shift_sensitivity`
  * `archetype_A3_nonlocal_heisenberg_commutator_for_modular_shift`
  * `archetype_A4_aharonov_bohm_gauge_covariant_modular_velocity`
  * `twoStateModularShift_bimetric_alignment`
-/

namespace NonCommutativeTwoStateAndModularShift

universe u
variable {B : Type u} [Ring B]

-- ============================================================================
-- 0. ACYCLIC CAUSAL POSET (A₀ ≺ A₁ ≺ A₂ ≺ A₃ ≺ A₄)
-- ============================================================================

/-- The five stages of the two-state sandwich and modular shift causal poset
$\mathcal{A}_0 \prec \mathcal{A}_1 \prec \mathcal{A}_2 \prec \mathcal{A}_3 \prec \mathcal{A}_4$. -/
inductive TwoStateModularShiftPosetStage : Type
  | A0 : TwoStateModularShiftPosetStage
  | A1 : TwoStateModularShiftPosetStage
  | A2 : TwoStateModularShiftPosetStage
  | A3 : TwoStateModularShiftPosetStage
  | A4 : TwoStateModularShiftPosetStage
  deriving DecidableEq, Repr

namespace TwoStateModularShiftPosetStage

/-- Numerical rank of each stage in $\mathcal{A}_0 \prec \dots \prec \mathcal{A}_4$. -/
def toNat : TwoStateModularShiftPosetStage → ℕ
  | A0 => 0
  | A1 => 1
  | A2 => 2
  | A3 => 3
  | A4 => 4

/-- `toNat` is injective on `TwoStateModularShiftPosetStage`. -/
theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  cases a <;> cases b <;> first | exact Eq.refl _ | cases h

instance : LinearOrder TwoStateModularShiftPosetStage :=
  LinearOrder.lift' toNat toNat_injective

/-- Strict causal chain $\mathcal{A}_0 \prec \mathcal{A}_1 \prec \mathcal{A}_2 \prec \mathcal{A}_3 \prec \mathcal{A}_4$. -/
theorem causal_poset_chain :
    (A0 : TwoStateModularShiftPosetStage) < A1 ∧
    (A1 : TwoStateModularShiftPosetStage) < A2 ∧
    (A2 : TwoStateModularShiftPosetStage) < A3 ∧
    (A3 : TwoStateModularShiftPosetStage) < A4 := by
  refine ⟨Nat.zero_lt_one, ?_, ?_, ?_⟩
  · exact Nat.lt_succ_self 1
  · exact Nat.lt_succ_self 2
  · exact Nat.lt_succ_self 3

end TwoStateModularShiftPosetStage

/-- Ring commutator `[x, y] = x * y - y * x`. -/
@[simp] def rcomm {A : Type u} [Ring A] (x y : A) : A := x * y - y * x

/-- Ring anticommutator `{x, y} = x * y + y * x`. -/
@[simp] def racomm {A : Type u} [Ring A] (x y : A) : A := x * y + y * x

-- ============================================================================
-- 1. ARCHETYPES A₀ & A₁: TWO-IDEMPOTENT SANDWICHES & WEAK-VALUE AMPLIFICATION
-- ============================================================================

/-- Bilateral two-state transition sandwich `W₂₁(P₂, P₁, A) = P₂ * A * P₁`. -/
@[simp] def twoStateSandwich (P2 P1 A : B) : B := P2 * A * P1

/--
**Archetype A₀ (`archetype_A0_two_state_transition_sandwich_and_overlap`):**
For ANY two (generally non-commuting) idempotents `P₁² = P₁` and `P₂² = P₂` in `[Ring B]`:
1. Left post-selection absorption: `P₂ * twoStateSandwich P₂ P₁ A = twoStateSandwich P₂ P₁ A`.
2. Right pre-selection absorption: `twoStateSandwich P₂ P₁ A * P₁ = twoStateSandwich P₂ P₁ A`.
3. Overlap square factorization through the Fubini–Study transition core `P₁ * P₂ * P₁`:
   `(P₂ * P₁) * (P₂ * P₁) = twoStateSandwich P₂ P₁ (P₁ * P₂ * P₁)`.
4. Linear decomposition of `twoStateSandwich`:
   `twoStateSandwich P₂ P₁ (A + C) = twoStateSandwich P₂ P₁ A + twoStateSandwich P₂ P₁ C`.
-/
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

/--
**Archetype A₁ (`archetype_A1_spin_half_weak_value_amplification_identity`):**
Let `σx, σy ∈ B` be any two anticommuting involutions (`σx² = 1`, `σy² = 1`, `{σx, σy} = 0`),
and let `Px = 1 + σx` (pre-selection projector, `Px² = 2 Px`) and `Py = 1 + σy` (post-selection
projector, `Py² = 2 Py`). Then:
1. **Quadratic Spectral Bound:** `(σx + σy)² = 2 • 1` and `(σx - σy)² = 2 • 1`.
2. **Eigen-Absorption:** `σx * Px = Px` and `Py * σy = Py`.
3. **Weak-Value Amplification Identity (Transcript 00:25:27–00:29:18):**
   `Py * (σx + σy) * Px = (Py * Px) + (Py * Px)` (`= 2 • (Py * Px)`).
4. **Orthogonal Weak-Value Extinction:**
   `Py * (σx - σy) * Px = 0`.
-/
theorem archetype_A1_spin_half_weak_value_amplification_identity
    {σx σy : B} (hx : σx * σx = 1) (hy : σy * σy = 1) (hxy : racomm σx σy = 0) :
    let Px := 1 + σx
    let Py := 1 + σy
    -- 1. Quadratic squares of (σx ± σy) equal 2:
    (σx + σy) * (σx + σy) = 1 + 1 ∧
    (σx - σy) * (σx - σy) = 1 + 1 ∧
    -- 2. Right eigen-absorption of σx on Px and left eigen-absorption of σy on Py:
    σx * Px = Px ∧
    Py * σy = Py ∧
    -- 3. Two-state weak-value amplification of (σx + σy) to 2 • (Py * Px):
    Py * (σx + σy) * Px = (Py * Px) + (Py * Px) ∧
    -- 4. Exact cancellation of (σx - σy) between Py and Px:
    Py * (σx - σy) * Px = 0 := by
  intro Px Py
  have h_anti : σx * σy + σy * σx = 0 := hxy
  have h_abs_x : σx * Px = Px := by
    dsimp [Px]; rw [mul_add, mul_one, hx, add_comm]
  have h_abs_y : Py * σy = Py := by
    dsimp [Py]; rw [add_mul, one_mul, hy, add_comm]
  refine ⟨?_, ?_, h_abs_x, h_abs_y, ?_, ?_⟩
  · calc (σx + σy) * (σx + σy)
      _ = σx * σx + σy * σy + (σx * σy + σy * σx) := by
          simp only [mul_add, add_mul]; abel
      _ = 1 + 1 := by rw [hx, hy, h_anti, add_zero]
  · calc (σx - σy) * (σx - σy)
      _ = σx * σx + σy * σy - (σx * σy + σy * σx) := by
          simp only [mul_sub, sub_mul]; abel
      _ = 1 + 1 := by rw [hx, hy, h_anti, sub_zero]
  · calc Py * (σx + σy) * Px
      _ = Py * (σx * Px) + (Py * σy) * Px := by
          simp only [mul_add, add_mul, mul_assoc]
      _ = (Py * Px) + (Py * Px) := by rw [h_abs_x, h_abs_y]
  · calc Py * (σx - σy) * Px
      _ = Py * (σx * Px) - (Py * σy) * Px := by
          simp only [mul_sub, sub_mul, mul_assoc]
      _ = (Py * Px) - (Py * Px) := by rw [h_abs_x, h_abs_y]
      _ = 0 := sub_self (Py * Px)

-- ============================================================================
-- 2. 2x2 MATRIX OPERATOR ALGEBRA `Mat2 B`: ARCHETYPES A₂, A₃, A₄
-- ============================================================================

/-- 2×2 matrix over `α`. -/
@[ext]
structure Mat2 (α : Type u) where
  a11 : α
  a12 : α
  a21 : α
  a22 : α
  deriving DecidableEq, Repr

instance : Inhabited (Mat2 B) := ⟨⟨0, 0, 0, 0⟩⟩

namespace Mat2

@[simp] def zero : Mat2 B := ⟨0, 0, 0, 0⟩
@[simp] def one  : Mat2 B := ⟨1, 0, 0, 1⟩
@[simp] def add (M N : Mat2 B) : Mat2 B :=
  ⟨M.a11 + N.a11, M.a12 + N.a12, M.a21 + N.a21, M.a22 + N.a22⟩
@[simp] def neg (M : Mat2 B) : Mat2 B :=
  ⟨-M.a11, -M.a12, -M.a21, -M.a22⟩
@[simp] def sub (M N : Mat2 B) : Mat2 B :=
  ⟨M.a11 - N.a11, M.a12 - N.a12, M.a21 - N.a21, M.a22 - N.a22⟩
@[simp] def mul (M N : Mat2 B) : Mat2 B :=
  ⟨M.a11 * N.a11 + M.a12 * N.a21, M.a11 * N.a12 + M.a12 * N.a22,
   M.a21 * N.a11 + M.a22 * N.a21, M.a21 * N.a12 + M.a22 * N.a22⟩

@[simp] def nsmulMat (n : ℕ) (M : Mat2 B) : Mat2 B :=
  ⟨n • M.a11, n • M.a12, n • M.a21, n • M.a22⟩

@[simp] def zsmulMat (n : ℤ) (M : Mat2 B) : Mat2 B :=
  ⟨n • M.a11, n • M.a12, n • M.a21, n • M.a22⟩

instance : Zero (Mat2 B) := ⟨zero⟩
instance : One (Mat2 B)  := ⟨one⟩
instance : Add (Mat2 B)  := ⟨add⟩
instance : Neg (Mat2 B)  := ⟨neg⟩
instance : Sub (Mat2 B)  := ⟨sub⟩
instance : Mul (Mat2 B)  := ⟨mul⟩

@[simp] lemma zero_a11 : (0 : Mat2 B).a11 = 0 := by
  have h : (0 : Mat2 B).a11 = 0 := Eq.refl _
  exact h
@[simp] lemma zero_a12 : (0 : Mat2 B).a12 = 0 := by
  have h : (0 : Mat2 B).a12 = 0 := Eq.refl _
  exact h
@[simp] lemma zero_a21 : (0 : Mat2 B).a21 = 0 := by
  have h : (0 : Mat2 B).a21 = 0 := Eq.refl _
  exact h
@[simp] lemma zero_a22 : (0 : Mat2 B).a22 = 0 := by
  have h : (0 : Mat2 B).a22 = 0 := Eq.refl _
  exact h
@[simp] lemma one_a11 : (1 : Mat2 B).a11 = 1 := by
  have h : (1 : Mat2 B).a11 = 1 := Eq.refl _
  exact h
@[simp] lemma one_a12 : (1 : Mat2 B).a12 = 0 := by
  have h : (1 : Mat2 B).a12 = 0 := Eq.refl _
  exact h
@[simp] lemma one_a21 : (1 : Mat2 B).a21 = 0 := by
  have h : (1 : Mat2 B).a21 = 0 := Eq.refl _
  exact h
@[simp] lemma one_a22 : (1 : Mat2 B).a22 = 1 := by
  have h : (1 : Mat2 B).a22 = 1 := Eq.refl _
  exact h
@[simp] lemma add_a11 (M N : Mat2 B) : (M + N).a11 = M.a11 + N.a11 := by
  have h : (M + N).a11 = M.a11 + N.a11 := Eq.refl _
  exact h
@[simp] lemma add_a12 (M N : Mat2 B) : (M + N).a12 = M.a12 + N.a12 := by
  have h : (M + N).a12 = M.a12 + N.a12 := Eq.refl _
  exact h
@[simp] lemma add_a21 (M N : Mat2 B) : (M + N).a21 = M.a21 + N.a21 := by
  have h : (M + N).a21 = M.a21 + N.a21 := Eq.refl _
  exact h
@[simp] lemma add_a22 (M N : Mat2 B) : (M + N).a22 = M.a22 + N.a22 := by
  have h : (M + N).a22 = M.a22 + N.a22 := Eq.refl _
  exact h
@[simp] lemma neg_a11 (M : Mat2 B) : (-M).a11 = -M.a11 := by
  have h : (-M).a11 = -M.a11 := Eq.refl _
  exact h
@[simp] lemma neg_a12 (M : Mat2 B) : (-M).a12 = -M.a12 := by
  have h : (-M).a12 = -M.a12 := Eq.refl _
  exact h
@[simp] lemma neg_a21 (M : Mat2 B) : (-M).a21 = -M.a21 := by
  have h : (-M).a21 = -M.a21 := Eq.refl _
  exact h
@[simp] lemma neg_a22 (M : Mat2 B) : (-M).a22 = -M.a22 := by
  have h : (-M).a22 = -M.a22 := Eq.refl _
  exact h
@[simp] lemma sub_a11 (M N : Mat2 B) : (M - N).a11 = M.a11 - N.a11 := by
  have h : (M - N).a11 = M.a11 - N.a11 := Eq.refl _
  exact h
@[simp] lemma sub_a12 (M N : Mat2 B) : (M - N).a12 = M.a12 - N.a12 := by
  have h : (M - N).a12 = M.a12 - N.a12 := Eq.refl _
  exact h
@[simp] lemma sub_a21 (M N : Mat2 B) : (M - N).a21 = M.a21 - N.a21 := by
  have h : (M - N).a21 = M.a21 - N.a21 := Eq.refl _
  exact h
@[simp] lemma sub_a22 (M N : Mat2 B) : (M - N).a22 = M.a22 - N.a22 := by
  have h : (M - N).a22 = M.a22 - N.a22 := Eq.refl _
  exact h
@[simp] lemma mul_a11 (M N : Mat2 B) : (M * N).a11 = M.a11 * N.a11 + M.a12 * N.a21 := by
  have h : (M * N).a11 = M.a11 * N.a11 + M.a12 * N.a21 := Eq.refl _
  exact h
@[simp] lemma mul_a12 (M N : Mat2 B) : (M * N).a12 = M.a11 * N.a12 + M.a12 * N.a22 := by
  have h : (M * N).a12 = M.a11 * N.a12 + M.a12 * N.a22 := Eq.refl _
  exact h
@[simp] lemma mul_a21 (M N : Mat2 B) : (M * N).a21 = M.a21 * N.a11 + M.a22 * N.a21 := by
  have h : (M * N).a21 = M.a21 * N.a11 + M.a22 * N.a21 := Eq.refl _
  exact h
@[simp] lemma mul_a22 (M N : Mat2 B) : (M * N).a22 = M.a21 * N.a12 + M.a22 * N.a22 := by
  have h : (M * N).a22 = M.a21 * N.a12 + M.a22 * N.a22 := Eq.refl _
  exact h

macro "aharonov_nc_mat2" : tactic =>
  `(tactic| (
    (try ext) <;>
    (simp only [zero, one, add, neg, sub, mul,
                zero_a11, zero_a12, zero_a21, zero_a22,
                one_a11, one_a12, one_a21, one_a22,
                add_a11, add_a12, add_a21, add_a22,
                neg_a11, neg_a12, neg_a21, neg_a22,
                sub_a11, sub_a12, sub_a21, sub_a22,
                mul_a11, mul_a12, mul_a21, mul_a22,
                mul_add, add_mul, sub_mul, mul_sub,
                mul_zero, zero_mul, mul_one, one_mul,
                add_zero, zero_add, sub_zero, zero_sub,
                neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                mul_assoc];
     try abel)))

instance instRingMat2 : Ring (Mat2 B) where
  add := add
  add_assoc := by intros; aharonov_nc_mat2
  zero := zero
  zero_add := by intros; aharonov_nc_mat2
  add_zero := by intros; aharonov_nc_mat2
  nsmul := nsmulMat
  nsmul_zero := by intros; ext <;> exact zero_smul ℕ _
  nsmul_succ := by intros; ext <;> exact succ_nsmul _ _
  zsmul := zsmulMat
  zsmul_zero' := by intros; ext <;> exact zero_smul ℤ _
  zsmul_succ' := by intros; ext <;> exact SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' := by intros; ext <;> exact SubNegMonoid.zsmul_neg' _ _
  neg := neg
  sub := sub
  sub_eq_add_neg := by intros; aharonov_nc_mat2
  neg_add_cancel := by intros; aharonov_nc_mat2
  add_comm := by intros; aharonov_nc_mat2
  mul := mul
  left_distrib := by intros; aharonov_nc_mat2
  right_distrib := by intros; aharonov_nc_mat2
  zero_mul := by intros; aharonov_nc_mat2
  mul_zero := by intros; aharonov_nc_mat2
  mul_assoc := by intros; aharonov_nc_mat2
  one := one
  one_mul := by intros; aharonov_nc_mat2
  mul_one := by intros; aharonov_nc_mat2

/-- Matrix trace `tr₂(M) = m₁₁ + m₂₂`. -/
@[simp] def tr2 (M : Mat2 B) : B := M.a11 + M.a22

/-- Scalar diagonal matrix `diagScalar(c) = [[c, 0], [0, c]]`. -/
@[simp] def diagScalar (c : B) : Mat2 B := ⟨c, 0, 0, c⟩

/-- Symmetric Pauli-X shift generator `Ex = [[0, 1], [1, 0]]`. -/
@[simp] def Ex : Mat2 B := ⟨0, 1, 1, 0⟩

/-- Symplectic Pauli-Y generator `Ey = [[0, -1], [1, 0]]`. -/
@[simp] def Ey : Mat2 B := ⟨0, -1, 1, 0⟩

/-- Diagonal Pauli-Z generator `Ez = [[1, 0], [0, -1]]`. -/
@[simp] def Ez : Mat2 B := ⟨1, 0, 0, -1⟩

/-- Upper-triangular forward shift unit `E₀₁ = [[0, 1], [0, 0]]`. -/
@[simp] def E01 : Mat2 B := ⟨0, 1, 0, 0⟩

/-- Concrete realization of Archetype A₁ on `(Ex, Ez)` in `Mat2 B`. -/
theorem archetype_A1_mat2_pauli_weak_value_amplification :
    let Px : Mat2 B := 1 + Ex
    let Pz : Mat2 B := 1 + Ez
    ((Ex : Mat2 B) + Ez) * (Ex + Ez) = 1 + 1 ∧
    Pz * (Ex + Ez) * Px = (Pz * Px) + (Pz * Px) ∧
    Pz * (Ex - Ez) * Px = 0 := by
  have hx : (Ex : Mat2 B) * Ex = 1 := by simp only [Ex]; aharonov_nc_mat2
  have hz : (Ez : Mat2 B) * Ez = 1 := by simp only [Ez]; aharonov_nc_mat2
  have hxz : racomm (Ex : Mat2 B) Ez = 0 := by simp only [racomm, Ex, Ez]; aharonov_nc_mat2
  have hA1 := archetype_A1_spin_half_weak_value_amplification_identity hx hz hxz
  exact ⟨hA1.1, hA1.2.2.2.2.1, hA1.2.2.2.2.2⟩

/-- Two-slit state matrix `ρ(d₁, d₂, u_+, u_-) = [[d₁, u_+], [u_-, d₂]]` with off-diagonal coherences. -/
@[simp] def twoPacketState (d1 d2 u_plus u_minus : B) : Mat2 B :=
  ⟨d1, u_plus, u_minus, d2⟩

/-- Local support-preserving observable `D_loc(f₁, f₂) = [[f₁, 0], [0, f₂]]` (e.g. polynomial `x^m p^n`). -/
@[simp] def localObs (f1 f2 : B) : Mat2 B :=
  ⟨f1, 0, 0, f2⟩

/-- Non-local Weyl shift / modular translation operator `T_L(τ_+, τ_-) = [[0, τ_+], [τ_-, 0]]`. -/
@[simp] def modularShift (τ_plus τ_minus : B) : Mat2 B :=
  ⟨0, τ_plus, τ_minus, 0⟩

/-- Local diagonal gauge transformation `G(g₁, g₂) = [[g₁, 0], [0, g₂]]`. -/
@[simp] def gaugeDiag (g1 g2 : B) : Mat2 B :=
  ⟨g1, 0, 0, g2⟩

/--
**Archetype A₂ (`archetype_A2_local_moment_blindness_vs_modular_shift_sensitivity`):**
Formalizes Transcript 00:40:40–00:44:21 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. **Blindness of Local Polynomial Moments:**
   For any `ρ = twoPacketState d₁ d₂ u_+ u_-` and `D = localObs f₁ f₂`, both `tr₂(ρ * D)`
   and `tr₂(ρ * D²)` depend ONLY on `(d₁, d₂)` and are completely independent of the
   interference coherences `(u_+, u_-)`:
   `tr₂(twoPacketState d₁ d₂ u_+ u_- * D) = tr₂(twoPacketState d₁ d₂ 0 0 * D)`.
2. **Phase Sensitivity of the Modular Shift Operator `T_L`:**
   `tr₂(twoPacketState d₁ d₂ u_+ u_- * modularShift τ_+ τ_-) = u_+ * τ_- + u_- * τ_+`,
   annihilating `(d₁, d₂)` and directly extracting the interference phase.
-/
theorem archetype_A2_local_moment_blindness_vs_modular_shift_sensitivity
    (d1 d2 u_plus u_minus f1 f2 τ_plus τ_minus : B) :
    let ρ_coh := twoPacketState d1 d2 u_plus u_minus
    let ρ_inc := twoPacketState d1 d2 0 0
    let D     := localObs f1 f2
    let T_L   := modularShift τ_plus τ_minus
    -- 1. Local observables D and D² are 100% blind to the interference coherences (u_+, u_-):
    tr2 (ρ_coh * D) = d1 * f1 + d2 * f2 ∧
    tr2 (ρ_coh * D) = tr2 (ρ_inc * D) ∧
    tr2 (ρ_coh * (D * D)) = tr2 (ρ_inc * (D * D)) ∧
    -- 2. The modular shift operator T_L directly extracts the interference coherences:
    tr2 (ρ_coh * T_L) = u_plus * τ_minus + u_minus * τ_plus ∧
    tr2 (ρ_inc * T_L) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [twoPacketState, localObs, modularShift, tr2]; aharonov_nc_mat2

/--
**Archetype A₃ (`archetype_A3_nonlocal_heisenberg_commutator_for_modular_shift`):**
Formalizes Transcript 00:45:28–00:48:48 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. **Forward Weyl Shift Commutator (`[e^{i p L / ħ}, V(x)] = (V(x + L) - V(x)) e^{i p L / ħ}`):**
   For `V_pot = localObs V₁ V₂`, the Heisenberg commutator with `E₀₁ = [[0, 1], [0, 0]]` is:
   `E₀₁ * V_pot - V_pot * E₀₁ = [[0, V₂ - V₁], [0, 0]] = diagScalar(V₂ - V₁) * E₀₁`.
2. **General Modular Shift Commutator:**
   `modularShift τ_+ τ_- * V_pot - V_pot * modularShift τ_+ τ_- =`
   `[[0, τ_+ V₂ - V₁ τ_+], [τ_- V₁ - V₂ τ_-, 0]]`.
3. **Symmetric Shift Commutator (`Ex`):**
   `Ex * V_pot - V_pot * Ex = -diagScalar(V₂ - V₁) * Ey`.
-/
theorem archetype_A3_nonlocal_heisenberg_commutator_for_modular_shift
    (V1 V2 τ_plus τ_minus : B) :
    let V_pot := localObs V1 V2
    let T_L   := modularShift τ_plus τ_minus
    -- 1. Forward shift commutator is proportional to the non-local potential difference V₂ - V₁:
    E01 * V_pot - V_pot * E01 = ⟨0, V2 - V1, 0, 0⟩ ∧
    E01 * V_pot - V_pot * E01 = diagScalar (V2 - V1) * E01 ∧
    -- 2. General non-commutative modular shift commutator:
    T_L * V_pot - V_pot * T_L = ⟨0, τ_plus * V2 - V1 * τ_plus, τ_minus * V1 - V2 * τ_minus, 0⟩ ∧
    -- 3. Symmetric shift Ex commutator:
    Ex * V_pot - V_pot * Ex = -(diagScalar (V2 - V1) * Ey) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [localObs, modularShift, diagScalar, E01, Ex, Ey]; aharonov_nc_mat2

/--
**Archetype A₄ (`archetype_A4_aharonov_bohm_gauge_covariant_modular_velocity`):**
Formalizes Transcript 00:55:56–00:57:55 in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. **Gauge-Covariant Modular Velocity Transformation:**
   Under local gauge transformations `G = gaugeDiag g₁ g₂` and `G_inv = gaugeDiag g₁_inv g₂_inv`,
   the Wilson-dressed modular shift `T_AB = modularShift W₁₂ W₂₁` transforms as:
   `G * T_AB * G_inv = modularShift (g₁ * W₁₂ * g₂_inv) (g₂ * W₂₁ * g₁_inv)`.
2. **Closed Aharonov–Bohm Holonomy Loop:**
   `T_AB * T_AB = localObs (W₁₂ * W₂₁) (W₂₁ * W₁₂)`, and when `g₂_inv * g₂ = 1` and `g₁_inv * g₁ = 1`,
   `(G * T_AB * G_inv)² = localObs (g₁ * W₁₂ * W₂₁ * g₁_inv) (g₂ * W₂₁ * W₁₂ * g₂_inv)`.
-/
theorem archetype_A4_aharonov_bohm_gauge_covariant_modular_velocity
    (g1 g2 g1_inv g2_inv W12 W21 : B)
    (hg1 : g1_inv * g1 = 1) (hg2 : g2_inv * g2 = 1) :
    let G     := gaugeDiag g1 g2
    let G_inv := gaugeDiag g1_inv g2_inv
    let T_AB  := modularShift W12 W21
    let T_gauged := G * T_AB * G_inv
    -- 1. Exact gauge covariance of the Wilson-dressed modular shift:
    T_gauged = modularShift (g1 * W12 * g2_inv) (g2 * W21 * g1_inv) ∧
    -- 2. Square of T_AB is the closed Wilson holonomy loop on each slit:
    T_AB * T_AB = localObs (W12 * W21) (W21 * W12) ∧
    -- 3. Gauge-conjugated holonomy loop:
    T_gauged * T_gauged =
      localObs (g1 * W12 * W21 * g1_inv) (g2 * W21 * W12 * g2_inv) := by
  intro G G_inv T_AB T_gauged
  have h1 : T_gauged = modularShift (g1 * W12 * g2_inv) (g2 * W21 * g1_inv) := by
    simp only [T_gauged, G, G_inv, T_AB, gaugeDiag, modularShift]; aharonov_nc_mat2
  have h2 : T_AB * T_AB = localObs (W12 * W21) (W21 * W12) := by
    simp only [T_AB, modularShift, localObs]; aharonov_nc_mat2
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

-- ============================================================================
-- 3. OWNER ALIGNMENT TO `BimetricSheetGeometry` & `TwoStateSandwich`
-- ============================================================================

/-- Equivalence between `NonCommutativeTwoStateAndModularShift.Mat2 B` and
`NonCommutativeBimetricSheetGeometry.Mat2 B`. -/
@[simp] def toBimetricMat2 (M : Mat2 B) : NonCommutativeBimetricSheetGeometry.Mat2 B :=
  ⟨M.a11, M.a12, M.a21, M.a22⟩

/--
**Owner Alignment (`twoStateModularShift_bimetric_alignment`):**
Aligns the modular Weyl shift `modularShift W12 W21`, its holonomy square
`localObs (W12 * W21) (W21 * W12)`, and `twoStateSandwich` with `matPhi`, `matV` in
`NonCommutativeBimetricSheetGeometry` and ordered two-chart sandwiches in
`InfoGeometry.OperatorAlgebra.PeirceSpine`:
1. `toBimetricMat2 (modularShift W12 W21) = matPhi W12 W21`
2. `toBimetricMat2 (localObs (W12 * W21) (W21 * W12)) = matV W12 W21`
3. `twoStateSandwich (P - conePlus P A) (P + coneMinus P C) X = (P - conePlus P A) * X * (P + coneMinus P C)`
-/
theorem twoStateModularShift_bimetric_alignment (P A C X W12 W21 : B) :
    toBimetricMat2 (modularShift W12 W21) =
      NonCommutativeBimetricSheetGeometry.Mat2.matPhi W12 W21 ∧
    toBimetricMat2 (localObs (W12 * W21) (W21 * W12)) =
      NonCommutativeBimetricSheetGeometry.Mat2.matV W12 W21 ∧
    twoStateSandwich
        (P - InfoGeometry.Core.IdempotentGraphGrassmannian.conePlus P A)
        (P + InfoGeometry.Core.IdempotentGraphGrassmannian.coneMinus P C) X =
      (P - InfoGeometry.Core.IdempotentGraphGrassmannian.conePlus P A) * X *
        (P + InfoGeometry.Core.IdempotentGraphGrassmannian.coneMinus P C) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : toBimetricMat2 (modularShift W12 W21) =
        NonCommutativeBimetricSheetGeometry.Mat2.matPhi W12 W21 := Eq.refl _
    exact h1
  · have h2 : toBimetricMat2 (localObs (W12 * W21) (W21 * W12)) =
        NonCommutativeBimetricSheetGeometry.Mat2.matV W12 W21 := Eq.refl _
    exact h2
  · have h3 : twoStateSandwich
        (P - InfoGeometry.Core.IdempotentGraphGrassmannian.conePlus P A)
        (P + InfoGeometry.Core.IdempotentGraphGrassmannian.coneMinus P C) X =
      (P - InfoGeometry.Core.IdempotentGraphGrassmannian.conePlus P A) * X *
        (P + InfoGeometry.Core.IdempotentGraphGrassmannian.coneMinus P C) := Eq.refl _
    exact h3

end Mat2
end NonCommutativeTwoStateAndModularShift
