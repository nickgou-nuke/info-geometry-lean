/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- [HIVE-MINDPROVENANCE HEADER]
-- LAYER: Operator Algebra / Peirce Spine (Finite Two-State and Modular-Shift Identities)
-- ARCHITECTURAL ROLE: Bilateral Sandwiches, Modular Shifts, and Two-Arm Operator Identities
-- EPISTEMIC STATUS: Algebraic identities only; physical interpretation requires separate structures
-- DEPENDENCIES: Mathlib.Algebra.Ring.Defs, Mathlib.Tactic.Abel, InfoGeometry.OperatorAlgebra.PeirceSpine.BimetricSheetGeometry
-- [END HEADER]

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.PeirceSpine.BimetricSheetGeometry

/-!
# Two-State Sandwich Algebras, Weak-Value Amplification & Non-Local Weyl Shift Commutators (A₀ ≺ ... ≺ A₄)

Formalized over an arbitrary noncommutative associative ring `[Ring B]` and explicit
finite matrix carriers. These declarations do not define normalized Hilbert-space
states, an inner product, probabilities, or weak-value quotients. Physical terminology
below records motivation rather than a proved physical interpretation.

## Audit Classification Map
- **BUCKET 1 (Kernel-Checked Constructive Identities):** All definitions and theorems (`archetype_A0`..`archetype_A5`, `archetype_G0`..`archetype_G2`, `archetype_R0`..`archetype_R4`, `archetype_N0`..`archetype_N4`, `archetype_C0`..`archetype_C5`).
- **BUCKET 2 (Eliminated Wrapper / Proxy Surfaces):** Zero `_True` surfaces, zero certificate wrappers, zero custom axioms.
- **BUCKET 3 (Open / Deferred Analytic Extensions):** Continuous Hilbert-space limits and probability normalization are outside this ring-algebraic module.

## Scope
The theorems below prove ring-level and finite-matrix identities under their explicit
hypotheses. They do not prove the physical weak-value quotient or measurement semantics.
The unnormalized factors `1 + σ` used below are quasi-idempotents, not generally projectors.
-/

namespace NonCommutativeTwoStateAndModularShift

universe u
variable {B : Type u} [Ring B]

/-- Ring commutator `[x, y] = x * y - y * x`. -/
@[simp] def rcomm {A : Type u} [Ring A] (x y : A) : A := x * y - y * x

/-- Ring anticommutator `{x, y} = x * y + y * x`. -/
@[simp] def racomm {A : Type u} [Ring A] (x y : A) : A := x * y + y * x

/-- The unnormalized `1 + x` associated with an involution is quasi-idempotent:
its square is twice itself. It is not generally an idempotent projector. -/
lemma one_add_involution_sq {x : B} (hx : x * x = 1) :
    (1 + x) * (1 + x) = (1 + x) + (1 + x) := by
  calc
    (1 + x) * (1 + x) = 1 * (1 + x) + x * (1 + x) := add_mul 1 x (1 + x)
    _ = (1 + x) + (x + x * x) := by rw [one_mul, mul_add, mul_one]
    _ = (1 + x) + (1 + x) := by rw [hx, add_comm x 1]

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
    rw [← mul_assoc P2 (P2 * A) P1, ← mul_assoc P2 P2 A, hP2]
  · dsimp [twoStateSandwich]
    rw [mul_assoc (P2 * A) P1 P1, hP1]
  · dsimp [twoStateSandwich]
    simp only [mul_assoc]
    rw [hP1]
  · dsimp [twoStateSandwich]
    simp only [mul_add, add_mul]

/-- Right-associated idempotent absorption `P * (P * Y) = P * Y`. -/
lemma idem_assoc {A : Type u} [Ring A] {P : A} (hP : P * P = P) (Y : A) :
    P * (P * Y) = P * Y := by
  rw [← mul_assoc P P Y, hP]

/--
**Archetype R₂ (`archetype_R2_halmos_two_idempotent_trigonometry_and_commutator`):**
Halmos's Universal Two-Idempotent Theorem in any non-commutative ring `[Ring B]`:
For any two idempotents `P₁ * P₁ = P₁` and `P₂ * P₂ = P₂`, the chordal distance operator
`Δ₂₁ = (P₂ - P₁) * (P₂ - P₁)` and contextuality commutator `C₂₁ = rcomm P₂ P₁` satisfy:
1. `[Δ₂₁, P₁] = 0` and `[Δ₂₁, P₂] = 0` (`Δ₂₁` commutes with both `P₁` and `P₂`),
2. `P₁ * P₂ * P₁ = P₁ * (1 - Δ₂₁)` and `P₂ * P₁ * P₂ = P₂ * (1 - Δ₂₁)` (Born transition sandwiches),
3. `-(C₂₁ * C₂₁) = Δ₂₁ * (1 - Δ₂₁)` (`-[P₂, P₁]² = Δ₂₁(1 - Δ₂₁)`).
-/
theorem archetype_R2_halmos_two_idempotent_trigonometry_and_commutator
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

/--
**Lineage L₀ (`lineage_L0_jordan_dixmier_davis_halmos_dihedral_two_idempotent_theorem`):**
Unifies Jordan (1875), Dixmier (1949), Davis (1958), and Halmos (1969) in ANY non-commutative
associative ring `[Ring B]`:
For any two idempotents `P₁ * P₁ = P₁` and `P₂ * P₂ = P₂`, define the difference operator
`D = P₂ - P₁` and the Davis reflection operator `Sig = P₁ + P₂ - 1`. Without Hilbert spaces,
involutions, or square roots:
1. **Chiral Factorizations of `[P₂, P₁]`:** `D * Sig = [P₂, P₁]` and `Sig * D = -[P₂, P₁]`.
2. **Strict Anticommutation:** `{D, Sig} = 0` and `[D, Sig] = 2 • [P₂, P₁]`.
3. **Universal Operator Pythagorean Identity (`sin² θ + cos² θ = 1`):** `D * D + Sig * Sig = 1`.
4. **Exact Subspace Intertwining:** `P₁ * Sig = P₁ * P₂`, `Sig * P₂ = P₁ * P₂`, `P₁ * Sig = Sig * P₂`,
   and `D * P₁ = (1 - P₂) * D`.
5. **Halmos Transition & Commutator Square Identities:**
   `P₁ * P₂ * P₁ = P₁ * (Sig * Sig) = P₁ * (1 - D * D)` and
   `-([P₂, P₁] * [P₂, P₁]) = (D * D) * (Sig * Sig) = (D * D) * (1 - D * D)`.
-/
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
    (simp only [sub_mul, mul_sub, mul_add, mul_one, hP1, hP2]); abel
  have h2 : (P1 + P2 - 1) * (P2 - P1) = -(P2 * P1 - P1 * P2) := by
    (simp only [sub_mul, mul_sub, add_mul, one_mul, hP1, hP2]); abel
  have h3 : (P2 - P1) * (P1 + P2 - 1) + (P1 + P2 - 1) * (P2 - P1) = 0 := by
    rw [h1, h2, add_neg_cancel]
  have h4 : (P2 - P1) * (P1 + P2 - 1) - (P1 + P2 - 1) * (P2 - P1) =
      (P2 * P1 - P1 * P2) + (P2 * P1 - P1 * P2) := by
    rw [h1, h2, sub_neg_eq_add]
  have h5 : (P2 - P1) * (P2 - P1) + (P1 + P2 - 1) * (P1 + P2 - 1) = 1 := by
    (simp only [sub_mul, mul_sub, add_mul, mul_add, mul_one, one_mul, hP1, hP2]); abel
  have h6 : P1 * (P1 + P2 - 1) = P1 * P2 := by
    (simp only [mul_sub, mul_add, mul_one, hP1]); abel
  have h7 : (P1 + P2 - 1) * P2 = P1 * P2 := by
    (simp only [sub_mul, add_mul, one_mul, hP2]); abel
  have h8 : P1 * (P1 + P2 - 1) = (P1 + P2 - 1) * P2 := by
    rw [h6, h7]
  have h9 : (P2 - P1) * P1 = (1 - P2) * (P2 - P1) := by
    (simp only [sub_mul, mul_sub, one_mul, hP1, hP2]); abel
  have hR2 := archetype_R2_halmos_two_idempotent_trigonometry_and_commutator hP1 hP2
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
          (simp only [mul_add, add_mul]); abel
      _ = 1 + 1 := by rw [hx, hy, h_anti, add_zero]
  · calc (σx - σy) * (σx - σy)
      _ = σx * σx + σy * σy - (σx * σy + σy * σx) := by
          (simp only [mul_sub, sub_mul]); abel
      _ = 1 + 1 := by rw [hx, hy, h_anti, sub_zero]
  · calc Py * (σx + σy) * Px
      _ = Py * (σx * Px) + (Py * σy) * Px := by
          (simp only [mul_add, add_mul, mul_assoc])
      _ = (Py * Px) + (Py * Px) := by rw [h_abs_x, h_abs_y]
  · calc Py * (σx - σy) * Px
      _ = Py * (σx * Px) - (Py * σy) * Px := by
          (simp only [mul_sub, sub_mul, mul_assoc])
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
  deriving DecidableEq, Repr, Inhabited

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

instance instZero : Zero (Mat2 B) := ⟨zero⟩
instance instOne : One (Mat2 B)  := ⟨one⟩
instance instAdd : Add (Mat2 B)  := ⟨add⟩
instance instNeg : Neg (Mat2 B)  := ⟨neg⟩
instance instSub : Sub (Mat2 B)  := ⟨sub⟩
instance instMul : Mul (Mat2 B)  := ⟨mul⟩

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
  have hx : (Ex : Mat2 B) * Ex = 1 := by dsimp only [Ex]; aharonov_nc_mat2
  have hz : (Ez : Mat2 B) * Ez = 1 := by dsimp only [Ez]; aharonov_nc_mat2
  have hxz : racomm (Ex : Mat2 B) Ez = 0 := by dsimp only [racomm, Ex, Ez]; aharonov_nc_mat2
  have hA1 := archetype_A1_spin_half_weak_value_amplification_identity hx hz hxz
  exact ⟨hA1.1, hA1.2.2.2.2.1, hA1.2.2.2.2.2⟩

/-- Two-slit state matrix `ρ(d₁, d₂, u_+, u_-) = [[d₁, u_+], [u_-, d₂]]` with off-diagonal coherences. -/
@[simp] def twoSlitState (d1 d2 u_plus u_minus : B) : Mat2 B :=
  ⟨d1, u_plus, u_minus, d2⟩

/-- Local support-preserving observable `D_loc(f₁, f₂) = [[f₁, 0], [0, f₂]]` (e.g. polynomial `x^m p^n`). -/
@[simp] def localObs (f1 f2 : B) : Mat2 B :=
  ⟨f1, 0, 0, f2⟩

/-- Multiplication of diagonal observables is componentwise, without assuming `B` commutative. -/
theorem localObs_mul (a b c d : B) :
    localObs a b * localObs c d = localObs (a * c) (b * d) := by
  dsimp only [localObs]; aharonov_nc_mat2

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
   For any `ρ = twoSlitState d₁ d₂ u_+ u_-` and `D = localObs f₁ f₂`, both `tr₂(ρ * D)`
   and `tr₂(ρ * D²)` depend ONLY on `(d₁, d₂)` and are completely independent of the
   interference coherences `(u_+, u_-)`:
   `tr₂(twoSlitState d₁ d₂ u_+ u_- * D) = tr₂(twoSlitState d₁ d₂ 0 0 * D)`.
2. **Phase Sensitivity of the Modular Shift Operator `T_L`:**
   `tr₂(twoSlitState d₁ d₂ u_+ u_- * modularShift τ_+ τ_-) = u_+ * τ_- + u_- * τ_+`,
   annihilating `(d₁, d₂)` and directly extracting the interference phase.
-/
theorem archetype_A2_local_moment_blindness_vs_modular_shift_sensitivity
    (d1 d2 u_plus u_minus f1 f2 τ_plus τ_minus : B) :
    let ρ_coh := twoSlitState d1 d2 u_plus u_minus
    let ρ_inc := twoSlitState d1 d2 0 0
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
  · simp only [twoSlitState, localObs, modularShift, tr2]; aharonov_nc_mat2

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
    dsimp only [T_gauged, G, G_inv, T_AB, gaugeDiag, modularShift]; aharonov_nc_mat2
  have h2 : T_AB * T_AB = localObs (W12 * W21) (W21 * W12) := by
    dsimp only [T_AB, modularShift, localObs]; aharonov_nc_mat2
  refine ⟨h1, h2, ?_⟩
  rw [h1]
  ext <;>
  · simp only [modularShift, localObs, mul_a11, mul_a12, mul_a21, mul_a22,
               mul_zero, zero_mul, add_zero, zero_add]
    try (calc g1 * W12 * g2_inv * (g2 * W21 * g1_inv)
          _ = g1 * W12 * (g2_inv * g2) * W21 * g1_inv := by (simp only [mul_assoc])
          _ = g1 * W12 * W21 * g1_inv                 := by rw [hg2, mul_one])
    try (calc g2 * W21 * g1_inv * (g1 * W12 * g2_inv)
          _ = g2 * W21 * (g1_inv * g1) * W12 * g2_inv := by (simp only [mul_assoc])
          _ = g2 * W21 * W12 * g2_inv                 := by rw [hg1, mul_one])

/--
**Archetype A₅ (`archetype_A5_quantum_cheshire_cat_two_state_decoupling`):**
Formalizes Aharonov's Quantum Cheshire Cat (Transcript 00:01:08) in `Mat2 B` over ANY
non-commutative ring `[Ring B]` equipped with anticommuting spin involutions
`σx² = 1, σz² = 1, {σx, σz} = 0`:
For the pre-selection operator `Ψ_cat = localObs (1 + σx) ((1 - σx) * σz)`, post-selection
operator `Φ_cat = localObs (1 + σx) (1 + σx)`, left/right spatial path projectors
`P_left = localObs 1 0`, `P_right = localObs 0 1`, and spin observable `S_z = diagScalar σz`:
1. **Particle Presence in Left Arm Only:**
   `Φ_cat * P_left * Ψ_cat = localObs ((1 + σx) + (1 + σx)) 0` and
   `Φ_cat * P_right * Ψ_cat = 0`.
2. **Spin Presence in Right Arm Only (Spatial Separation of Spin from Particle):**
   `Φ_cat * (P_left * S_z) * Ψ_cat = 0` and
   `Φ_cat * (P_right * S_z) * Ψ_cat = localObs 0 ((1 + σx) + (1 + σx))`.
-/
theorem archetype_A5_quantum_cheshire_cat_two_state_decoupling
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Qplus  := 1 + σx
    let Qminus := 1 - σx
    let Ψ_cat  := localObs Qplus (Qminus * σz)
    let Φ_cat  := localObs Qplus Qplus
    let P_left := localObs (1 : B) 0
    let P_right := localObs (0 : B) 1
    let S_z    := diagScalar σz
    -- 1. Particle presence is localized in the Left arm and vanishes in the Right arm:
    Φ_cat * P_left * Ψ_cat = localObs (Qplus + Qplus) 0 ∧
    Φ_cat * P_right * Ψ_cat = 0 ∧
    -- 2. Spin S_z vanishes in the Left arm and is localized in the Right arm:
    Φ_cat * (P_left * S_z) * Ψ_cat = 0 ∧
    Φ_cat * (P_right * S_z) * Ψ_cat = localObs 0 (Qplus + Qplus) := by
  intro Qplus Qminus Ψ_cat Φ_cat P_left P_right S_z
  have h_anti : σx * σz + σz * σx = 0 := hxz
  have h_xz : σx * σz = -(σz * σx) := eq_neg_of_add_eq_zero_left h_anti
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
    simp only [mul_zero, zero_mul]
    simp only [one_mul]
    rw [hQzQplus]
    ext <;> exact Eq.refl _
  · change localObs Qplus Qplus * (localObs 0 1 * diagScalar σz) *
      localObs Qplus (Qminus * σz) = localObs 0 (Qplus + Qplus)
    rw [show diagScalar σz = localObs σz σz from Eq.refl _, localObs_mul, localObs_mul, localObs_mul]
    simp only [mul_zero, zero_mul]
    simp only [one_mul]
    rw [hQzQminus]

-- ============================================================================
-- 3. ARCHETYPES G₀, G₁, G₂: FULL ENTANGLED 2x2 QUASI-PROJECTOR CHANNEL
--    DECOUPLING & WIDOM–HANKEL–TOEPLITZ PRODUCT CANCELLATION
-- ============================================================================

/-- Left spatial corner projector `P_left = [[1, 0], [0, 0]] ∈ Mat2 B`. -/
@[simp] def P_left : Mat2 B := ⟨1, 0, 0, 0⟩

/-- Right spatial corner projector `P_right = [[0, 0], [0, 1]] ∈ Mat2 B`. -/
@[simp] def P_right : Mat2 B := ⟨0, 0, 0, 1⟩

/--
Full non-diagonal entangled pre-selection quasi-projector in `Mat2 B`:
`Ψ_ent(σx, σz) = [[1 + σx, (1 + σx) σz], [σz (1 + σx), 1 - σx]]`.
-/
@[simp] def PsiEnt (σx σz : B) : Mat2 B :=
  ⟨1 + σx, (1 + σx) * σz,
   σz * (1 + σx), 1 - σx⟩

/--
Full non-diagonal entangled post-selection quasi-projector in `Mat2 B`:
`Φ_ent(σx) = [[1 + σx, 1 + σx], [1 + σx, 1 + σx]]`.
-/
@[simp] def PhiEnt (σx : B) : Mat2 B :=
  ⟨1 + σx, 1 + σx,
   1 + σx, 1 + σx⟩

/-- Diagonal pre-selection state `Ψ_diag(σx, σz) = localObs(1 + σx, (1 - σx) σz)`. -/
@[simp] def PsiDiag (σx σz : B) : Mat2 B :=
  localObs (1 + σx) ((1 - σx) * σz)

/-- Diagonal post-selection state `Φ_diag(σx) = localObs(1 + σx, 1 + σx)`. -/
@[simp] def PhiDiag (σx : B) : Mat2 B :=
  localObs (1 + σx) (1 + σx)

/-- Helper lemma: `σz * σx = - (σx * σz)` from `racomm σx σz = 0`. -/
lemma comm_flip_of_anticomm {σx σz : B} (hxz : racomm σx σz = 0) :
    σz * σx = -(σx * σz) := by
  unfold racomm at hxz
  calc σz * σx
    _ = (σx * σz + σz * σx) - σx * σz := by abel
    _ = 0 - σx * σz                   := by rw [hxz]
    _ = -(σx * σz)                    := by abel

/-- Helper lemma for multi-factor products containing `σz * σx`. -/
lemma mul_comm_flip_of_anticomm {σx σz : B} (hxz : racomm σx σz = 0) (Y : B) :
    σz * (σx * Y) = -(σx * (σz * Y)) := by
  rw [← mul_assoc σz σx Y, comm_flip_of_anticomm hxz, neg_mul, mul_assoc]

/-- Helper lemma: `σ * (σ * Y) = Y` when `σ * σ = 1`. -/
lemma sq_left_of_sq_one {σ : B} (h : σ * σ = 1) (Y : B) :
    σ * (σ * Y) = Y := by
  rw [← mul_assoc, h, one_mul]

/--
**Archetype G₀ (`archetype_G0_clifford_intertwining_and_entangled_quasiprojectors`):**
For ANY anticommuting involutions `σx² = 1, σz² = 1, {σx, σz} = 0` in `[Ring B]`:
1. **Peirce Intertwining:** `(1 + σx) * σz = σz * (1 - σx)` and `(1 + σx) * σz * (1 + σx) = 0`.
2. **Entangled Quasi-Projector Idempotency (`Ψ_ent² = 4 Ψ_ent` and `Φ_ent² = 4 Φ_ent`):**
   Both full `2 × 2` entangled matrices `Ψ_ent` and `Φ_ent` satisfy `M * M = 4 • M`.
-/
theorem archetype_G0_clifford_intertwining_and_entangled_quasiprojectors
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Ψ := PsiEnt σx σz
    let Φ := PhiEnt σx
    -- 1. Intertwining of (1 ± σx) by σz and orthogonality of (1 + σx) σz (1 + σx):
    (1 + σx) * σz = σz * (1 - σx) ∧
    (1 + σx) * σz * (1 + σx) = 0 ∧
    (1 + σx) * σz * (1 - σx) * σz = (1 + σx) + (1 + σx) ∧
    -- 2. Full entangled 2x2 matrices Ψ_ent and Φ_ent are exact quasi-projectors:
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
    (dsimp [PsiEnt];
     simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                add_a11, add_a12, add_a21, add_a22,
                mul_add, add_mul, sub_mul, mul_sub,
                mul_one, one_mul, mul_assoc,
                hflip, hflipY, hx, hz, hxY,
                neg_mul, mul_neg, neg_add_rev, neg_neg];
     try abel)
  · ext <;>
    (dsimp [PhiEnt];
     simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                add_a11, add_a12, add_a21, add_a22,
                mul_add, add_mul, mul_one, one_mul, hx];
     try abel)

/--
**Archetype G₁ (`archetype_G1_entangled_corner_channel_decoupling`):**
Proves BOTH the full entangled 2x2 decoupling (`Ψ_ent, Φ_ent`) AND the diagonal decoupling
(`Ψ_diag, Φ_diag`) in `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. **Full Entangled Quasi-Projector Decoupling:**
   - Identity channel is 100% in the Left corner: `Φ_ent * P_left * Ψ_ent = Φ_ent * Ψ_ent` and
     `Φ_ent * P_right * Ψ_ent = 0`.
   - `S_z`-twisted channel is 100% in the Right corner: `Φ_ent * (P_left * S_z) * Ψ_ent = 0` and
     `Φ_ent * (P_right * S_z) * Ψ_ent = Φ_ent * Ψ_ent`.
2. **Diagonal Specialization (`archetype_A5_quantum_cheshire_cat_two_state_decoupling`):**
   - `Φ_diag * P_left * Ψ_diag = localObs (2(1 + σx)) 0` and `Φ_diag * P_right * Ψ_diag = 0`,
   - `Φ_diag * (P_left * S_z) * Ψ_diag = 0` and `Φ_diag * (P_right * S_z) * Ψ_diag = localObs 0 (2(1 + σx))`.
-/
theorem archetype_G1_entangled_corner_channel_decoupling
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Sz     := diagScalar σz
    let Ψ_e    := PsiEnt σx σz
    let Φ_e    := PhiEnt σx
    let Ψ_d    := PsiDiag σx σz
    let Φ_d    := PhiDiag σx
    let twoPiP := (1 + σx) + (1 + σx)
    -- 1. Full Entangled Quasi-Projector Channel Decoupling:
    Φ_e * P_left * Ψ_e         = Φ_e * Ψ_e ∧
    Φ_e * P_right * Ψ_e        = 0 ∧
    Φ_e * (P_left * Sz) * Ψ_e  = 0 ∧
    Φ_e * (P_right * Sz) * Ψ_e = Φ_e * Ψ_e ∧
    -- 2. Diagonal Specialization (matching `archetype_A5_quantum_cheshire_cat_two_state_decoupling`):
    Φ_d * P_left * Ψ_d         = localObs twoPiP 0 ∧
    Φ_d * P_right * Ψ_d        = 0 ∧
    Φ_d * (P_left * Sz) * Ψ_d  = 0 ∧
    Φ_d * (P_right * Sz) * Ψ_d = localObs 0 twoPiP := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hxY := sq_left_of_sq_one hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext <;>
    (dsimp [PsiEnt, PhiEnt, PsiDiag, PhiDiag, P_left, P_right, diagScalar, localObs];
     simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                zero_a11, zero_a12, zero_a21, zero_a22,
                mul_add, add_mul, sub_mul, mul_sub,
                mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
                mul_assoc, hflip, hflipY, hx, hz, hxY,
                mul_neg, neg_add_rev, neg_neg];
     try abel)

/--
**Archetype G₂ (`archetype_G2_widom_hankel_toeplitz_cancellation_of_joint_product`):**
Resolves why the joint product `P_left * (P_right * S_z) = 0` vanishes while both individual
sandwiches equal `Φ_ent * Ψ_ent`:
Splitting across `Φ_ent` (`Φ_ent² = 4 Φ_ent`) and its complementary quasi-projector
`Φ_comp = 4 • 1 - Φ_ent` (`Φ_comp² = 4 Φ_comp`), the non-zero Toeplitz product
`+8 • (Φ_ent * Ψ_ent)` is exactly canceled by the Hankel excursion `-8 • (Φ_ent * Ψ_ent)`
through the orthogonal complement `Φ_comp`.
-/
theorem archetype_G2_widom_hankel_toeplitz_cancellation_of_joint_product
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Sz       := diagScalar σz
    let Ψ        := PsiEnt σx σz
    let Φ        := PhiEnt σx
    let Φ_comp   := (1 + 1 + 1 + 1 : Mat2 B) - Φ
    let overlap4 := (Φ * Ψ) + (Φ * Ψ) + (Φ * Ψ) + (Φ * Ψ)
    let overlap8 := overlap4 + overlap4
    -- 1. Joint operator product vanishes identically:
    P_left * (P_right * Sz) = 0 ∧
    -- 2. Intermediate Toeplitz product is +8 • (Φ_ent * Ψ_ent):
    (Φ * P_left * Φ) * (Φ * (P_right * Sz) * Ψ) = overlap8 ∧
    -- 3. Intermediate Hankel excursion through Φ_comp = 4•1 - Φ_ent is -8 • (Φ_ent * Ψ_ent):
    (Φ * P_left * Φ_comp) * (Φ_comp * (P_right * Sz) * Ψ) = -overlap8 ∧
    -- 4. Their sum cancels to zero:
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
    (dsimp [Sz, Ψ, Φ, overlap8, overlap4, PsiEnt, PhiEnt, P_left, P_right, diagScalar];
     simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                add_a11, add_a12, add_a21, add_a22,
                mul_add, add_mul, mul_sub,
                mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
                mul_assoc, hflip, hflipY, hx, hz, hxY,
                mul_neg, neg_add_rev, neg_neg];
     try abel)
  have hHankel : (Φ * P_left * Φ_comp) * (Φ_comp * (P_right * Sz) * Ψ) = -overlap8 := by
    ext <;>
    (dsimp [Sz, Ψ, Φ, Φ_comp, overlap8, overlap4, PsiEnt, PhiEnt, P_left, P_right, diagScalar, one];
     simp only [mul_a11, mul_a12, mul_a21, mul_a22,
                add_a11, add_a12, add_a21, add_a22,
                sub_a11, sub_a12, sub_a21, sub_a22,
                neg_a11, neg_a12, neg_a21, neg_a22,
                mul_add, add_mul, sub_mul, mul_sub,
                mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
                mul_assoc, hflip, hflipY, hx, hz, hxY,
                mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg];
     try abel)
  refine ⟨by simp only [P_left, P_right, diagScalar]; aharonov_nc_mat2, hToeplitz, hHankel, ?_⟩
  rw [hToeplitz, hHankel]
  exact add_neg_cancel overlap8

-- ============================================================================
-- 3C. REPRESENTATION CONSEQUENCES R₀, R₁, R₃ ≺ R₄ IN `Mat2 B`
-- ============================================================================

/-- Unnormalized Walsh–Hadamard / Cayley reflection `H_Walsh = Ez + Ex = [[1, 1], [1, -1]]`. -/
@[simp] def H_Walsh : Mat2 B := Ez + Ex

/--
**Archetype R₀ (`archetype_R0_minimal_ideal_spinor_reconstruction_and_corner_homomorphism`):**
Proves that every operator `M ∈ Mat2 B` is reconstructed from the single minimal left ideal
`Mat2 B * P_left` via the Weyl sheet flip `Ex`, and that the `P_left` corner intersection
recovers the `(1,1)` expectation value in `B`:
1. `M = M * P_left + (M * Ex * P_left) * Ex`,
2. `P_right = Ex * P_left * Ex`,
3. `(P_left * Y) * M * (X * P_left) = ⟨(Y * M * X).a11, 0, 0, 0⟩`.
-/
theorem archetype_R0_minimal_ideal_spinor_reconstruction_and_corner_homomorphism
    (M X Y : Mat2 B) :
    M = M * P_left + (M * Ex * P_left) * Ex ∧
    (P_right : Mat2 B) = Ex * P_left * Ex ∧
    (P_left * Y) * M * (X * P_left) = ⟨(Y * M * X).a11, 0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp only [P_left, P_right, Ex]
    aharonov_nc_mat2

/--
**Archetype R₁ (`archetype_R1_walsh_hadamard_localization_shift_duality`):**
Proves that the Walsh–Hadamard / Cayley reflection `H_Walsh = Ez + Ex` (`H_Walsh² = 2•1`)
conjugates the diagonal localization generator `Ez` into the off-diagonal Weyl shift `2•Ex`,
conjugates `Ex` into `2•Ez`, inverts the symplectic bivector `Ey`, and maps any diagonal
observable `localObs d₁ d₂` into the sum of a scalar mean and a symmetric off-diagonal shift
`modularShift (d₁ - d₂) (d₁ - d₂)`:
1. `H_Walsh * H_Walsh = 1 + 1`,
2. `H_Walsh * Ez * H_Walsh = Ex + Ex`,
3. `H_Walsh * Ex * H_Walsh = Ez + Ez`,
4. `H_Walsh * Ey * H_Walsh = -(Ey + Ey)`,
5. `H_Walsh * localObs d₁ d₂ * H_Walsh = diagScalar (d₁ + d₂) + modularShift (d₁ - d₂) (d₁ - d₂)`.
-/
theorem archetype_R1_walsh_hadamard_localization_shift_duality (d1 d2 : B) :
    (H_Walsh : Mat2 B) * H_Walsh = 1 + 1 ∧
    (H_Walsh : Mat2 B) * Ez * H_Walsh = Ex + Ex ∧
    (H_Walsh : Mat2 B) * Ex * H_Walsh = Ez + Ez ∧
    (H_Walsh : Mat2 B) * Ey * H_Walsh = -(Ey + Ey) ∧
    H_Walsh * localObs d1 d2 * H_Walsh =
      diagScalar (d1 + d2) + modularShift (d1 - d2) (d1 - d2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [H_Walsh, Ez, Ex, Ey, localObs, diagScalar, modularShift]
    aharonov_nc_mat2

/--
**Archetype R₃ ≺ R₄ (`archetype_R3_R4_morita_signature_split_and_entangled_routing`):**
Combines the Lorentzian `(+V, -V)` signature split between the symmetric bridge
`Φ = modularShift A C` (`Φ² = +V`) and symplectic bridge `J = modularShift A (-C)` (`J² = -V`)
with the orthogonal corner routing of `1` vs. `S_z` between `Φ_ent` and `Ψ_ent`.
-/
theorem archetype_R3_R4_morita_signature_split_and_entangled_routing
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0)
    (A C : B) :
    let Phi   := modularShift A C
    let J     := modularShift A (-C)
    let V     := localObs (A * C) (C * A)
    let Sig   := localObs (A * C) (-(C * A))
    let V4    := (V + V) + (V + V)
    let Sz    := diagScalar σz
    let Psi_e := PsiEnt σx σz
    let Phi_e := PhiEnt σx
    -- 1. R₃: Signature Split (+V vs. -V), Anticommutativity, Dipole & Double Commutator:
    Phi * Phi = V ∧
    J * J = -V ∧
    racomm Phi J = 0 ∧
    rcomm Phi J = -(Sig + Sig) ∧
    -rcomm Phi (rcomm Phi J) = -(V4 * J) ∧
    -- 2. R₄: Orthogonal Corner Routing of `1` vs. `Sz` between `Phi_e` and `Psi_e`:
    Phi_e * P_left * Psi_e         = Phi_e * Psi_e ∧
    Phi_e * P_right * Psi_e        = 0 ∧
    Phi_e * (P_left * Sz) * Psi_e  = 0 ∧
    Phi_e * (P_right * Sz) * Psi_e = Phi_e * Psi_e := by
  have hG1 := archetype_G1_entangled_corner_channel_decoupling hx hz hxz
  refine ⟨?_, ?_, ?_, ?_, ?_, hG1.1, hG1.2.1, hG1.2.2.1, hG1.2.2.2.1⟩ <;>
  · dsimp only [modularShift, localObs, rcomm, racomm]
    aharonov_nc_mat2

/--
**Lineage L₄ (`lineage_L4_widom_kirkwood_dirac_aharonov_toeplitz_hankel_decoupling`):**
Unifies Kirkwood (1933), Dirac (1945), Widom (1976), and Aharonov–Albert–Vaidman (1988/2013):
1. Kirkwood–Dirac trace marginalization: `tr2 (P2 * M * P1) + tr2 ((1 - P2) * M * P1) = tr2 (M * P1)`.
2. Entangled corner routing of `1` vs. `Sz`:
   `Φ * P_left * Ψ = Φ * (P_right * Sz) * Ψ = Φ * Ψ`, while `Φ * P_right * Ψ = 0` and
   `Φ * (P_left * Sz) * Ψ = 0`.
3. Widom Toeplitz–Hankel cancellation of the joint product `P_left * (P_right * Sz) = 0` across
   `Φ` and `Φ_comp = 4 • 1 - Φ`.
-/
theorem lineage_L4_widom_kirkwood_dirac_aharonov_toeplitz_hankel_decoupling
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0)
    (P2 P1 M : Mat2 B) :
    let Sz     := diagScalar σz
    let Ψ      := PsiEnt σx σz
    let Φ      := PhiEnt σx
    let Φ_comp := (1 + 1 + 1 + 1 : Mat2 B) - Φ
    -- 1. Kirkwood-Dirac trace marginalization:
    tr2 (P2 * M * P1) + tr2 ((1 - P2) * M * P1) = tr2 (M * P1) ∧
    -- 2. Entangled corner routing of 1 vs. Sz:
    Φ * P_left * Ψ         = Φ * Ψ ∧
    Φ * P_right * Ψ        = 0 ∧
    Φ * (P_left * Sz) * Ψ  = 0 ∧
    Φ * (P_right * Sz) * Ψ = Φ * Ψ ∧
    -- 3. Widom Toeplitz-Hankel cancellation between Φ and Φ_comp = 4•1 - Φ:
    (Φ * P_left * Φ) * (Φ * (P_right * Sz) * Ψ) +
    (Φ * P_left * Φ_comp) * (Φ_comp * (P_right * Sz) * Ψ) = 0 := by
  have hG1 := archetype_G1_entangled_corner_channel_decoupling hx hz hxz
  have hG2 := archetype_G2_widom_hankel_toeplitz_cancellation_of_joint_product hx hz hxz
  have hKD : tr2 (P2 * M * P1) + tr2 ((1 - P2) * M * P1) = tr2 (M * P1) := by
    dsimp only [tr2]
    aharonov_nc_mat2
  exact ⟨hKD, hG1.1, hG1.2.1, hG1.2.2.1, hG1.2.2.2.1, hG2.2.2.2⟩

-- ============================================================================
-- 3D. THE THREE-IDEMPOTENT BARGMANN–WIDOM–NAMBU CALCULUS N₀ ≺ N₁ ≺ N₂ ≺ N₃ ≺ N₄
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

/--
**Archetype N₀ (`archetype_N0_operator_double_angle_euler_identities`):**
For ANY two idempotents `P₁² = P₁` and `P₂² = P₂` in ANY non-commutative ring `[Ring B]`:
1. `S₁ = Σ₁₂ + D₁₂` and `S₂ = Σ₁₂ - D₁₂`, with `S₁² = 1` and `S₂² = 1`.
2. **Operator Euler Double-Angle Identity (`e^{2iθ} = cos(2θ) + i sin(2θ)`):**
   `S₁ * S₂ = (Σ₁₂² - D₁₂²) + 2 • (D₁₂ * Σ₁₂) = (1 - 2 • D₁₂²) + 2 • [P₁, P₂]`.
3. **Symmetric `cos(2θ)` and Skew `sin(2θ)` Projections:**
   `{S₁, S₂} = 2 • (1 - 2 • D₁₂²)` and `[S₁, S₂] = 4 • [P₁, P₂]`.
-/
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

/--
**Archetype N₁ (`archetype_N1_two_step_davis_reflection_and_widom_hankel_split`):**
For ANY three idempotents `P₁² = P₁, P₂² = P₂, P₃² = P₃` in `[Ring B]`:
1. **Orthogonal Consciousness/Shadow Channel Splitting:**
   `Σ₁₂ * Σ₂₃ = P₁ * P₂ * P₃ + (1 - P₁) * (1 - P₂) * (1 - P₃)` (zero cross-channel mixing).
2. **Widom Toeplitz vs. Hankel Path Projection:**
   - `P₁ * (Σ₁₂ * Σ₂₃) * P₃ = P₁ * P₂ * P₃` (pure Toeplitz path through `P₂`),
   - `P₁ * (Σ₁₃ - Σ₁₂ * Σ₂₃) * P₃ = P₁ * (1 - P₂) * P₃` (pure Hankel excursion through `1 - P₂`).
-/
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

/--
**Archetype N₂ (`archetype_N2_three_step_bargmann_holonomy_and_linear_reduction`):**
For ANY three idempotents `P₁² = P₁, P₂² = P₂, P₃² = P₃` in `[Ring B]`:
1. **Conscious-Minus-Shadow Loop Decomposition:**
   `B₁₂₃ = Σ₁₂ * Σ₂₃ * Σ₃₁ = P₁ P₂ P₃ P₁ - (1 - P₁)(1 - P₂)(1 - P₃)(1 - P₁)`.
2. **Exact Centrality at the Base Vertex `P₁`:**
   `[B₁₂₃, P₁] = 0` and `P₁ * B₁₂₃ = P₁ * P₂ * P₃ * P₁`.
3. **Cancellation of 4th-Degree Terms in the Orientation Curvature `B₁₂₃ - B₁₃₂`:**
   `B₁₂₃ - B₁₃₂ = P₁ * [P₂, P₃] * P₁ - (1 - P₁) * [P₂, P₃] * (1 - P₁) = {P₁, [P₂, P₃]} - [P₂, P₃]`.
-/
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

/--
**Archetype N₃ (`archetype_N3_bargmann_nambu_ternary_curvature_theorem`):**
**The Bargmann–Nambu Theorem:**
For ANY three idempotents `P₁² = P₁, P₂² = P₂, P₃² = P₃` in ANY non-commutative ring `[Ring B]`:
1. The boundary commutator sum `[P₁, P₂] + [P₂, P₃] + [P₃, P₁]` equals the chordal difference
   commutator `[D₁₂, D₂₃] = [P₁ - P₂, P₂ - P₃]`.
2. Summing the Bargmann orientation curvature `B_{ijk} - B_{ikj}` cyclically over all three
   vertices `(1, 2, 3) + (2, 3, 1) + (3, 1, 2)` yields twice **Yoichiro Nambu's Ternary Bracket**
   `2 • [P₁, P₂, P₃]_Nambu` minus the boundary commutator sum `[D₁₂, D₂₃]`:
   `(B₁₂₃ - B₁₃₂) + (B₂₃₁ - B₂₁₃) + (B₃₁₂ - B₃₂₁) + [D₁₂, D₂₃] = 2 • [P₁, P₂, P₃]_Nambu`.
-/
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

/--
**Archetype N₄ (`archetype_N4_idempotent_triangle_generates_bimetric_dipole`):**
Over ANY non-commutative ring `[Ring B]` and ANY `a, c ∈ B`:
1. `idem1`, `idem2 a`, and `idem3 c` are exact idempotents in `Mat2 B` (requiring no division by 2).
2. Clockwise 3-reflection Bargmann holonomy `B₁₂₃ = localObs (a * c) 0` and counterclockwise
   holonomy `B₁₃₂ = localObs 0 (-(c * a))`.
3. **Symmetric Sum IS the Bimetric Dipole `localObs (a * c) (-(c * a))` and Orientation Difference IS `localObs (a * c) (c * a)`:**
   `B₁₂₃ + B₁₃₂ = localObs (a * c) (-(c * a))` and
   `B₁₂₃ - B₁₃₂ = localObs (a * c) (c * a)`.
4. **Nambu 3-Bracket of the Idempotent Triangle:**
   `nambu3 idem1 (idem2 a) (idem3 c) = ⟨a * c + a * c, a, 0, c * a⟩`.
-/
theorem archetype_N4_idempotent_triangle_generates_bimetric_dipole (a c : B) :
    let P1 := (idem1 : Mat2 B)
    let P2 := idem2 a
    let P3 := idem3 c
    P1 * P1 = P1 ∧
    P2 * P2 = P2 ∧
    P3 * P3 = P3 ∧
    bargmannHolonomy P1 P2 P3 = localObs (a * c) 0 ∧
    bargmannHolonomy P1 P3 P2 = localObs 0 (-(c * a)) ∧
    bargmannHolonomy P1 P2 P3 + bargmannHolonomy P1 P3 P2 = localObs (a * c) (-(c * a)) ∧
    bargmannHolonomy P1 P2 P3 - bargmannHolonomy P1 P3 P2 = localObs (a * c) (c * a) ∧
    nambu3 P1 P2 P3 = ⟨a * c + a * c, a, 0, c * a⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [bargmannHolonomy, davisSigma, nambu3, idem1, idem2, idem3, localObs]
    aharonov_nc_mat2

-- ============================================================================
-- 3E. CHIRAL MODULAR GENESIS OF THE QUANTUM CHESHIRE CAT, BOHM MASS–SPIN
--     TRANSDUCTION & CHIRAL GAUGE VALVE C₀ ≺ C₁ ≺ C₂ ≺ C₃ ≺ C₄
-- ============================================================================

/-- Upper chiral nilpotent `chiralNPlus(σz) = [[0, σz], [0, 0]]` in `Mat2 B`. -/
@[simp] def chiralNPlus (σz : B) : Mat2 B := ⟨0, σz, 0, 0⟩

/-- Lower chiral nilpotent `chiralNMinus = [[0, 0], [1, 0]]` in `Mat2 B`. -/
@[simp] def chiralNMinus : Mat2 B := ⟨0, 0, 1, 0⟩

/-- Chiral modular shift `chiralPhi(σz) = [[0, σz], [1, 0]]` in `Mat2 B`. -/
@[simp] def chiralPhi (σz : B) : Mat2 B := modularShift σz 1

/-- Inter-sheet mass/presence dipole `massDipole = P_left - P_right = [[1, 0], [0, -1]]`. -/
@[simp] def massDipole : Mat2 B := ⟨1, 0, 0, -1⟩

/-- Inter-sheet spin dipole `spinDipole(σz) = (P_left - P_right) * diagScalar σz = [[σz, 0], [0, -σz]]`. -/
@[simp] def spinDipole (σz : B) : Mat2 B := ⟨σz, 0, 0, -σz⟩

/-- Bohm double-commutator curvature `bohmCurvature(Φ, Z) = -[Φ, [Φ, Z]]` in `Mat2 B`. -/
@[simp] def bohmCurvature (Φ Z : Mat2 B) : Mat2 B := -rcomm Φ (rcomm Φ Z)

macro "chiral_mat2" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
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
                  mul_assoc, $hs,*]
       try abel))

/--
**Archetype C₀ (`archetype_C0_chiral_modular_shift_bimetric_spin_identity`):**
For ANY involution `σz² = 1` in `[Ring B]`, the chiral modular shift `Φc = [[0, σz], [1, 0]] = Np + Nm` satisfies:
1. Upper bimetric sheet metric `Np * Nm = P_left * diagScalar σz` (Left-arm spin),
2. Lower bimetric sheet metric `Nm * Np = P_right * diagScalar σz` (Right-arm spin),
3. Bimetric dipole `Np * Nm - Nm * Np = spinDipole σz`,
4. Total bimetric metric `Φc * Φc = diagScalar σz` (global spin operator),
5. Fourth-power identity `(Φc * Φc) * (Φc * Φc) = 1` (this does not assert exact order four).
-/
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [chiralNPlus, chiralNMinus, chiralPhi, modularShift, P_left, P_right, diagScalar, spinDipole]
    chiral_mat2 [hz]

/--
**Archetype C₁ (`archetype_C1_cheshire_cat_chiral_intertwiner_genesis`):**
For ANY anticommuting involutions `σx² = 1, σz² = 1, {σx, σz} = 0` in `[Ring B]`:
1. **Diagonal Cheshire Cat Intertwiner Genesis:**
   `Φc * PsiDiag σx σz * Ex = PhiDiag σx` and `diagScalar σz * Φc * PhiDiag σx * Ex = PsiDiag σx σz`.
2. **Full Entangled 2×2 Quasi-Projector Intertwiner Genesis:**
   For `Φc_inv = Ex * Φc * Ex = [[0, 1], [σz, 0]]`, `Φc * Φc_inv = 1`,
   `Φc * PsiEnt σx σz * Φc_inv = PhiEnt σx`, and `Φc_inv * PhiEnt σx * Φc = PsiEnt σx σz`!
-/
theorem archetype_C1_cheshire_cat_chiral_intertwiner_genesis
    {σx σz : B} (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Φc := chiralPhi σz
    let Φc_inv := Ex * Φc * Ex
    let Sz := diagScalar σz
    let Ψ_d := PsiDiag σx σz
    let Φ_d := PhiDiag σx
    let Ψ_e := PsiEnt σx σz
    let Φ_e := PhiEnt σx
    Φc * Φc_inv = 1 ∧
    Φc * Ψ_d * Ex = Φ_d ∧
    Sz * Φc * Φ_d * Ex = Ψ_d ∧
    Φc * Ψ_e * Φc_inv = Φ_e ∧
    Φc_inv * Φ_e * Φc = Ψ_e := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hzY := sq_left_of_sq_one hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [chiralPhi, modularShift, PsiDiag, PhiDiag, PsiEnt, PhiEnt,
                localObs, diagScalar, Ex]
    chiral_mat2 [hflip, hflipY, hz, hzY]

/--
**Archetype C₂ (`archetype_C2_bohm_curvature_transduces_mass_and_spin_dipoles`):**
Under the chiral modular shift `Φc = [[0, σz], [1, 0]]` with `σz² = 1`:
1. The Bohm double-commutator curvature transduces the Mass Dipole `Dm = Ez = P_left - P_right`
   into `-4` times the Spin Dipole `Ds = spinDipole σz = (P_left - P_right) * Sz`:
   `-[Φc, [Φc, Dm]] = -4 • Ds`.
2. Conversely, the Bohm curvature of `Ds` is `-4` times `Dm`:
   `-[Φc, [Φc, Ds]] = -4 • Dm`.
3. Consequently, the 4th-order Bohm bi-curvature satisfies the eigenvalue identity
   `-[Φc, [Φc, -[Φc, [Φc, Dm]]]] = 16 • Dm`.
-/
theorem archetype_C2_bohm_curvature_transduces_mass_and_spin_dipoles
    {σz : B} (hz : σz * σz = 1) :
    let Φc := chiralPhi σz
    let Dm := (Ez : Mat2 B)
    let Ds := spinDipole σz
    let Ds4 := (Ds + Ds) + (Ds + Ds)
    let Dm4 := (Dm + Dm) + (Dm + Dm)
    let Dm16 := (Dm4 + Dm4) + (Dm4 + Dm4)
    bohmCurvature Φc Dm = -Ds4 ∧
    bohmCurvature Φc Ds = -Dm4 ∧
    bohmCurvature Φc (bohmCurvature Φc Dm) = Dm16 := by
  have hzY := sq_left_of_sq_one hz
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp only [bohmCurvature, rcomm, chiralPhi, modularShift, Ez, spinDipole]
    chiral_mat2 [hz, hzY]

/--
General two-state response to an arbitrary off-diagonal operator link.  The two
matrix entries remain ordered products in `B`; no commutation or parity
assumption on either link is used.  This is the channel formula specialized by
`archetype_C3` below.
-/
theorem cheshire_modular_sandwich_channel_formula (σx σz u v : B) :
    PhiDiag σx * modularShift u v * PsiDiag σx σz =
      modularShift ((1 + σx) * u * ((1 - σx) * σz))
                   ((1 + σx) * v * (1 + σx)) := by
  dsimp only [PhiDiag, PsiDiag, localObs, modularShift]
  aharonov_nc_mat2

/-- Exact noncommutative vanishing criterion for the two-state link sandwich.
The right factor `σz` in the first channel is cancellable under `σz² = 1`;
the two channels then vanish independently, with their multiplication order
retained in `B`. -/
theorem cheshire_modular_sandwich_eq_zero_iff
    (σx σz u v : B) (hz : σz * σz = 1) :
    PhiDiag σx * modularShift u v * PsiDiag σx σz = 0 ↔
      (1 + σx) * u * (1 - σx) = 0 ∧
      (1 + σx) * v * (1 + σx) = 0 := by
  rw [cheshire_modular_sandwich_channel_formula]
  constructor
  · intro h
    constructor
    · have h12 : (1 + σx) * u * ((1 - σx) * σz) = 0 := by
        (simpa only [modularShift, zero_a12] using congrArg Mat2.a12 h)
      have hcancel :
          ((1 + σx) * u * ((1 - σx) * σz)) * σz = 0 := by
        (simpa using congrArg (fun z : B => z * σz) h12)
      calc
        (1 + σx) * u * (1 - σx) =
            (1 + σx) * u * ((1 - σx) * (σz * σz)) := by rw [hz, mul_one]
        _ = ((1 + σx) * u * ((1 - σx) * σz)) * σz := by noncomm_ring
        _ = 0 := hcancel
    · simpa only [modularShift, zero_a21] using congrArg Mat2.a21 h
  · rintro ⟨hu, hv⟩
    have hu' : (1 + σx) * u * ((1 - σx) * σz) = 0 := by
      calc
        (1 + σx) * u * ((1 - σx) * σz) =
            ((1 + σx) * u * (1 - σx)) * σz := by noncomm_ring
        _ = 0 := by rw [hu]; simp
    ext <;> simp [modularShift, hu', hv]

/--
**Archetype C₃ (`archetype_C3_cheshire_cat_chiral_modular_valve`):**
**The Non-Reciprocal Chiral Cheshire Cat Gauge Valve:**
For any `σx² = 1, σz² = 1, {σx, σz} = 0` and any gauge link `w ∈ B` commuting with `σx` (`[w, σx] = 0`):
1. **Parity-Even Link `modularShift w w`:**
   The `(1,2)` entry is zero and the `(2,1)` entry is `2 w (1 + σx)`.
2. **Parity-Odd Link `modularShift (w * σz) (w * σz)`:**
   The `(2,1)` entry is zero and the `(1,2)` entry is `2 w (1 + σx)`.
The stated surviving entry may itself be zero in the given ring; no nonzero transport
claim follows from this theorem.
-/
theorem archetype_C3_cheshire_cat_chiral_modular_valve
    {σx σz w : B} (hx : σx * σx = 1) (hz : σz * σz = 1)
    (hxz : racomm σx σz = 0) (hw : rcomm w σx = 0) :
    let Ψ := PsiDiag σx σz
    let Φ := PhiDiag σx
    let Teven := modularShift w w
    let Todd  := modularShift (w * σz) (w * σz)
    let wP    := w * (1 + σx)
    let twoWP := wP + wP
    Φ * Teven * Ψ = modularShift 0 twoWP ∧
    Φ * Todd * Ψ  = modularShift twoWP 0 := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hxY := sq_left_of_sq_one hx
  have hzY := sq_left_of_sq_one hz
  have hw_flip : σx * w = w * σx := (sub_eq_zero.mp hw).symm
  have hw_flipY (Y : B) : σx * (w * Y) = w * (σx * Y) := by
    rw [← mul_assoc, hw_flip, mul_assoc]
  have hgeneral_even := cheshire_modular_sandwich_channel_formula σx σz w w
  have hgeneral_odd := cheshire_modular_sandwich_channel_formula σx σz (w * σz) (w * σz)
  refine ⟨?_, ?_⟩
  · rw [hgeneral_even]
    dsimp only [modularShift]
    chiral_mat2 [hflip, hflipY, hx, hxY, hz, hzY, hw_flip, hw_flipY]
  · rw [hgeneral_odd]
    dsimp only [modularShift]
    chiral_mat2 [hflip, hflipY, hx, hxY, hz, hzY, hw_flip, hw_flipY]

/-! ### C₃′: full-entangled response to parity-even and parity-odd links -/

/-- Exact channel expansion for the full non-diagonal entangled boundary matrices.
No involution, commutation, or parity hypotheses are needed. -/
theorem entangled_modular_sandwich_channel_formula (σx σz u v : B) :
    PhiEnt σx * modularShift u v * PsiEnt σx σz =
      ⟨(1 + σx) * v * (1 + σx) + (1 + σx) * u * σz * (1 + σx),
       (1 + σx) * v * (1 + σx) * σz + (1 + σx) * u * (1 - σx),
       (1 + σx) * v * (1 + σx) + (1 + σx) * u * σz * (1 + σx),
       (1 + σx) * v * (1 + σx) * σz + (1 + σx) * u * (1 - σx)⟩ := by
  dsimp only [PhiEnt, PsiEnt, modularShift]
  aharonov_nc_mat2

/-- In the full-entangled boundary model, parity-even and parity-odd links give
the same exact response matrix. This is an operator identity and does not assert
that the common response is nonzero in every ring. -/
theorem archetype_C3_full_entangled_link_parity_blindness
    {σx σz w : B} (hx : σx * σx = 1) (hz : σz * σz = 1)
    (hxz : racomm σx σz = 0) (hw : rcomm w σx = 0) :
    let q := 1 + σx
    let response := (⟨(w * q) + (w * q),
                     (w * q * σz) + (w * q * σz),
                     (w * q) + (w * q),
                     (w * q * σz) + (w * q * σz)⟩ : Mat2 B)
    PhiEnt σx * modularShift w w * PsiEnt σx σz = response ∧
    PhiEnt σx * modularShift (w * σz) (w * σz) * PsiEnt σx σz = response := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hxY := sq_left_of_sq_one hx
  have hzY := sq_left_of_sq_one hz
  have hw_flip : σx * w = w * σx := (sub_eq_zero.mp hw).symm
  have hw_flipY (Y : B) : σx * (w * Y) = w * (σx * Y) := by
    rw [← mul_assoc, hw_flip, mul_assoc]
  have heven := entangled_modular_sandwich_channel_formula σx σz w w
  have hodd := entangled_modular_sandwich_channel_formula σx σz (w * σz) (w * σz)
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [heven]
    chiral_mat2 [hflip, hflipY, hx, hxY, hz, hzY, hw_flip, hw_flipY]
  · rw [hodd]
    chiral_mat2 [hflip, hflipY, hx, hxY, hz, hzY, hw_flip, hw_flipY]

/--
**Archetype C₄ (`archetype_C4_cheshire_cat_sheet_exchange_swaps_cat_and_grin`):**
Conjugating `PsiDiag σx σz` by the sheet-exchange involution `Ex` (`Ψswap = Ex * PsiDiag σx σz * Ex`)
swaps the localization of particle presence and spin `Sz = diagScalar σz` between the Left and Right arms:
1. `PhiDiag σx * P_left * Ψswap = 0` (Left arm is empty),
2. `PhiDiag σx * P_right * Ψswap = localObs 0 ((1 + σx) + (1 + σx))` (presence is in the Right arm),
3. `PhiDiag σx * (P_left * Sz) * Ψswap = localObs ((1 + σx) + (1 + σx)) 0` (spin is in the Left arm),
4. `PhiDiag σx * (P_right * Sz) * Ψswap = 0` (Right arm has zero spin).
-/
theorem archetype_C4_cheshire_cat_sheet_exchange_swaps_cat_and_grin
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1) (hxz : racomm σx σz = 0) :
    let Ψswap := Ex * PsiDiag σx σz * Ex
    let Φ     := PhiDiag σx
    let Sz    := diagScalar σz
    let twoP  := (1 + σx) + (1 + σx)
    Φ * P_left * Ψswap = 0 ∧
    Φ * P_right * Ψswap = localObs 0 twoP ∧
    Φ * (P_left * Sz) * Ψswap = localObs twoP 0 ∧
    Φ * (P_right * Sz) * Ψswap = 0 := by
  have hflip := comm_flip_of_anticomm hxz
  have hflipY := mul_comm_flip_of_anticomm hxz
  have hxY := sq_left_of_sq_one hx
  have hzY := sq_left_of_sq_one hz
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [PhiDiag, PsiDiag, localObs, diagScalar, P_left, P_right, Ex]
    chiral_mat2 [hflip, hflipY, hx, hxY, hz, hzY]

/--
**Archetype C₅ (`archetype_C5_cheshire_cat_bargmann_berry_holonomy_generates_spin_dipole_and_grin`):**
**The 3-Idempotent Bargmann–Berry Phase of the Quantum Cheshire Cat ($\mathcal{N}_0\text{–}\mathcal{N}_4 \bowtie \mathcal{C}_0\text{–}\mathcal{C}_4$):**
For ANY `σx, σz ∈ B` with `σx * σx = 1`, `σz * σz = 1`, and `racomm σx σz = 0`, consider the
division-free 3-idempotent triangle `P1 = idem1 = P_left`, `P2 = idem2 σz = [[1, σz], [0, 0]]`,
and `P3 = idem3 1 = [[0, 0], [1, 1]]`:
1. **Off-Diagonal Reconstruction of the Chiral Modular Shift:**
   `(P2 - P1) + (P3 - P_right) = chiralPhi σz`.
2. **Forward & Backward 3-Step Bargmann Holonomies Separate Left and Right Arm Spin:**
   `bargmannHolonomy P1 P2 P3 = P_left * diagScalar σz` (`= chiralNPlus σz * chiralNMinus`) and
   `bargmannHolonomy P1 P3 P2 = -(P_right * diagScalar σz)` (`= -(chiralNMinus * chiralNPlus σz)`).
3. **Symmetric & Antisymmetric Bargmann Holonomy Combinations:**
   `bargmannHolonomy P1 P2 P3 + bargmannHolonomy P1 P3 P2 = spinDipole σz` and
   `bargmannHolonomy P1 P2 P3 - bargmannHolonomy P1 P3 P2 = diagScalar σz = chiralPhi σz * chiralPhi σz`.
4. **Cheshire Cat Sandwich of the Bargmann Holonomy (Disembodied Grin = Reversed Holonomy):**
   In the Cheshire Cat two-state sandwich between `PhiDiag σx` and `PsiDiag σx σz`, the forward
   Bargmann holonomy vanishes identically (`PhiDiag σx * bargmannHolonomy P1 P2 P3 * PsiDiag σx σz = 0`),
   whereas the reversed Bargmann holonomy `-bargmannHolonomy P1 P3 P2` carries the entire disembodied
   Right-arm spin `localObs 0 (2(1 + σx))`!
-/
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
  · dsimp only [idem1, idem2, idem3, bargmannHolonomy, davisSigma,
                P_left, P_right, chiralPhi, modularShift, diagScalar, spinDipole,
                PhiDiag, PsiDiag, localObs]
    chiral_mat2 [hflip, hflipY, hx, hxY, hz, hzY]

/--
**Archetype C₆ (`archetype_C6_bohm_curvature_is_bargmann_holonomy_sum`):**
For anticommuting involutions `σx` and `σz`, the C₂ curvature law and C₅ triangle
law identify the mass-dipole curvature output with four negative copies of the
sum of the two oriented idempotent-triangle holonomies. This is an operator
identity in `Mat2 B`; it asserts no nonzero transport or physical interpretation.
-/
theorem archetype_C6_bohm_curvature_is_bargmann_holonomy_sum
    {σz : B} (hz : σz * σz = 1) :
    let P1 := idem1 (B := B)
    let P2 := idem2 σz
    let P3 := idem3 (1 : B)
    let B123 := bargmannHolonomy P1 P2 P3
    let B132 := bargmannHolonomy P1 P3 P2
    let H := B123 + B132
    bohmCurvature (chiralPhi σz) (Ez : Mat2 B) =
      -(((H + H) + (H + H))) := by
  have hcurv := archetype_C2_bohm_curvature_transduces_mass_and_spin_dipoles hz
  have htriangle := archetype_N4_idempotent_triangle_generates_bimetric_dipole σz (1 : B)
  have hsum : bargmannHolonomy (idem1 (B := B)) (idem2 σz) (idem3 (1 : B)) +
      bargmannHolonomy (idem1 (B := B)) (idem3 (1 : B)) (idem2 σz) = spinDipole σz := by
    (simpa [spinDipole, localObs] using htriangle.2.2.2.2.2.1)
  rw [hcurv.1, ← hsum]

-- ============================================================================
-- 4. FAITHFUL NONCOMMUTATIVE OPERATOR TRANSPORT TO `BimetricSheetGeometry`
-- ============================================================================

/-! ### C₇: the closed chiral curvature formula -/

/-- For an involution `σz`, the double commutator with `chiralPhi σz` acts on
every block operator `Z` by the ordered expression `2 Φ Z Φ - Sz Z - Z Sz`,
where `Sz = Φ²`. There are no diagonal or commutation assumptions on `Z`. -/
theorem archetype_C7_chiral_curvature_closed_formula
    {σz : B} (hz : σz * σz = 1) (Z : Mat2 B) :
    bohmCurvature (chiralPhi σz) Z =
      (chiralPhi σz * Z * chiralPhi σz + chiralPhi σz * Z * chiralPhi σz) -
        (diagScalar σz * Z + Z * diagScalar σz) := by
  have hsq : chiralPhi σz * chiralPhi σz = diagScalar σz := by
    exact (archetype_C0_chiral_modular_shift_bimetric_spin_identity hz).2.2.2.1
  calc
    bohmCurvature (chiralPhi σz) Z =
        (chiralPhi σz * Z * chiralPhi σz + chiralPhi σz * Z * chiralPhi σz) -
          (chiralPhi σz * chiralPhi σz * Z + Z * (chiralPhi σz * chiralPhi σz)) := by
          (simp only [bohmCurvature, rcomm, mul_sub, sub_mul, mul_assoc,
            neg_sub])
          abel
    _ = (chiralPhi σz * Z * chiralPhi σz + chiralPhi σz * Z * chiralPhi σz) -
          (diagScalar σz * Z + Z * diagScalar σz) := by rw [hsq]

/-- Coordinate realization of this module's block operators in the bimetric owner. -/
@[simp] def toBimetricMat2 (M : Mat2 B) : NonCommutativeBimetricSheetGeometry.Mat2 B :=
  ⟨M.a11, M.a12, M.a21, M.a22⟩

omit [Ring B] in
/-- Injectivity of the coordinate realization `toBimetricMat2`. -/
theorem toBimetricMat2_injective (M N : Mat2 B) :
    toBimetricMat2 M = toBimetricMat2 N → M = N := by
  intro h
  cases M with
  | mk a11 a12 a21 a22 =>
    cases N with
    | mk b11 b12 b21 b22 =>
      cases h
      rfl

/-- Multiplicativity of the coordinate realization `toBimetricMat2`. -/
theorem toBimetricMat2_mul (M N : Mat2 B) :
    toBimetricMat2 (M * N) = toBimetricMat2 M * toBimetricMat2 N := by
  cases M with
  | mk a11 a12 a21 a22 =>
    cases N with
    | mk b11 b12 b21 b22 =>
      rfl

/-- Composition of modular shifts under `toBimetricMat2`. -/
theorem toBimetricMat2_modularShift_comp (a b c d : B) :
    toBimetricMat2 (modularShift a b * modularShift c d) =
      NonCommutativeBimetricSheetGeometry.Mat2.matPhi a b *
        NonCommutativeBimetricSheetGeometry.Mat2.matPhi c d := by
  rw [toBimetricMat2_mul]
  rfl

set_option linter.unusedSimpArgs false in
/-- Square of a modular shift under `toBimetricMat2`. -/
theorem toBimetricMat2_modularShift_square (a c : B) :
    toBimetricMat2 (modularShift a c * modularShift a c) =
      NonCommutativeBimetricSheetGeometry.Mat2.matV a c := by
  rw [toBimetricMat2_modularShift_comp]
  ext <;>
    simp [NonCommutativeBimetricSheetGeometry.Mat2.matPhi,
      NonCommutativeBimetricSheetGeometry.Mat2.matV]

end Mat2
end NonCommutativeTwoStateAndModularShift
