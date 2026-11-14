/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis
import InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis

/-!
# Normed $\star$-Completion of $\mathcal{C}\ell_\infty(A)$, Hodge–Parabolic Lindblad Bridge & Contraction

This module unifies the inductive colimit quotient $\mathcal{C}\ell_\infty(A)$ and Metriplectic
Lindblad mass-gap damping (`NoncommutativeCliffordColimitMassGapSynthesis`) with the all-scales
Hodge–Parabolic nilpotent tower (`NoncommutativeHodgeParabolicTowerSynthesis`):

1. **Algebraic & Normed $\star$-Completion of $\mathcal{C}\ell_\infty(A)$**:
   Equips `ClTower A n` with the recursive conjugate-transpose $\star$-ring structure, proves
   `bottEmbed` and `bottEmbedIter` preserve `+`, `0`, `-`, `*`, and `star`, lifts the
   non-unital $\star$-ring operations and recursive block-supremum norm `towerNorm` onto the
   quotient `ClInf A`, proves `ClInf A` is a `NormedAddCommGroup` and `NonUnitalRing`, and
   establishes `UniformSpace.Completion (ClInf A)` as its isometric Cauchy completion.
2. **Hodge–Parabolic $\leftrightarrow$ Lindblad & Supertrace Bridge**:
   Connects the $k$-step Hodge–Parabolic monodromy $(Q_{\mathrm{Hodge}}^{(n+1)})^k$ to
   `clInfSuperTrace` and `lindbladDissipator (massGapOp m₀ (n + 1))`, distinguishing the
   coexact diagonal vacuum evacuation (decoherence-free for central mass $m_0$) from the
   off-diagonal parabolic transition coherence (quadratic damping $-m_0^2$).
3. **Normed Lindblad Euler-Step Contraction & Mass-Gap Decay**:
   Over `[NormedRing A] [NormedAlgebra ℝ A]`, proves that on transition coherences
   $\Psi_{\mathrm{coh}}$ the Euler Lindblad step contracts the `clInfNorm` (and its
   `UniformSpace.Completion` norm) by exact factor $(1 - t m_0^2)$ while preserving the
   Cantor vacuum $\Pi_{\mathcal{C}_n}$.
-/

namespace InfoGeometry.Algebra.NoncommutativeColimitNormedLindbladBridge

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis

universe u

/-!
## Part 1: Recursive $\star$-Structure, Quotient Non-Unital $\star$-Ring & Normed Completion of `ClInf A`
-/

section AlgebraicAndNormedCompletion

section RingOperations

variable {A : Type u} [Ring A]

lemma bottEmbed_zero (n : ℕ) : bottEmbed (0 : ClTower A n) = 0 := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbed_add (n : ℕ) (X Y : ClTower A n) :
    bottEmbed (X + Y) = bottEmbed X + bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbed_neg (n : ℕ) (X : ClTower A n) :
    bottEmbed (-X) = -bottEmbed X := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbed_sub (n : ℕ) (X Y : ClTower A n) :
    bottEmbed (X - Y) = bottEmbed X - bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed, sub_eq_add_neg]

lemma bottEmbedIter_zero {n : ℕ} (k : ℕ) :
    bottEmbedIter k (0 : ClTower A n) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => dsimp [bottEmbedIter]; rw [ih, bottEmbed_zero]

lemma bottEmbedIter_add {n : ℕ} (k : ℕ) (X Y : ClTower A n) :
    bottEmbedIter k (X + Y) = bottEmbedIter k X + bottEmbedIter k Y := by
  induction k with
  | zero => rfl
  | succ k ih => dsimp [bottEmbedIter]; rw [ih, bottEmbed_add]

lemma bottEmbedIter_neg {n : ℕ} (k : ℕ) (X : ClTower A n) :
    bottEmbedIter k (-X) = -bottEmbedIter k X := by
  induction k with
  | zero => rfl
  | succ k ih => dsimp [bottEmbedIter]; rw [ih, bottEmbed_neg]

lemma bottEmbedIter_mul {n : ℕ} (k : ℕ) (X Y : ClTower A n) :
    bottEmbedIter k (X * Y) = bottEmbedIter k X * bottEmbedIter k Y := by
  induction k with
  | zero => rfl
  | succ k ih => dsimp [bottEmbedIter]; rw [ih, bottEmbed_mul]

/-- Cast across equal tower levels. -/
def castTower {m n : ℕ} (h : m = n) (X : ClTower A m) : ClTower A n :=
  h ▸ X

omit [Ring A] in
lemma castTower_rfl {n : ℕ} (X : ClTower A n) : castTower rfl X = X := rfl

omit [Ring A] in
lemma castTower_heq {m n : ℕ} (h : m = n) (X : ClTower A m) :
    HEq (castTower h X) X := by
  subst h; rfl

lemma castTower_add {m n : ℕ} (h : m = n) (X Y : ClTower A m) :
    castTower h (X + Y) = castTower h X + castTower h Y := by
  subst h; rfl

lemma castTower_mul {m n : ℕ} (h : m = n) (X Y : ClTower A m) :
    castTower h (X * Y) = castTower h X * castTower h Y := by
  subst h; rfl

lemma bottEmbedIter_castTower {m n : ℕ} (h : m = n) (k : ℕ) (X : ClTower A m) :
    bottEmbedIter k (castTower h X) =
      castTower (congrArg (· + k) h) (bottEmbedIter k X) := by
  subst h; rfl

omit [Ring A] in
lemma eq_of_heq_tower {m n : ℕ} (h : m = n) {X : ClTower A m} {Y : ClTower A n}
    (heq : HEq X Y) : castTower h X = Y := by
  subst h; exact eq_of_heq heq

lemma toClInf_eq_of_heq {m n : ℕ} (h : m = n) {X : ClTower A m} {Y : ClTower A n}
    (heq : HEq X Y) : toClInf m X = toClInf n Y := by
  subst h; cases eq_of_heq heq; rfl

lemma toClInf_castTower {m n : ℕ} (h : m = n) (X : ClTower A m) :
    toClInf n (castTower h X) = toClInf m X := by
  subst h; rfl

lemma toClInf_bottEmbedIter {n : ℕ} (k : ℕ) (X : ClTower A n) :
    toClInf (n + k) (bottEmbedIter k X) = toClInf n X := by
  apply Quotient.sound
  exact ⟨0, k, rfl, HEq.rfl⟩

private lemma bottEmbedIter_split_heq {n k₁ k₂ k : ℕ} (X : ClTower A n)
    (h : k₁ + k₂ = k) :
    HEq (bottEmbedIter k₂ (bottEmbedIter k₁ X)) (bottEmbedIter k X) := by
  refine HEq.trans (bottEmbedIter_add_heq k₁ k₂ X).symm ?_
  subst h; rfl

private lemma bottEmbedIter_congr_heq_dim {m₁ m₂ : ℕ} (d₁ d₂ : ℕ)
    {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (hd : d₁ = d₂) (h_heq : HEq X Y) :
    HEq (bottEmbedIter d₁ X) (bottEmbedIter d₂ Y) := by
  subst hd
  exact bottEmbedIter_congr_heq d₁ h_dim h_heq

private lemma toClInf_binop_stabilize
    (op : ∀ n : ℕ, ClTower A n → ClTower A n → ClTower A n)
    (h_emb : ∀ (n k : ℕ) (X Y : ClTower A n),
      bottEmbedIter k (op n X Y) = op (n + k) (bottEmbedIter k X) (bottEmbedIter k Y))
    (h_cast : ∀ {m n : ℕ} (h : m = n) (X Y : ClTower A m),
      castTower h (op m X Y) = op n (castTower h X) (castTower h Y))
    (u v : Σ n : ℕ, ClTower A n) {M N : ℕ}
    (huM : u.1 ≤ M) (hvM : v.1 ≤ M) (hMN : M ≤ N) :
    toClInf M
      (op M (castTower (Nat.add_sub_cancel' huM) (bottEmbedIter (M - u.1) u.2))
            (castTower (Nat.add_sub_cancel' hvM) (bottEmbedIter (M - v.1) v.2))) =
    toClInf N
      (op N (castTower (Nat.add_sub_cancel' (le_trans huM hMN)) (bottEmbedIter (N - u.1) u.2))
            (castTower (Nat.add_sub_cancel' (le_trans hvM hMN)) (bottEmbedIter (N - v.1) v.2))) := by
  rw [← toClInf_bottEmbedIter (N - M), h_emb]
  have h_dim : M + (N - M) = N := Nat.add_sub_cancel' hMN
  rw [← toClInf_castTower h_dim, h_cast h_dim]
  congr 2
  · apply eq_of_heq_tower rfl
    refine HEq.trans (castTower_heq _ _) ?_
    rw [bottEmbedIter_castTower]
    refine HEq.trans (castTower_heq _ _) ?_
    refine HEq.trans (bottEmbedIter_split_heq u.2 (by omega)) (castTower_heq _ _).symm
  · apply eq_of_heq_tower rfl
    refine HEq.trans (castTower_heq _ _) ?_
    rw [bottEmbedIter_castTower]
    refine HEq.trans (castTower_heq _ _) ?_
    refine HEq.trans (bottEmbedIter_split_heq v.2 (by omega)) (castTower_heq _ _).symm

/-- Helper: lift a level-wise binary operation compatible with `bottEmbedIter` onto `ClInf A`. -/
private lemma lift_binop_wd
    (op : ∀ n : ℕ, ClTower A n → ClTower A n → ClTower A n)
    (h_emb : ∀ (n k : ℕ) (X Y : ClTower A n),
      bottEmbedIter k (op n X Y) = op (n + k) (bottEmbedIter k X) (bottEmbedIter k Y))
    (h_cast : ∀ {m n : ℕ} (h : m = n) (X Y : ClTower A m),
      castTower h (op m X Y) = op n (castTower h X) (castTower h Y))
    {u₁ u₂ v₁ v₂ : Σ n : ℕ, ClTower A n}
    (hu : ClInfRel u₁ u₂) (hv : ClInfRel v₁ v₂) :
    toClInf (max u₁.1 v₁.1)
      (op (max u₁.1 v₁.1)
        (castTower (Nat.add_sub_cancel' (le_max_left u₁.1 v₁.1))
          (bottEmbedIter (max u₁.1 v₁.1 - u₁.1) u₁.2))
        (castTower (Nat.add_sub_cancel' (le_max_right u₁.1 v₁.1))
          (bottEmbedIter (max u₁.1 v₁.1 - v₁.1) v₁.2))) =
    toClInf (max u₂.1 v₂.1)
      (op (max u₂.1 v₂.1)
        (castTower (Nat.add_sub_cancel' (le_max_left u₂.1 v₂.1))
          (bottEmbedIter (max u₂.1 v₂.1 - u₂.1) u₂.2))
        (castTower (Nat.add_sub_cancel' (le_max_right u₂.1 v₂.1))
          (bottEmbedIter (max u₂.1 v₂.1 - v₂.1) v₂.2))) := by
  rcases hu with ⟨k₁, k₂, h_u, heq_u⟩
  rcases hv with ⟨l₁, l₂, h_v, heq_v⟩
  set M₁ := max u₁.1 v₁.1
  set M₂ := max u₂.1 v₂.1
  set M  := max (u₁.1 + k₁) (v₁.1 + l₁)
  set N  := M₁ + M₂ + M
  have hN₁ : M₁ ≤ N := le_trans (Nat.le_add_right M₁ M₂) (Nat.le_add_right _ M)
  have hN₂ : M₂ ≤ N := le_trans (Nat.le_add_left M₂ M₁) (Nat.le_add_right _ M)
  rw [toClInf_binop_stabilize op h_emb h_cast u₁ v₁ (le_max_left _ _) (le_max_right _ _) hN₁]
  rw [toClInf_binop_stabilize op h_emb h_cast u₂ v₂ (le_max_left _ _) (le_max_right _ _) hN₂]
  have hu_eq :
      castTower (Nat.add_sub_cancel' (le_trans (le_max_left u₁.1 v₁.1) hN₁))
        (bottEmbedIter (N - u₁.1) u₁.2) =
      castTower (Nat.add_sub_cancel' (le_trans (le_max_left u₂.1 v₂.1) hN₂))
        (bottEmbedIter (N - u₂.1) u₂.2) := by
    apply eq_of_heq_tower rfl
    refine HEq.trans (castTower_heq _ _) ?_
    refine HEq.trans ?_ (castTower_heq _ _).symm
    have heq_step :
        HEq (bottEmbedIter (N - (u₁.1 + k₁)) (bottEmbedIter k₁ u₁.2))
            (bottEmbedIter (N - (u₂.1 + k₂)) (bottEmbedIter k₂ u₂.2)) :=
      bottEmbedIter_congr_heq_dim (N - (u₁.1 + k₁)) (N - (u₂.1 + k₂)) h_u (by omega) heq_u
    exact (bottEmbedIter_split_heq u₁.2 (by omega : k₁ + (N - (u₁.1 + k₁)) = N - u₁.1)).symm.trans
      (heq_step.trans (bottEmbedIter_split_heq u₂.2 (by omega : k₂ + (N - (u₂.1 + k₂)) = N - u₂.1)))
  have hv_eq :
      castTower (Nat.add_sub_cancel' (le_trans (le_max_right u₁.1 v₁.1) hN₁))
        (bottEmbedIter (N - v₁.1) v₁.2) =
      castTower (Nat.add_sub_cancel' (le_trans (le_max_right u₂.1 v₂.1) hN₂))
        (bottEmbedIter (N - v₂.1) v₂.2) := by
    apply eq_of_heq_tower rfl
    refine HEq.trans (castTower_heq _ _) ?_
    refine HEq.trans ?_ (castTower_heq _ _).symm
    have heq_step :
        HEq (bottEmbedIter (N - (v₁.1 + l₁)) (bottEmbedIter l₁ v₁.2))
            (bottEmbedIter (N - (v₂.1 + l₂)) (bottEmbedIter l₂ v₂.2)) :=
      bottEmbedIter_congr_heq_dim (N - (v₁.1 + l₁)) (N - (v₂.1 + l₂)) h_v (by omega) heq_v
    exact (bottEmbedIter_split_heq v₁.2 (by omega : l₁ + (N - (v₁.1 + l₁)) = N - v₁.1)).symm.trans
      (heq_step.trans (bottEmbedIter_split_heq v₂.2 (by omega : l₂ + (N - (v₂.1 + l₂)) = N - v₂.1)))
  rw [hu_eq, hv_eq]

private lemma heq_neg_tower {m n : ℕ} (h : m = n) {X : ClTower A m} {Y : ClTower A n}
    (heq : HEq X Y) : HEq (-X) (-Y) := by
  subst h; cases eq_of_heq heq; rfl

private lemma heq_zero_tower {m n : ℕ} (h : m = n) :
    HEq (0 : ClTower A m) (0 : ClTower A n) := by
  subst h; rfl

private def addClInf (x y : ClInf A) : ClInf A :=
  Quotient.liftOn₂ x y
    (fun u v =>
      let M := max u.1 v.1
      toClInf M
        (castTower (Nat.add_sub_cancel' (le_max_left u.1 v.1)) (bottEmbedIter (M - u.1) u.2) +
         castTower (Nat.add_sub_cancel' (le_max_right u.1 v.1)) (bottEmbedIter (M - v.1) v.2)))
    (fun _ _ _ _ hu hv =>
      lift_binop_wd (fun _ X Y => X + Y)
        (fun _ k X Y => bottEmbedIter_add k X Y)
        (fun h X Y => castTower_add h X Y) hu hv)

private def mulClInf (x y : ClInf A) : ClInf A :=
  Quotient.liftOn₂ x y
    (fun u v =>
      let M := max u.1 v.1
      toClInf M
        (castTower (Nat.add_sub_cancel' (le_max_left u.1 v.1)) (bottEmbedIter (M - u.1) u.2) *
         castTower (Nat.add_sub_cancel' (le_max_right u.1 v.1)) (bottEmbedIter (M - v.1) v.2)))
    (fun _ _ _ _ hu hv =>
      lift_binop_wd (fun _ X Y => X * Y)
        (fun _ k X Y => bottEmbedIter_mul k X Y)
        (fun h X Y => castTower_mul h X Y) hu hv)

private def negClInf (x : ClInf A) : ClInf A :=
  Quotient.liftOn x
    (fun u => toClInf u.1 (-u.2))
    (fun _ _ ⟨k₁, k₂, h_dim, heq_u⟩ => by
      apply Quotient.sound
      refine ⟨k₁, k₂, h_dim, ?_⟩
      rw [bottEmbedIter_neg, bottEmbedIter_neg]
      exact heq_neg_tower h_dim heq_u)

private def zeroClInf : ClInf A := toClInf 0 0

instance instZeroClInf : Zero (ClInf A) where zero := zeroClInf
instance instAddClInf : Add (ClInf A) where add := addClInf
instance instNegClInf : Neg (ClInf A) where neg := negClInf
instance instMulClInf : Mul (ClInf A) where mul := mulClInf

lemma toClInf_zero (n : ℕ) : toClInf n (0 : ClTower A n) = 0 := by
  change toClInf n (0 : ClTower A n) = toClInf 0 0
  apply Quotient.sound
  refine ⟨0, n, (Nat.zero_add n).symm, ?_⟩
  have hb : bottEmbedIter n (0 : ClTower A 0) = 0 := bottEmbedIter_zero n
  rw [hb]
  exact heq_zero_tower (Nat.zero_add n).symm

private lemma castTower_bottEmbedIter_max {n : ℕ} (h : n + (max n n - n) = max n n)
    (X : ClTower A n) :
    castTower h (bottEmbedIter (max n n - n) X) = castTower (max_self n).symm X := by
  apply eq_of_heq_tower rfl
  refine HEq.trans (castTower_heq _ _) ?_
  refine HEq.trans ?_ (castTower_heq _ _).symm
  have hz : max n n - n = 0 := by omega
  rw [hz]
  rfl

@[simp] lemma add_toClInf (n : ℕ) (X Y : ClTower A n) :
    toClInf n X + toClInf n Y = toClInf n (X + Y) := by
  change addClInf (toClInf n X) (toClInf n Y) = toClInf n (X + Y)
  simp only [addClInf, toClInf, Quotient.liftOn₂_mk]
  rw [castTower_bottEmbedIter_max, castTower_bottEmbedIter_max, ← castTower_add]
  exact toClInf_castTower _ _

@[simp] lemma mul_toClInf (n : ℕ) (X Y : ClTower A n) :
    toClInf n X * toClInf n Y = toClInf n (X * Y) := by
  change mulClInf (toClInf n X) (toClInf n Y) = toClInf n (X * Y)
  simp only [mulClInf, toClInf, Quotient.liftOn₂_mk]
  rw [castTower_bottEmbedIter_max, castTower_bottEmbedIter_max, ← castTower_mul]
  exact toClInf_castTower _ _

@[simp] lemma neg_toClInf (n : ℕ) (X : ClTower A n) :
    -(toClInf n X) = toClInf n (-X) := rfl

lemma exists_toClInf (x : ClInf A) : ∃ (n : ℕ) (X : ClTower A n), x = toClInf n X := by
  rcases Quotient.exists_rep x with ⟨⟨n, X⟩, rfl⟩
  exact ⟨n, X, rfl⟩

lemma toClInf_lift_three (x y z : ClInf A) :
    ∃ (n : ℕ) (X Y Z : ClTower A n),
      x = toClInf n X ∧ y = toClInf n Y ∧ z = toClInf n Z := by
  rcases Quotient.exists_rep x with ⟨⟨n₁, X₁⟩, rfl⟩
  rcases Quotient.exists_rep y with ⟨⟨n₂, X₂⟩, rfl⟩
  rcases Quotient.exists_rep z with ⟨⟨n₃, X₃⟩, rfl⟩
  set N := max n₁ (max n₂ n₃)
  refine ⟨N,
    castTower (by omega : n₁ + (N - n₁) = N) (bottEmbedIter (N - n₁) X₁),
    castTower (by omega : n₂ + (N - n₂) = N) (bottEmbedIter (N - n₂) X₂),
    castTower (by omega : n₃ + (N - n₃) = N) (bottEmbedIter (N - n₃) X₃),
    ?_, ?_, ?_⟩ <;>
  · rw [toClInf_castTower, toClInf_bottEmbedIter]; rfl

lemma toClInf_lift_two (x y : ClInf A) :
    ∃ (n : ℕ) (X Y : ClTower A n),
      x = toClInf n X ∧ y = toClInf n Y := by
  rcases toClInf_lift_three x y 0 with ⟨n, X, Y, _, hx, hy, _⟩
  exact ⟨n, X, Y, hx, hy⟩

/-- Genuine `NonUnitalRing` structure on the colimit quotient `ClInf A`. -/
instance instNonUnitalRingClInf : NonUnitalRing (ClInf A) where
  add_assoc x y z := by
    rcases toClInf_lift_three x y z with ⟨n, X, Y, Z, rfl, rfl, rfl⟩
    simp [add_assoc]
  zero_add x := by
    rcases exists_toClInf x with ⟨n, X, rfl⟩
    rw [← toClInf_zero n, add_toClInf, zero_add]
  add_zero x := by
    rcases exists_toClInf x with ⟨n, X, rfl⟩
    rw [← toClInf_zero n, add_toClInf, add_zero]
  neg_add_cancel x := by
    rcases exists_toClInf x with ⟨n, X, rfl⟩
    rw [neg_toClInf, add_toClInf, neg_add_cancel, toClInf_zero]
  add_comm x y := by
    rcases toClInf_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
    simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc x y z := by
    rcases toClInf_lift_three x y z with ⟨n, X, Y, Z, rfl, rfl, rfl⟩
    simp [mul_assoc]
  zero_mul x := by
    rcases exists_toClInf x with ⟨n, X, rfl⟩
    rw [← toClInf_zero n, mul_toClInf, zero_mul, toClInf_zero]
  mul_zero x := by
    rcases exists_toClInf x with ⟨n, X, rfl⟩
    rw [← toClInf_zero n, mul_toClInf, mul_zero, toClInf_zero]
  left_distrib x y z := by
    rcases toClInf_lift_three x y z with ⟨n, X, Y, Z, rfl, rfl, rfl⟩
    simp [mul_add]
  right_distrib x y z := by
    rcases toClInf_lift_three x y z with ⟨n, X, Y, Z, rfl, rfl, rfl⟩
    simp [add_mul]

/-- The canonical colimit injection `toClInf n` is a `NonUnitalRingHom`. -/
def toClInfHom (n : ℕ) : ClTower A n →ₙ+* ClInf A where
  toFun := toClInf n
  map_zero' := toClInf_zero n
  map_add' X Y := (add_toClInf n X Y).symm
  map_mul' X Y := (mul_toClInf n X Y).symm

end RingOperations

section StarOperations

variable {A : Type u} [Ring A] [StarRing A]

/-- Recursive conjugate-transpose $\star$-ring structure on `ClTower A n`. -/
@[reducible] instance instStarRingClTower : ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 =>
      let _ : Ring (ClTower A n) := instRingClTower n
      let _ : StarRing (ClTower A n) := instStarRingClTower n
      inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))

lemma bottEmbed_star (n : ℕ) (X : ClTower A n) :
    bottEmbed (star X) = star (bottEmbed X) := by
  let _ : StarRing (ClTower A n) := instStarRingClTower n
  apply ext_fin2
  · simp [bottEmbed, Matrix.star_apply]
  · simp [bottEmbed, Matrix.star_apply]
  · simp [bottEmbed, Matrix.star_apply]
  · simp [bottEmbed, Matrix.star_apply]

lemma bottEmbedIter_star {n : ℕ} (k : ℕ) (X : ClTower A n) :
    bottEmbedIter k (star X) = star (bottEmbedIter k X) := by
  induction k with
  | zero => rfl
  | succ k ih => dsimp [bottEmbedIter]; rw [ih, bottEmbed_star]

private lemma heq_star_tower {m n : ℕ} (h : m = n) {X : ClTower A m} {Y : ClTower A n}
    (heq : HEq X Y) : HEq (star X) (star Y) := by
  subst h; cases eq_of_heq heq; rfl

/-- Quotient-lifted $\star$-involution on `ClInf A`. -/
private def starClInf (x : ClInf A) : ClInf A :=
  Quotient.liftOn x
    (fun u => toClInf u.1 (star u.2))
    (fun _ _ ⟨k₁, k₂, h_dim, heq_u⟩ => by
      apply Quotient.sound
      refine ⟨k₁, k₂, h_dim, ?_⟩
      rw [bottEmbedIter_star, bottEmbedIter_star]
      exact heq_star_tower h_dim heq_u)

instance instStarClInf : Star (ClInf A) where
  star := starClInf

@[simp] lemma star_toClInf (n : ℕ) (X : ClTower A n) :
    star (toClInf n X) = toClInf n (star X) := rfl

instance instInvolutiveStarClInf : InvolutiveStar (ClInf A) where
  star_involutive x := by
    rcases Quotient.exists_rep x with ⟨⟨n, X⟩, rfl⟩
    change star (star (toClInf n X)) = toClInf n X
    simp [star_star]

instance instStarAddMonoidClInf : StarAddMonoid (ClInf A) where
  star_add x y := by
    rcases toClInf_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
    simp [star_add]

instance instStarMulClInf : StarMul (ClInf A) where
  star_mul x y := by
    rcases toClInf_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
    simp [star_mul]

end StarOperations

section NormedCompletion

variable {A : Type u} [NormedRing A]

/-- Recursive block-supremum norm on `ClTower A n`. -/
def towerNorm : ∀ n : ℕ, ClTower A n → ℝ
  | 0,     a => ‖a‖
  | n + 1, M => max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                    (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1)))

lemma towerNorm_nonneg : ∀ (n : ℕ) (X : ClTower A n), 0 ≤ towerNorm n X
  | 0,     a => norm_nonneg a
  | n + 1, M => le_trans (towerNorm_nonneg n (M 0 0)) (le_trans (le_max_left _ _) (le_max_left _ _))

lemma towerNorm_zero : ∀ (n : ℕ), towerNorm n (0 : ClTower A n) = 0
  | 0     => norm_zero
  | n + 1 => by
      dsimp [towerNorm]
      change max (max (towerNorm n (0 : ClTower A n)) (towerNorm n 0))
                 (max (towerNorm n 0) (towerNorm n 0)) = 0
      simp [towerNorm_zero n]

lemma towerNorm_neg : ∀ (n : ℕ) (X : ClTower A n), towerNorm n (-X) = towerNorm n X
  | 0,     a => norm_neg a
  | n + 1, M => by
      dsimp [towerNorm]
      change max (max (towerNorm n (-M 0 0)) (towerNorm n (-M 0 1)))
                 (max (towerNorm n (-M 1 0)) (towerNorm n (-M 1 1))) =
             max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                 (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1)))
      simp [towerNorm_neg n]

lemma towerNorm_add_le : ∀ (n : ℕ) (X Y : ClTower A n),
    towerNorm n (X + Y) ≤ towerNorm n X + towerNorm n Y
  | 0,     a, b => norm_add_le a b
  | n + 1, M, N => by
      dsimp [towerNorm]
      change max (max (towerNorm n (M 0 0 + N 0 0)) (towerNorm n (M 0 1 + N 0 1)))
                 (max (towerNorm n (M 1 0 + N 1 0)) (towerNorm n (M 1 1 + N 1 1))) ≤
             max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                 (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1))) +
             max (max (towerNorm n (N 0 0)) (towerNorm n (N 0 1)))
                 (max (towerNorm n (N 1 0)) (towerNorm n (N 1 1)))
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
      · exact le_trans (towerNorm_add_le n (M 0 0) (N 0 0))
          (add_le_add (le_trans (le_max_left _ _) (le_max_left _ _))
                      (le_trans (le_max_left _ _) (le_max_left _ _)))
      · exact le_trans (towerNorm_add_le n (M 0 1) (N 0 1))
          (add_le_add (le_trans (le_max_right _ _) (le_max_left _ _))
                      (le_trans (le_max_right _ _) (le_max_left _ _)))
      · exact le_trans (towerNorm_add_le n (M 1 0) (N 1 0))
          (add_le_add (le_trans (le_max_left _ _) (le_max_right _ _))
                      (le_trans (le_max_left _ _) (le_max_right _ _)))
      · exact le_trans (towerNorm_add_le n (M 1 1) (N 1 1))
          (add_le_add (le_trans (le_max_right _ _) (le_max_right _ _))
                      (le_trans (le_max_right _ _) (le_max_right _ _)))

lemma eq_zero_of_towerNorm_eq_zero : ∀ {n : ℕ} {X : ClTower A n},
    towerNorm n X = 0 → X = 0
  | 0,     _, h => norm_eq_zero.mp h
  | n + 1, M, h => by
      dsimp [towerNorm] at h
      have h00 : towerNorm n (M 0 0) = 0 :=
        le_antisymm (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h.le)
          (towerNorm_nonneg n (M 0 0))
      have h01 : towerNorm n (M 0 1) = 0 :=
        le_antisymm (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h.le)
          (towerNorm_nonneg n (M 0 1))
      have h10 : towerNorm n (M 1 0) = 0 :=
        le_antisymm (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h.le)
          (towerNorm_nonneg n (M 1 0))
      have h11 : towerNorm n (M 1 1) = 0 :=
        le_antisymm (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h.le)
          (towerNorm_nonneg n (M 1 1))
      apply ext_fin2
      · exact eq_zero_of_towerNorm_eq_zero h00
      · exact eq_zero_of_towerNorm_eq_zero h01
      · exact eq_zero_of_towerNorm_eq_zero h10
      · exact eq_zero_of_towerNorm_eq_zero h11

theorem towerNorm_bottEmbed (n : ℕ) (X : ClTower A n) :
    towerNorm (n + 1) (bottEmbed X) = towerNorm n X := by
  dsimp [towerNorm, bottEmbed, mat2]
  simp [towerNorm_zero n, max_eq_left (towerNorm_nonneg n X)]

theorem towerNorm_bottEmbedIter {n : ℕ} (k : ℕ) (X : ClTower A n) :
    towerNorm (n + k) (bottEmbedIter k X) = towerNorm n X := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [bottEmbedIter]
      change towerNorm ((n + k) + 1) (bottEmbed (bottEmbedIter k X)) = towerNorm n X
      rw [towerNorm_bottEmbed, ih]

private lemma towerNorm_eq_of_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    towerNorm m₁ X = towerNorm m₂ Y := by
  subst h_dim; cases eq_of_heq h_heq; rfl

private lemma clInfNorm_well_defined
    (u v : Σ n : ℕ, ClTower A n) (h_rel : ClInfRel u v) :
    towerNorm u.1 u.2 = towerNorm v.1 v.2 := by
  rcases h_rel with ⟨k₁, k₂, h_dim, h_heq⟩
  calc towerNorm u.1 u.2
    _ = towerNorm (u.1 + k₁) (bottEmbedIter k₁ u.2) := (towerNorm_bottEmbedIter k₁ u.2).symm
    _ = towerNorm (v.1 + k₂) (bottEmbedIter k₂ v.2) := towerNorm_eq_of_heq h_dim h_heq
    _ = towerNorm v.1 v.2                            := towerNorm_bottEmbedIter k₂ v.2

/-- Quotient-lifted inductive-limit norm on `ClInf A`. -/
def clInfNorm : ClInf A → ℝ :=
  Quotient.lift (fun u => towerNorm u.1 u.2) clInfNorm_well_defined

@[simp] lemma clInfNorm_toClInf (n : ℕ) (X : ClTower A n) :
    clInfNorm (toClInf n X) = towerNorm n X := rfl

/-- Genuine `NormedAddCommGroup` structure on `ClInf A`, inducing its metric and uniform space. -/
noncomputable instance instNormedAddCommGroupClInf : NormedAddCommGroup (ClInf A) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := clInfNorm
      map_zero' := by
        rw [← toClInf_zero 0, clInfNorm_toClInf, towerNorm_zero]
      add_le' := fun x y => by
        rcases toClInf_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
        simp only [add_toClInf, clInfNorm_toClInf]
        exact towerNorm_add_le n X Y
      neg' := fun x => by
        rcases Quotient.exists_rep x with ⟨⟨n, X⟩, rfl⟩
        change clInfNorm (-(toClInf n X)) = clInfNorm (toClInf n X)
        simp only [neg_toClInf, clInfNorm_toClInf]
        exact towerNorm_neg n X
      eq_zero_of_map_eq_zero' := fun x hx => by
        rcases Quotient.exists_rep x with ⟨⟨n, X⟩, rfl⟩
        change clInfNorm (toClInf n X) = 0 at hx
        rw [clInfNorm_toClInf] at hx
        change toClInf n X = 0
        rw [eq_zero_of_towerNorm_eq_zero hx, toClInf_zero] }

@[simp] lemma norm_toClInf (n : ℕ) (X : ClTower A n) :
    ‖toClInf n X‖ = towerNorm n X := rfl

/-- Isometric Cauchy completion $\widehat{\mathcal{C}\ell}_\infty(A) = \mathrm{Completion}(\mathcal{C}\ell_\infty(A))$. -/
abbrev ClInfCompletion (A : Type u) [NormedRing A] := UniformSpace.Completion (ClInf A)

theorem clInf_completion_isometric_dense (n : ℕ) (X : ClTower A n) :
    ‖((toClInf n X : ClInf A) : ClInfCompletion A)‖ = towerNorm n X ∧
    DenseRange (fun x : ClInf A => (x : ClInfCompletion A)) :=
  ⟨by rw [UniformSpace.Completion.norm_coe, norm_toClInf],
   UniformSpace.Completion.denseRange_coe⟩

lemma towerNorm_star [StarRing A] [NormedStarGroup A] :
    ∀ (n : ℕ) (X : ClTower A n), towerNorm n (star X) = towerNorm n X
  | 0,     a => norm_star a
  | n + 1, M => by
      let _ : StarRing (ClTower A n) := instStarRingClTower n
      dsimp [towerNorm]
      change max (max (towerNorm n (star (M 0 0))) (towerNorm n (star (M 1 0))))
                 (max (towerNorm n (star (M 0 1))) (towerNorm n (star (M 1 1)))) =
             max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                 (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1)))
      rw [towerNorm_star n (M 0 0), towerNorm_star n (M 1 0),
          towerNorm_star n (M 0 1), towerNorm_star n (M 1 1)]
      ac_rfl

theorem clInf_star_isometry [StarRing A] [NormedStarGroup A] (x : ClInf A) :
    ‖star x‖ = ‖x‖ := by
  rcases Quotient.exists_rep x with ⟨⟨n, X⟩, rfl⟩
  change ‖star (toClInf n X)‖ = ‖toClInf n X‖
  rw [star_toClInf, norm_toClInf, norm_toClInf, towerNorm_star]

end NormedCompletion

end AlgebraicAndNormedCompletion

/-!
## Part 2: Hodge–Parabolic Monodromy $\leftrightarrow$ Quotient Supertrace & Lindblad Damping
-/

section HodgeParabolicLindbladBridge

variable {A : Type u} [Ring A]

/-- Canonical ring isomorphism transporting `NoncommutativeHodgeParabolicTowerSynthesis.ClTower A n`
into `NoncommutativeCliffordColimitMassGapSynthesis.ClTower A n`. -/
def hpToCl : ∀ {n : ℕ},
    InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.ClTower A n → ClTower A n
  | 0,     a => a
  | _ + 1, M => mat2 (hpToCl (M 0 0)) (hpToCl (M 0 1)) (hpToCl (M 1 0)) (hpToCl (M 1 1))

lemma hpToCl_zero (n : ℕ) :
    hpToCl (A := A) (0 : InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.ClTower A n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [hpToCl]
      apply ext_fin2 <;> simp [mat2, ih]

lemma hpToCl_one (n : ℕ) :
    hpToCl (A := A) (1 : InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.ClTower A n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [hpToCl]
      apply ext_fin2 <;> simp [mat2, ih, hpToCl_zero]

lemma hpToCl_add {n : ℕ}
    (X Y : InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.ClTower A n) :
    hpToCl (X + Y) = hpToCl X + hpToCl Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [hpToCl]
      apply ext_fin2 <;> simp [mat2, ih]

lemma hpToCl_mul {n : ℕ}
    (X Y : InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.ClTower A n) :
    hpToCl (X * Y) = hpToCl X * hpToCl Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [hpToCl]
      apply ext_fin2 <;> simp [mat2, ih, hpToCl_add, mul_apply, Fin.sum_univ_two]

lemma hpToCl_pow {n : ℕ}
    (X : InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.ClTower A n) (k : ℕ) :
    hpToCl (X ^ k) = (hpToCl X) ^ k := by
  induction k with
  | zero => simp [hpToCl_one]
  | succ k ih => rw [pow_succ, hpToCl_mul, ih, pow_succ]

lemma hpToCl_cantorProj (n : ℕ) :
    hpToCl (InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.cantorProj (A := A) n) =
      cantorProj (A := A) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.cantorProj,
        cantorProj, bottEmbed, hpToCl,
        InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.mat2]
      apply ext_fin2 <;> simp [mat2, ih, hpToCl_zero]

lemma hpToCl_wittDelta (n : ℕ) :
    hpToCl (InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.wittDelta (A := A) n) =
      mat2 0 0 (cantorProj (A := A) n) 0 := by
  dsimp [InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.wittDelta,
    hpToCl, InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.mat2]
  apply ext_fin2 <;> simp [mat2, hpToCl_zero, hpToCl_cantorProj]

/-- Off-diagonal parabolic transition coherence induced by $k$-step Hodge–Parabolic monodromy:
$\Psi_{\mathrm{Hodge}}^{(k)}(n) := (1 - \Pi_{\mathcal{C}_{n+1}}) (Q_{\mathrm{Hodge}}^{(n+1)})^k \Pi_{\mathcal{C}_{n+1}}$. -/
def hodgeParabolicCoherence (n k : ℕ) : ClTower A (n + 1) :=
  coherenceMode (n + 1)
    (hpToCl ((InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.hodgeMonodromy (A := A) n) ^ k))

/-- **Hodge–Parabolic $\leftrightarrow$ Quotient Supertrace & Lindblad Bridge Theorem**:
1. *Vacuum Evacuation*: `hpToCl (hodgeMonodromy n) * cantorProj (n + 1) = hpToCl (wittDelta n)`,
   which is a pure off-diagonal transition coherence (`coherenceMode (n + 1) (hpToCl (wittDelta n)) = hpToCl (wittDelta n)`),
   with `clInfSuperTrace` dropping from `1` (vacuum) to `0` (evacuated coexact coherence).
2. *Evacuated State Quadratic Damping*: On `Ψ_evac = hpToCl (hodgeMonodromy n) * P_vac`,
   `lindbladDissipator (massGapOp m₀ (n + 1)) Ψ_evac = -(towerScalar (n + 1) (m₀ * m₀) * Ψ_evac)`.
3. *Parabolic Transition Coherence Damping*: On the $k$-step off-diagonal parabolic coherence
   `hodgeParabolicCoherence n k`, the Lindblad dissipator acts by exact quadratic mass-gap
   damping `-(towerScalar (n + 1) (m₀ * m₀) * hodgeParabolicCoherence n k)`. -/
theorem hodge_parabolic_lindblad_and_supertrace_bridge (m₀ : A) (n k : ℕ) :
    let P_vac  := cantorProj (A := A) (n + 1)
    let Ψ_evac := hpToCl (InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.hodgeMonodromy (A := A) n) * P_vac
    let Ψ_coh  := hodgeParabolicCoherence (A := A) n k
    let Δ      := massGapOp m₀ (n + 1)
    Ψ_evac = hpToCl (InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.wittDelta n) ∧
    clInfSuperTrace (toClInf (n + 1) P_vac) = 1 ∧
    clInfSuperTrace (toClInf (n + 1) Ψ_evac) = 0 ∧
    lindbladDissipator Δ Ψ_evac =
      -(towerScalar (n + 1) (m₀ * m₀) * Ψ_evac) ∧
    lindbladDissipator Δ Ψ_coh =
      -(towerScalar (n + 1) (m₀ * m₀) * Ψ_coh) := by
  intro P_vac Ψ_evac Ψ_coh Δ
  have h_evac : Ψ_evac = hpToCl (InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.wittDelta n) := by
    dsimp [Ψ_evac, P_vac]
    rw [← hpToCl_cantorProj (n + 1), ← hpToCl_mul]
    exact congrArg hpToCl
      (InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.vacuum_evacuation_and_k_step_coexact_excitation n k).1
  have h_str_vac : clInfSuperTrace (toClInf (n + 1) P_vac) = 1 :=
    (clInf_vacuum_stabilization_and_supertrace (n + 1) P_vac).2.2
  have h_str_evac : clInfSuperTrace (toClInf (n + 1) Ψ_evac) = 0 := by
    rw [h_evac, hpToCl_wittDelta]
    dsimp only [clInfSuperTrace, toClInf]
    rw [Quotient.lift_mk]
    dsimp only [superTrace, chiralityOp]
    have h0 : ∀ m : ℕ, towerTrace (0 : ClTower A m) = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ j ih =>
          dsimp [towerTrace]
          change towerTrace (0 : ClTower A j) + towerTrace (0 : ClTower A j) = 0
          rw [ih, add_zero]
    have h_mat :
        mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * mat2 0 0 (cantorProj (A := A) n) 0 =
        mat2 0 0 ((-chiralityOp n) * cantorProj n) 0 := by
      apply ext_fin2 <;> simp [mat2]
    have h_res :
        towerTrace (A := A) (n := n + 1)
          (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) *
            mat2 0 0 (cantorProj (A := A) n) 0) = 0 := by
      rw [h_mat]
      dsimp [towerTrace]
      rw [h0 n, add_zero]
    exact h_res
  have h_evac_coh : coherenceMode (n + 1) Ψ_evac = Ψ_evac := by
    rw [h_evac, hpToCl_wittDelta]
    have hP := cantorProj_idem (A := A) n
    dsimp [coherenceMode, P_vac, cantorProj, bottEmbed]
    apply ext_fin2 <;> simp [mat2, hP]
  have h_lind_evac :
      lindbladDissipator Δ Ψ_evac = -(towerScalar (n + 1) (m₀ * m₀) * Ψ_evac) := by
    have h_l := (lindblad_mass_gap_damping_and_colimit_stability m₀ (n + 1) 0 0 Ψ_evac).2.2.1
    rw [h_evac_coh] at h_l
    exact h_l
  have h_lind_coh :
      lindbladDissipator Δ Ψ_coh = -(towerScalar (n + 1) (m₀ * m₀) * Ψ_coh) :=
    (lindblad_mass_gap_damping_and_colimit_stability m₀ (n + 1) 0 0
      (hpToCl ((InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis.hodgeMonodromy (A := A) n) ^ k))).2.2.1
  exact ⟨h_evac, h_str_vac, h_str_evac, h_lind_evac, h_lind_coh⟩

end HodgeParabolicLindbladBridge

/-!
## Part 3: Normed Lindblad Contraction & Mass-Gap Decay Bound
-/

section NormedLindbladContraction

variable {A : Type u} [NormedRing A] [NormedAlgebra ℝ A]

/-- Recursive `ℝ`-module structure on `ClTower A n`. -/
@[reducible] noncomputable instance instModuleRealClTower : ∀ n : ℕ, Module ℝ (ClTower A n)
  | 0     => inferInstanceAs (Module ℝ A)
  | n + 1 =>
      let _ : Ring (ClTower A n) := instRingClTower n
      let _ : Module ℝ (ClTower A n) := instModuleRealClTower n
      inferInstanceAs (Module ℝ (Matrix (Fin 2) (Fin 2) (ClTower A n)))

lemma towerNorm_smul (c : ℝ) :
    ∀ (n : ℕ) (X : ClTower A n), towerNorm n (c • X) = |c| * towerNorm n X
  | 0,     a => norm_smul c a
  | n + 1, M => by
      dsimp [towerNorm]
      change max (max (towerNorm n (c • M 0 0)) (towerNorm n (c • M 0 1)))
                 (max (towerNorm n (c • M 1 0)) (towerNorm n (c • M 1 1))) =
             |c| * max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                       (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1)))
      rw [towerNorm_smul c n (M 0 0), towerNorm_smul c n (M 0 1),
          towerNorm_smul c n (M 1 0), towerNorm_smul c n (M 1 1)]
      simp only [← mul_max_of_nonneg _ _ (abs_nonneg c)]

lemma towerScalar_algebraMap_mul (n : ℕ) (r : ℝ) (X : ClTower A n) :
    towerScalar n (algebraMap ℝ A r) * X = r • X := by
  induction n with
  | zero =>
      change algebraMap ℝ A r * X = r • X
      exact (Algebra.smul_def r X).symm
  | succ n ih =>
      apply ext_fin2 <;>
      · dsimp [towerScalar, mat2]
        simp [ih]

/-- **Normed Lindblad Euler-Step Contraction & Vacuum Decoherence-Free Theorem**:
For any scalar mass $m_0 \in \mathbb{R}$ and Euler step $t \ge 0$ with $t m_0^2 \le 1$:
1. *Exact Vacuum Preservation*: The Cantor vacuum $\Pi_{\mathcal{C}_n}$ is stationary under
   the Euler Lindblad flow, preserving its norm in `ClInf A` and `ClInfCompletion A`.
2. *Exact Coherence Contraction*: On any transition coherence
   $\Psi_{\mathrm{coh}}(X) = (1 - \Pi_{\mathcal{C}_n}) X \Pi_{\mathcal{C}_n}$,
   the Euler Lindblad step contracts the inductive-limit norm by exact factor $(1 - t m_0^2)$:
   $$\|\pi_\infty(n, \Psi_{\mathrm{coh}} + t \bullet \mathcal{D}_{\mathrm{Lind}}(\Delta_n(m_0), \Psi_{\mathrm{coh}}))\|
     = (1 - t m_0^2)\,\|\pi_\infty(n, \Psi_{\mathrm{coh}})\|.$$ -/
theorem lindblad_euler_contraction_and_vacuum_preservation
    (m₀ t : ℝ) (ht : 0 ≤ t) (h_cfl : t * (m₀ * m₀) ≤ 1) (n : ℕ) (X : ClTower A n) :
    let m_A   := algebraMap ℝ A m₀
    let Δ_n   := massGapOp m_A n
    let Ψ_coh := coherenceMode n X
    let step_vac := cantorProj n + t • lindbladDissipator Δ_n (cantorProj n)
    let step_coh := Ψ_coh + t • lindbladDissipator Δ_n Ψ_coh
    step_vac = cantorProj n ∧
    ‖((toClInf n step_vac : ClInf A) : ClInfCompletion A)‖ =
      ‖((toClInf n (cantorProj n) : ClInf A) : ClInfCompletion A)‖ ∧
    step_coh = (1 - t * (m₀ * m₀)) • Ψ_coh ∧
    ‖((toClInf n step_coh : ClInf A) : ClInfCompletion A)‖ =
      (1 - t * (m₀ * m₀)) * ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ ∧
    ‖((toClInf n step_coh : ClInf A) : ClInfCompletion A)‖ ≤
      ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ := by
  intro m_A Δ_n Ψ_coh step_vac step_coh
  have h_lind := lindblad_mass_gap_damping_and_colimit_stability m_A n 0 0 X
  have h_vac_zero : lindbladDissipator Δ_n (cantorProj n) = 0 := h_lind.2.1
  have h_step_vac : step_vac = cantorProj n := by
    dsimp [step_vac]
    rw [h_vac_zero, smul_zero, add_zero]
  have h_step_coh : step_coh = (1 - t * (m₀ * m₀)) • Ψ_coh := by
    dsimp [step_coh]
    rw [h_lind.2.2.1]
    have hm2 : towerScalar n (m_A * m_A) * Ψ_coh = (m₀ * m₀) • Ψ_coh := by
      have h_alg : m_A * m_A = algebraMap ℝ A (m₀ * m₀) := by
        dsimp [m_A]; rw [map_mul]
      rw [h_alg, towerScalar_algebraMap_mul]
    rw [hm2, smul_neg, ← sub_eq_add_neg, sub_smul, one_smul, smul_smul]
  have h_norm_eq :
      ‖((toClInf n step_coh : ClInf A) : ClInfCompletion A)‖ =
        (1 - t * (m₀ * m₀)) * ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ := by
    rw [h_step_coh]
    simp only [UniformSpace.Completion.norm_coe, norm_toClInf, towerNorm_smul]
    rw [abs_of_nonneg (sub_nonneg.mpr h_cfl)]
  have h_factor_le : 1 - t * (m₀ * m₀) ≤ 1 :=
    sub_le_self 1 (mul_nonneg ht (mul_self_nonneg m₀))
  refine ⟨h_step_vac, ?_, h_step_coh, h_norm_eq, ?_⟩
  · rw [h_step_vac]
  · rw [h_norm_eq]
    calc (1 - t * (m₀ * m₀)) * ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖
      _ ≤ 1 * ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ :=
          mul_le_mul_of_nonneg_right h_factor_le (norm_nonneg _)
      _ = ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ := one_mul _

end NormedLindbladContraction

/-- Non-commutativity witness for `ClInf A` (inherited from `ClTower A 1`). -/
private theorem clInf_noncomm_witness {A : Type u} [Ring A] [Nontrivial A] :
    ∃ x y : ClInf A, x * y ≠ y * x := by
  refine ⟨toClInf 1 (mat2 (0 : A) 1 0 0), toClInf 1 (mat2 (0 : A) 0 1 0), ?_⟩
  intro h
  have h_left := congrArg (fun z => toClInf 1 (mat2 (1 : A) 0 0 0) * z) h
  simp only [mul_toClInf] at h_left
  have h_lhs : mat2 (1 : A) 0 0 0 * (mat2 0 1 0 0 * mat2 0 0 1 0) = mat2 1 0 0 0 := by
    apply ext_fin2 <;> simp [mat2]
  have h_rhs : mat2 (1 : A) 0 0 0 * (mat2 0 0 1 0 * mat2 0 1 0 0) = 0 := by
    apply ext_fin2 <;> simp [mat2]
  rw [h_lhs, h_rhs] at h_left
  have h_str := congrArg clInfSuperTrace h_left
  have h1_eq : mat2 (1 : A) 0 0 0 = cantorProj 1 := rfl
  rw [h1_eq] at h_str
  have h1 : clInfSuperTrace (toClInf 1 (cantorProj (A := A) 1)) = 1 :=
    (clInf_vacuum_stabilization_and_supertrace 1 (cantorProj 1)).2.2
  have h0 : clInfSuperTrace (toClInf 1 (0 : ClTower A 1)) = 0 := by
    rw [toClInf_zero]
    change clInfSuperTrace (toClInf 0 (0 : A)) = 0
    dsimp [clInfSuperTrace, toClInf, superTrace, chiralityOp, towerTrace]
    exact mul_zero 1
  rw [h1, h0] at h_str
  exact one_ne_zero h_str

end InfoGeometry.Algebra.NoncommutativeColimitNormedLindbladBridge
