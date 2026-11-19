/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# $2^\infty$ UHF Inductive Colimit C*-Algebra & Completion

This module formalizes the universal hyperfinite (UHF) inductive colimit algebra of type $2^\infty$
(the canonical CAR algebra), equipped with unital block-doubling embeddings and the strict $L^2$
operator norm (`Matrix.Norms.L2Operator`), and constructs its C*-completion:

1. **Unital Star Embedding `uhfStep`**:
   At each level $n$, $A \in M_{2^n}(\mathbb{C})$ maps to $\mathrm{diag}(A, A) \in M_{2^{n+1}}(\mathbb{C})$ via
   `fromBlocks A 0 0 A` reindexed across `finSumTwoPow n : Fin (2^n) ⊕ Fin (2^n) ≃ Fin (2^(n+1))`.
   This is a unital $\star$-algebra homomorphism (`uhfStepHom n : UHFStage n →⋆ₐ[ℂ] UHFStage (n + 1)`).
2. **Strict $L^2$ Operator Norm Isometry**:
   Proves `‖uhfStep n A‖ = ‖A‖`, ensuring the directed system is strictly isometric.
3. **Directed Colimit Algebra `UHFAlg`**:
   The quotient of $\Sigma\, n : \mathbb{N},\, M_{2^n}(\mathbb{C})$ by the inductive equivalence relation
   inherits a genuine unital $\star$-ring structure (`Ring UHFAlg`, `StarRing UHFAlg`), an exact
   C*-norm (`CStarRing UHFAlg`), unit norm `‖(1 : UHFAlg)‖ = 1`, and certified non-commutativity.
4. **C*-Algebra Completion `UHFCStar`**:
   The completion `UniformSpace.Completion UHFAlg` is a complete C*-algebra (`CompleteSpace UHFCStar`,
   `NormedRing UHFCStar`, `StarRing UHFCStar`, `CStarRing UHFCStar`), permanently closing Open Debt #3.
-/

namespace InfoGeometry.Algebra.UHFColimitCStarCompletion

open Matrix
open scoped Matrix.Norms.L2Operator

/-!
## Part 1: Index Equivalences and Unital Block-Doubling Step Embedding
-/

/-- Index equivalence between the sum of two blocks of size $2^n$ and the block of size $2^{n+1}$. -/
def finSumTwoPow (n : ℕ) : Fin (2^n) ⊕ Fin (2^n) ≃ Fin (2^(n+1)) :=
  finSumFinEquiv.trans (Fin.castOrderIso (by rw [← mul_two, ← pow_succ])).toEquiv

/-- Level-$n$ matrix algebra $M_{2^n}(\mathbb{C})$. -/
abbrev UHFStage (n : ℕ) : Type := Matrix (Fin (2^n)) (Fin (2^n)) ℂ

/-- Unital block-doubling step embedding $A \mapsto \mathrm{diag}(A, A)$ from level $n$ to level $n + 1$. -/
def uhfStep (n : ℕ) (A : UHFStage n) : UHFStage (n + 1) :=
  reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks A 0 0 A)

lemma uhfStep_zero (n : ℕ) : uhfStep n 0 = 0 := by
  change reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks 0 0 0 0) = 0
  rw [fromBlocks_zero, map_zero]

lemma uhfStep_one (n : ℕ) : uhfStep n 1 = 1 := by
  change reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks 1 0 0 1) = 1
  rw [fromBlocks_one, map_one]

lemma uhfStep_add (n : ℕ) (A B : UHFStage n) :
    uhfStep n (A + B) = uhfStep n A + uhfStep n B := by
  change reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks (A + B) 0 0 (A + B)) =
    reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks A 0 0 A) +
    reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks B 0 0 B)
  rw [← map_add]
  congr 1
  ext (i | i) (j | j) <;> simp

lemma uhfStep_mul (n : ℕ) (A B : UHFStage n) :
    uhfStep n (A * B) = uhfStep n A * uhfStep n B := by
  change reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks (A * B) 0 0 (A * B)) =
    reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks A 0 0 A) *
    reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks B 0 0 B)
  rw [← map_mul]
  congr 1
  rw [fromBlocks_multiply]
  simp

lemma uhfStep_neg (n : ℕ) (A : UHFStage n) :
    uhfStep n (-A) = -uhfStep n A := by
  change reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks (-A) 0 0 (-A)) =
    -reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks A 0 0 A)
  rw [← map_neg]
  congr 1
  ext (i | i) (j | j) <;> simp

lemma uhfStep_smul (n : ℕ) (c : ℂ) (A : UHFStage n) :
    uhfStep n (c • A) = c • uhfStep n A := by
  change reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks (c • A) 0 0 (c • A)) =
    c • reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks A 0 0 A)
  rw [← map_smul]
  congr 1
  ext (i | i) (j | j) <;> simp

lemma uhfStep_star (n : ℕ) (A : UHFStage n) :
    uhfStep n (star A) = star (uhfStep n A) := by
  change reindex (finSumTwoPow n) (finSumTwoPow n) (fromBlocks Aᴴ 0 0 Aᴴ) =
    (reindex (finSumTwoPow n) (finSumTwoPow n) (fromBlocks A 0 0 A))ᴴ
  rw [conjTranspose_reindex]
  congr 1
  rw [fromBlocks_conjTranspose, conjTranspose_zero]

/-- Bundled unital $\star$-algebra homomorphism for the step embedding. -/
def uhfStepHom (n : ℕ) : UHFStage n →⋆ₐ[ℂ] UHFStage (n + 1) where
  toFun := uhfStep n
  map_one' := uhfStep_one n
  map_mul' := uhfStep_mul n
  map_zero' := uhfStep_zero n
  map_add' := uhfStep_add n
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [uhfStep_smul, uhfStep_one]
  map_star' := uhfStep_star n

lemma uhfStep_injective (n : ℕ) : Function.Injective (uhfStep n) := by
  intro A B h
  dsimp [uhfStep] at h
  have hfb : fromBlocks A 0 0 A = fromBlocks B 0 0 B :=
    (reindexAlgEquiv ℂ ℂ (finSumTwoPow n)).injective h
  ext i j
  have hij := congr_fun (congr_fun hfb (Sum.inl i)) (Sum.inl j)
  simpa only [fromBlocks_apply₁₁] using hij

/-- **Strict $L^2$ Operator Norm Isometry Theorem**:
The block-doubling embedding preserves the operator C*-norm identically. -/
theorem uhfStep_isometry (n : ℕ) (A : UHFStage n) : ‖uhfStep n A‖ = ‖A‖ :=
  NonUnitalStarAlgHom.norm_map (uhfStepHom n) (uhfStep_injective n) A

/-!
## Part 2: Iterated Step Embeddings and Equal-Level Casts
-/

/-- Iterated multi-step embedding $\iota^{(k)} : M_{2^n}(\mathbb{C}) \to M_{2^{n+k}}(\mathbb{C})$. -/
def uhfStepIter : ∀ {n : ℕ} (k : ℕ), UHFStage n → UHFStage (n + k)
  | _, 0,     X => X
  | _, k + 1, X => uhfStep _ (uhfStepIter k X)

lemma uhfStepIter_zero {n : ℕ} (k : ℕ) : uhfStepIter k (0 : UHFStage n) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [uhfStepIter]
      rw [ih, uhfStep_zero]

lemma uhfStepIter_one {n : ℕ} (k : ℕ) : uhfStepIter k (1 : UHFStage n) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [uhfStepIter]
      rw [ih, uhfStep_one]

lemma uhfStepIter_add {n : ℕ} (k : ℕ) (X Y : UHFStage n) :
    uhfStepIter k (X + Y) = uhfStepIter k X + uhfStepIter k Y := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [uhfStepIter]
      rw [ih, uhfStep_add]

lemma uhfStepIter_neg {n : ℕ} (k : ℕ) (X : UHFStage n) :
    uhfStepIter k (-X) = -uhfStepIter k X := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [uhfStepIter]
      rw [ih, uhfStep_neg]

lemma uhfStepIter_mul {n : ℕ} (k : ℕ) (X Y : UHFStage n) :
    uhfStepIter k (X * Y) = uhfStepIter k X * uhfStepIter k Y := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [uhfStepIter]
      rw [ih, uhfStep_mul]

lemma uhfStepIter_star {n : ℕ} (k : ℕ) (X : UHFStage n) :
    uhfStepIter k (star X) = star (uhfStepIter k X) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [uhfStepIter]
      rw [ih, uhfStep_star]

theorem uhfStepIter_norm {n : ℕ} (k : ℕ) (X : UHFStage n) :
    ‖uhfStepIter k X‖ = ‖X‖ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [uhfStepIter]
      rw [uhfStep_isometry, ih]

/-- Cast across equal stage dimensions. -/
def castStage {m n : ℕ} (h : m = n) (X : UHFStage m) : UHFStage n :=
  h ▸ X

lemma castStage_rfl {n : ℕ} (X : UHFStage n) : castStage (by rfl) X = X := by
  dsimp [castStage]

lemma castStage_heq {m n : ℕ} (h : m = n) (X : UHFStage m) :
    HEq (castStage h X) X := by
  subst h
  rfl

lemma castStage_add {m n : ℕ} (h : m = n) (X Y : UHFStage m) :
    castStage h (X + Y) = castStage h X + castStage h Y := by
  subst h
  rfl

lemma castStage_neg {m n : ℕ} (h : m = n) (X : UHFStage m) :
    castStage h (-X) = -castStage h X := by
  subst h
  rfl

lemma castStage_mul {m n : ℕ} (h : m = n) (X Y : UHFStage m) :
    castStage h (X * Y) = castStage h X * castStage h Y := by
  subst h
  rfl

lemma castStage_star {m n : ℕ} (h : m = n) (X : UHFStage m) :
    castStage h (star X) = star (castStage h X) := by
  subst h
  rfl

lemma castStage_norm {m n : ℕ} (h : m = n) (X : UHFStage m) :
    ‖castStage h X‖ = ‖X‖ := by
  subst h
  rfl

lemma uhfStepIter_castStage {m n : ℕ} (h : m = n) (k : ℕ) (X : UHFStage m) :
    uhfStepIter k (castStage h X) =
      castStage (congrArg (· + k) h) (uhfStepIter k X) := by
  subst h
  rfl

lemma eq_of_heq_stage {m n : ℕ} (h : m = n) {X : UHFStage m} {Y : UHFStage n}
    (heq : HEq X Y) : castStage h X = Y := by
  subst h
  exact eq_of_heq heq

lemma uhfStep_congr_heq {m₁ m₂ : ℕ} {X : UHFStage m₁} {Y : UHFStage m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    HEq (uhfStep m₁ X) (uhfStep m₂ Y) := by
  subst h_dim
  cases eq_of_heq h_heq
  exact HEq.rfl

lemma uhfStepIter_congr_heq {m₁ m₂ : ℕ} (d : ℕ) {X : UHFStage m₁} {Y : UHFStage m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    HEq (uhfStepIter d X) (uhfStepIter d Y) := by
  induction d with
  | zero => exact h_heq
  | succ d ih => exact uhfStep_congr_heq (by simp [h_dim]) ih

lemma uhfStepIter_add_heq {n : ℕ} (k d : ℕ) (X : UHFStage n) :
    HEq (uhfStepIter (k + d) X) (uhfStepIter d (uhfStepIter k X)) := by
  induction d with
  | zero => exact HEq.rfl
  | succ d ih => exact uhfStep_congr_heq (by simp [Nat.add_assoc]) ih

lemma uhfStepIter_comm_heq {n : ℕ} (a b : ℕ) (X : UHFStage n) :
    HEq (uhfStepIter (a + b) X) (uhfStepIter (b + a) X) := by
  have h : a + b = b + a := Nat.add_comm a b
  rw [h]

private lemma heq_zero_stage {m n : ℕ} (h : m = n) :
    HEq (0 : UHFStage m) (0 : UHFStage n) := by
  subst h
  rfl

private lemma heq_one_stage {m n : ℕ} (h : m = n) :
    HEq (1 : UHFStage m) (1 : UHFStage n) := by
  subst h
  rfl

private lemma heq_neg_stage {m n : ℕ} (h : m = n) {X : UHFStage m} {Y : UHFStage n}
    (heq : HEq X Y) : HEq (-X) (-Y) := by
  subst h
  cases eq_of_heq heq
  rfl

private lemma heq_star_stage {m n : ℕ} (h : m = n) {X : UHFStage m} {Y : UHFStage n}
    (heq : HEq X Y) : HEq (star X) (star Y) := by
  subst h
  cases eq_of_heq heq
  rfl

/-!
## Part 3: Colimit Setoid and the Directed Colimit Algebra `UHFAlg`
-/

/-- Directed colimit equivalence relation on $\Sigma\, n : \mathbb{N},\, M_{2^n}(\mathbb{C})$. -/
def UHFRel (u v : Σ n : ℕ, UHFStage n) : Prop :=
  ∃ (k₁ k₂ : ℕ), u.1 + k₁ = v.1 + k₂ ∧
    HEq (uhfStepIter k₁ u.2) (uhfStepIter k₂ v.2)

theorem uhfRel_trans {u v w : Σ n : ℕ, UHFStage n}
    (huv : UHFRel u v) (hvw : UHFRel v w) : UHFRel u w := by
  rcases huv with ⟨k₁, k₂, h12, heq12⟩
  rcases hvw with ⟨l₁, l₂, h23, heq23⟩
  refine ⟨k₁ + l₁, l₂ + k₂, by omega, ?_⟩
  exact (uhfStepIter_add_heq k₁ l₁ u.2).trans <|
    (uhfStepIter_congr_heq l₁ h12 heq12).trans <|
    (uhfStepIter_add_heq k₂ l₁ v.2).symm.trans <|
    (uhfStepIter_comm_heq k₂ l₁ v.2).trans <|
    (uhfStepIter_add_heq l₁ k₂ v.2).trans <|
    (uhfStepIter_congr_heq k₂ h23 heq23).trans <|
    (uhfStepIter_add_heq l₂ k₂ w.2).symm

/-- Certified `Setoid` instance for the inductive colimit $2^\infty$ UHF algebra. -/
instance uhfSetoid : Setoid (Σ n : ℕ, UHFStage n) where
  r := UHFRel
  iseqv := {
    refl  := fun _ => ⟨0, 0, rfl, HEq.rfl⟩
    symm  := fun ⟨k₁, k₂, h, heq⟩ => ⟨k₂, k₁, h.symm, heq.symm⟩
    trans := uhfRel_trans
  }

/-- The universal inductive colimit algebra $\mathcal{UHF} = \mathrm{Quotient}(\mathrm{uhfSetoid})$. -/
abbrev UHFAlg := Quotient uhfSetoid

/-- Canonical colimit inclusion $\pi_n : M_{2^n}(\mathbb{C}) \to \mathcal{UHF}$. -/
def toUHF (n : ℕ) (X : UHFStage n) : UHFAlg :=
  Quotient.mk uhfSetoid ⟨n, X⟩

lemma toUHF_castStage {m n : ℕ} (h : m = n) (X : UHFStage m) :
    toUHF n (castStage h X) = toUHF m X := by
  subst h
  rfl

lemma toUHF_uhfStepIter {n : ℕ} (k : ℕ) (X : UHFStage n) :
    toUHF (n + k) (uhfStepIter k X) = toUHF n X := by
  apply Quotient.sound
  exact ⟨0, k, rfl, HEq.rfl⟩

lemma toUHF_uhfStep (n : ℕ) (X : UHFStage n) :
    toUHF (n + 1) (uhfStep n X) = toUHF n X :=
  toUHF_uhfStepIter 1 X

lemma exists_toUHF (x : UHFAlg) : ∃ (n : ℕ) (X : UHFStage n), x = toUHF n X := by
  rcases Quotient.exists_rep x with ⟨⟨n, X⟩, rfl⟩
  exact ⟨n, X, rfl⟩

private lemma uhfStepIter_split_heq {n k₁ k₂ k : ℕ} (X : UHFStage n)
    (h : k₁ + k₂ = k) :
    HEq (uhfStepIter k₂ (uhfStepIter k₁ X)) (uhfStepIter k X) := by
  refine HEq.trans (uhfStepIter_add_heq k₁ k₂ X).symm ?_
  subst h
  rfl

private lemma uhfStepIter_congr_heq_dim {m₁ m₂ : ℕ} (d₁ d₂ : ℕ)
    {X : UHFStage m₁} {Y : UHFStage m₂}
    (h_dim : m₁ = m₂) (hd : d₁ = d₂) (h_heq : HEq X Y) :
    HEq (uhfStepIter d₁ X) (uhfStepIter d₂ Y) := by
  subst hd
  exact uhfStepIter_congr_heq d₁ h_dim h_heq

private lemma toUHF_binop_stabilize
    (op : ∀ n : ℕ, UHFStage n → UHFStage n → UHFStage n)
    (h_emb : ∀ (n k : ℕ) (X Y : UHFStage n),
      uhfStepIter k (op n X Y) = op (n + k) (uhfStepIter k X) (uhfStepIter k Y))
    (h_cast : ∀ {m n : ℕ} (h : m = n) (X Y : UHFStage m),
      castStage h (op m X Y) = op n (castStage h X) (castStage h Y))
    (u v : Σ n : ℕ, UHFStage n) {M N : ℕ}
    (huM : u.1 ≤ M) (hvM : v.1 ≤ M) (hMN : M ≤ N) :
    toUHF M
      (op M (castStage (Nat.add_sub_cancel' huM) (uhfStepIter (M - u.1) u.2))
            (castStage (Nat.add_sub_cancel' hvM) (uhfStepIter (M - v.1) v.2))) =
    toUHF N
      (op N (castStage (Nat.add_sub_cancel' (le_trans huM hMN)) (uhfStepIter (N - u.1) u.2))
            (castStage (Nat.add_sub_cancel' (le_trans hvM hMN)) (uhfStepIter (N - v.1) v.2))) := by
  rw [← toUHF_uhfStepIter (N - M), h_emb]
  have h_dim : M + (N - M) = N := Nat.add_sub_cancel' hMN
  rw [← toUHF_castStage h_dim, h_cast h_dim]
  congr 2
  · apply eq_of_heq_stage rfl
    refine HEq.trans (castStage_heq _ _) ?_
    rw [uhfStepIter_castStage]
    refine HEq.trans (castStage_heq _ _) ?_
    refine HEq.trans (uhfStepIter_split_heq u.2 (by omega)) (castStage_heq _ _).symm
  · apply eq_of_heq_stage rfl
    refine HEq.trans (castStage_heq _ _) ?_
    rw [uhfStepIter_castStage]
    refine HEq.trans (castStage_heq _ _) ?_
    refine HEq.trans (uhfStepIter_split_heq v.2 (by omega)) (castStage_heq _ _).symm

private lemma lift_binop_wd
    (op : ∀ n : ℕ, UHFStage n → UHFStage n → UHFStage n)
    (h_emb : ∀ (n k : ℕ) (X Y : UHFStage n),
      uhfStepIter k (op n X Y) = op (n + k) (uhfStepIter k X) (uhfStepIter k Y))
    (h_cast : ∀ {m n : ℕ} (h : m = n) (X Y : UHFStage m),
      castStage h (op m X Y) = op n (castStage h X) (castStage h Y))
    {u₁ u₂ v₁ v₂ : Σ n : ℕ, UHFStage n}
    (hu : UHFRel u₁ u₂) (hv : UHFRel v₁ v₂) :
    toUHF (max u₁.1 v₁.1)
      (op (max u₁.1 v₁.1)
        (castStage (Nat.add_sub_cancel' (le_max_left u₁.1 v₁.1))
          (uhfStepIter (max u₁.1 v₁.1 - u₁.1) u₁.2))
        (castStage (Nat.add_sub_cancel' (le_max_right u₁.1 v₁.1))
          (uhfStepIter (max u₁.1 v₁.1 - v₁.1) v₁.2))) =
    toUHF (max u₂.1 v₂.1)
      (op (max u₂.1 v₂.1)
        (castStage (Nat.add_sub_cancel' (le_max_left u₂.1 v₂.1))
          (uhfStepIter (max u₂.1 v₂.1 - u₂.1) u₂.2))
        (castStage (Nat.add_sub_cancel' (le_max_right u₂.1 v₂.1))
          (uhfStepIter (max u₂.1 v₂.1 - v₂.1) v₂.2))) := by
  rcases hu with ⟨k₁, k₂, h_u, heq_u⟩
  rcases hv with ⟨l₁, l₂, h_v, heq_v⟩
  set M₁ := max u₁.1 v₁.1
  set M₂ := max u₂.1 v₂.1
  set M  := max (u₁.1 + k₁) (v₁.1 + l₁)
  set N  := M₁ + M₂ + M
  have hN₁ : M₁ ≤ N := le_trans (Nat.le_add_right M₁ M₂) (Nat.le_add_right _ M)
  have hN₂ : M₂ ≤ N := le_trans (Nat.le_add_left M₂ M₁) (Nat.le_add_right _ M)
  rw [toUHF_binop_stabilize op h_emb h_cast u₁ v₁ (le_max_left _ _) (le_max_right _ _) hN₁]
  rw [toUHF_binop_stabilize op h_emb h_cast u₂ v₂ (le_max_left _ _) (le_max_right _ _) hN₂]
  have hu_eq :
      castStage (Nat.add_sub_cancel' (le_trans (le_max_left u₁.1 v₁.1) hN₁))
        (uhfStepIter (N - u₁.1) u₁.2) =
      castStage (Nat.add_sub_cancel' (le_trans (le_max_left u₂.1 v₂.1) hN₂))
        (uhfStepIter (N - u₂.1) u₂.2) := by
    apply eq_of_heq_stage rfl
    refine HEq.trans (castStage_heq _ _) ?_
    refine HEq.trans ?_ (castStage_heq _ _).symm
    have heq_step :
        HEq (uhfStepIter (N - (u₁.1 + k₁)) (uhfStepIter k₁ u₁.2))
            (uhfStepIter (N - (u₂.1 + k₂)) (uhfStepIter k₂ u₂.2)) :=
      uhfStepIter_congr_heq_dim (N - (u₁.1 + k₁)) (N - (u₂.1 + k₂)) h_u (by omega) heq_u
    exact (uhfStepIter_split_heq u₁.2 (by omega : k₁ + (N - (u₁.1 + k₁)) = N - u₁.1)).symm.trans
      (heq_step.trans (uhfStepIter_split_heq u₂.2 (by omega : k₂ + (N - (u₂.1 + k₂)) = N - u₂.1)))
  have hv_eq :
      castStage (Nat.add_sub_cancel' (le_trans (le_max_right u₁.1 v₁.1) hN₁))
        (uhfStepIter (N - v₁.1) v₁.2) =
      castStage (Nat.add_sub_cancel' (le_trans (le_max_right u₂.1 v₂.1) hN₂))
        (uhfStepIter (N - v₂.1) v₂.2) := by
    apply eq_of_heq_stage rfl
    refine HEq.trans (castStage_heq _ _) ?_
    refine HEq.trans ?_ (castStage_heq _ _).symm
    have heq_step :
        HEq (uhfStepIter (N - (v₁.1 + l₁)) (uhfStepIter l₁ v₁.2))
            (uhfStepIter (N - (v₂.1 + l₂)) (uhfStepIter l₂ v₂.2)) :=
      uhfStepIter_congr_heq_dim (N - (v₁.1 + l₁)) (N - (v₂.1 + l₂)) h_v (by omega) heq_v
    exact (uhfStepIter_split_heq v₁.2 (by omega : l₁ + (N - (v₁.1 + l₁)) = N - v₁.1)).symm.trans
      (heq_step.trans (uhfStepIter_split_heq v₂.2 (by omega : l₂ + (N - (v₂.1 + l₂)) = N - v₂.1)))
  rw [hu_eq, hv_eq]

private def addUHF (x y : UHFAlg) : UHFAlg :=
  Quotient.liftOn₂ x y
    (fun u v =>
      let M := max u.1 v.1
      toUHF M
        (castStage (Nat.add_sub_cancel' (le_max_left u.1 v.1))
          (uhfStepIter (M - u.1) u.2) +
         castStage (Nat.add_sub_cancel' (le_max_right u.1 v.1))
          (uhfStepIter (M - v.1) v.2)))
    (fun _ _ _ _ hu hv =>
      lift_binop_wd (fun _ X Y => X + Y)
        (fun _ _ _ _ => uhfStepIter_add _ _ _)
        (fun h _ _ => castStage_add h _ _) hu hv)

private def mulUHF (x y : UHFAlg) : UHFAlg :=
  Quotient.liftOn₂ x y
    (fun u v =>
      let M := max u.1 v.1
      toUHF M
        (castStage (Nat.add_sub_cancel' (le_max_left u.1 v.1))
          (uhfStepIter (M - u.1) u.2) *
         castStage (Nat.add_sub_cancel' (le_max_right u.1 v.1))
          (uhfStepIter (M - v.1) v.2)))
    (fun _ _ _ _ hu hv =>
      lift_binop_wd (fun _ X Y => X * Y)
        (fun _ _ _ _ => uhfStepIter_mul _ _ _)
        (fun h _ _ => castStage_mul h _ _) hu hv)

private def negUHF (x : UHFAlg) : UHFAlg :=
  Quotient.liftOn x
    (fun u => toUHF u.1 (-u.2))
    (fun _ _ ⟨k₁, k₂, h_dim, heq_u⟩ => by
      apply Quotient.sound
      refine ⟨k₁, k₂, h_dim, ?_⟩
      rw [uhfStepIter_neg, uhfStepIter_neg]
      exact heq_neg_stage h_dim heq_u)

private def starUHF (x : UHFAlg) : UHFAlg :=
  Quotient.liftOn x
    (fun u => toUHF u.1 (star u.2))
    (fun _ _ ⟨k₁, k₂, h_dim, heq_u⟩ => by
      apply Quotient.sound
      refine ⟨k₁, k₂, h_dim, ?_⟩
      rw [uhfStepIter_star, uhfStepIter_star]
      exact heq_star_stage h_dim heq_u)

instance instAddUHFAlg : Add UHFAlg := ⟨addUHF⟩
instance instMulUHFAlg : Mul UHFAlg := ⟨mulUHF⟩
instance instNegUHFAlg : Neg UHFAlg := ⟨negUHF⟩
instance instStarUHFAlg : Star UHFAlg := ⟨starUHF⟩
instance instZeroUHFAlg : Zero UHFAlg := ⟨toUHF 0 0⟩
instance instOneUHFAlg : One UHFAlg := ⟨toUHF 0 1⟩

lemma toUHF_zero (n : ℕ) : toUHF n 0 = (0 : UHFAlg) := by
  change toUHF n 0 = toUHF 0 0
  apply Quotient.sound
  refine ⟨0, n, (Nat.zero_add n).symm, ?_⟩
  have hb : uhfStepIter n (0 : UHFStage 0) = 0 := uhfStepIter_zero n
  rw [hb]
  exact heq_zero_stage (Nat.zero_add n).symm

lemma toUHF_one (n : ℕ) : toUHF n 1 = (1 : UHFAlg) := by
  change toUHF n 1 = toUHF 0 1
  apply Quotient.sound
  refine ⟨0, n, (Nat.zero_add n).symm, ?_⟩
  have hb : uhfStepIter n (1 : UHFStage 0) = 1 := uhfStepIter_one n
  rw [hb]
  exact heq_one_stage (Nat.zero_add n).symm

private lemma castStage_uhfStepIter_max {n : ℕ} (h : n + (max n n - n) = max n n)
    (X : UHFStage n) :
    castStage h (uhfStepIter (max n n - n) X) = castStage (max_self n).symm X := by
  apply eq_of_heq_stage rfl
  refine HEq.trans (castStage_heq _ _) ?_
  refine HEq.trans ?_ (castStage_heq _ _).symm
  have hz : max n n - n = 0 := by omega
  rw [hz]
  rfl

@[simp] lemma add_toUHF (n : ℕ) (X Y : UHFStage n) :
    toUHF n X + toUHF n Y = toUHF n (X + Y) := by
  change addUHF (toUHF n X) (toUHF n Y) = toUHF n (X + Y)
  simp only [addUHF, toUHF, Quotient.liftOn₂_mk]
  rw [castStage_uhfStepIter_max (Nat.add_sub_cancel' (le_max_left n n)),
      castStage_uhfStepIter_max (Nat.add_sub_cancel' (le_max_right n n)),
      ← castStage_add]
  exact toUHF_castStage _ _

@[simp] lemma mul_toUHF (n : ℕ) (X Y : UHFStage n) :
    toUHF n X * toUHF n Y = toUHF n (X * Y) := by
  change mulUHF (toUHF n X) (toUHF n Y) = toUHF n (X * Y)
  simp only [mulUHF, toUHF, Quotient.liftOn₂_mk]
  rw [castStage_uhfStepIter_max (Nat.add_sub_cancel' (le_max_left n n)),
      castStage_uhfStepIter_max (Nat.add_sub_cancel' (le_max_right n n)),
      ← castStage_mul]
  exact toUHF_castStage _ _

@[simp] lemma neg_toUHF (n : ℕ) (X : UHFStage n) :
    -(toUHF n X) = toUHF n (-X) := by
  change negUHF (toUHF n X) = toUHF n (-X)
  rfl

@[simp] lemma star_toUHF (n : ℕ) (X : UHFStage n) :
    star (toUHF n X) = toUHF n (star X) := by
  change starUHF (toUHF n X) = toUHF n (star X)
  rfl

lemma toUHF_lift_three (x y z : UHFAlg) :
    ∃ (n : ℕ) (X Y Z : UHFStage n),
      x = toUHF n X ∧ y = toUHF n Y ∧ z = toUHF n Z := by
  rcases Quotient.exists_rep x with ⟨⟨n₁, X₁⟩, rfl⟩
  rcases Quotient.exists_rep y with ⟨⟨n₂, X₂⟩, rfl⟩
  rcases Quotient.exists_rep z with ⟨⟨n₃, X₃⟩, rfl⟩
  set N := max n₁ (max n₂ n₃)
  refine ⟨N,
    castStage (by omega : n₁ + (N - n₁) = N) (uhfStepIter (N - n₁) X₁),
    castStage (by omega : n₂ + (N - n₂) = N) (uhfStepIter (N - n₂) X₂),
    castStage (by omega : n₃ + (N - n₃) = N) (uhfStepIter (N - n₃) X₃),
    ?_, ?_, ?_⟩ <;>
  · rw [toUHF_castStage, toUHF_uhfStepIter]
    rfl

lemma toUHF_lift_two (x y : UHFAlg) :
    ∃ (n : ℕ) (X Y : UHFStage n),
      x = toUHF n X ∧ y = toUHF n Y := by
  rcases toUHF_lift_three x y 0 with ⟨n, X, Y, _, hx, hy, _⟩
  exact ⟨n, X, Y, hx, hy⟩

/-- Genuine unital `Ring` structure on `UHFAlg`. -/
instance instRingUHFAlg : Ring UHFAlg where
  add_assoc x y z := by
    rcases toUHF_lift_three x y z with ⟨n, X, Y, Z, rfl, rfl, rfl⟩
    simp [add_assoc]
  zero_add x := by
    rcases exists_toUHF x with ⟨n, X, rfl⟩
    rw [← toUHF_zero n, add_toUHF, zero_add]
  add_zero x := by
    rcases exists_toUHF x with ⟨n, X, rfl⟩
    rw [← toUHF_zero n, add_toUHF, add_zero]
  neg_add_cancel x := by
    rcases exists_toUHF x with ⟨n, X, rfl⟩
    rw [neg_toUHF, add_toUHF, neg_add_cancel, toUHF_zero]
  add_comm x y := by
    rcases toUHF_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
    simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc x y z := by
    rcases toUHF_lift_three x y z with ⟨n, X, Y, Z, rfl, rfl, rfl⟩
    simp [mul_assoc]
  zero_mul x := by
    rcases exists_toUHF x with ⟨n, X, rfl⟩
    rw [← toUHF_zero n, mul_toUHF, zero_mul, toUHF_zero]
  mul_zero x := by
    rcases exists_toUHF x with ⟨n, X, rfl⟩
    rw [← toUHF_zero n, mul_toUHF, mul_zero, toUHF_zero]
  one_mul x := by
    rcases exists_toUHF x with ⟨n, X, rfl⟩
    rw [← toUHF_one n, mul_toUHF, one_mul]
  mul_one x := by
    rcases exists_toUHF x with ⟨n, X, rfl⟩
    rw [← toUHF_one n, mul_toUHF, mul_one]
  left_distrib x y z := by
    rcases toUHF_lift_three x y z with ⟨n, X, Y, Z, rfl, rfl, rfl⟩
    simp [left_distrib]
  right_distrib x y z := by
    rcases toUHF_lift_three x y z with ⟨n, X, Y, Z, rfl, rfl, rfl⟩
    simp [right_distrib]

/-- Genuine `StarRing` structure on `UHFAlg`. -/
instance instStarRingUHFAlg : StarRing UHFAlg where
  star_involutive x := by
    rcases exists_toUHF x with ⟨n, X, rfl⟩
    rw [star_toUHF, star_toUHF, star_star]
  star_mul x y := by
    rcases toUHF_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
    rw [mul_toUHF, star_toUHF, star_toUHF, star_toUHF, star_mul, mul_toUHF]
  star_add x y := by
    rcases toUHF_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
    rw [add_toUHF, star_toUHF, star_toUHF, star_toUHF, star_add, add_toUHF]

/-!
## Part 4: C*-Norm on `UHFAlg` and Non-Commutativity
-/

private lemma uhfNorm_eq_of_heq {m₁ m₂ : ℕ} {X : UHFStage m₁} {Y : UHFStage m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) : ‖X‖ = ‖Y‖ := by
  subst h_dim
  cases eq_of_heq h_heq
  rfl

private lemma uhfNorm_well_defined
    (u v : Σ n : ℕ, UHFStage n) (h_rel : UHFRel u v) :
    ‖u.2‖ = ‖v.2‖ := by
  rcases h_rel with ⟨k₁, k₂, h_dim, h_heq⟩
  calc ‖u.2‖
    _ = ‖uhfStepIter k₁ u.2‖ := (uhfStepIter_norm k₁ u.2).symm
    _ = ‖uhfStepIter k₂ v.2‖ := uhfNorm_eq_of_heq h_dim h_heq
    _ = ‖v.2‖                := uhfStepIter_norm k₂ v.2

/-- Exact C*-norm on `UHFAlg`. -/
noncomputable def uhfNorm : UHFAlg → ℝ :=
  Quotient.lift (fun u => ‖u.2‖) uhfNorm_well_defined

@[simp] private lemma uhfNorm_toUHF (n : ℕ) (X : UHFStage n) :
    uhfNorm (toUHF n X) = ‖X‖ := by
  show uhfNorm (toUHF n X) = ‖X‖
  rfl

lemma norm_star_toUHF (n : ℕ) (X : UHFStage n) :
    uhfNorm (star (toUHF n X)) = uhfNorm (toUHF n X) := by
  rw [star_toUHF, uhfNorm_toUHF, uhfNorm_toUHF, norm_star]

theorem norm_star_uhf (x : UHFAlg) : uhfNorm (star x) = uhfNorm x := by
  rcases exists_toUHF x with ⟨n, X, rfl⟩
  exact norm_star_toUHF n X

lemma eq_zero_of_toUHF_norm_zero (x : UHFAlg) (hx : uhfNorm x = 0) : x = 0 := by
  rcases exists_toUHF x with ⟨n, X, rfl⟩
  rw [uhfNorm_toUHF, norm_eq_zero] at hx
  rw [hx, toUHF_zero]

/-- Bundled `AddGroupNorm` on `UHFAlg`. -/
noncomputable def uhfAddGroupNorm : AddGroupNorm UHFAlg where
  toFun := uhfNorm
  map_zero' := by
    change uhfNorm (0 : UHFAlg) = 0
    rw [← toUHF_zero 0, uhfNorm_toUHF, norm_zero]
  add_le' := fun x y => by
    rcases toUHF_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
    rw [add_toUHF, uhfNorm_toUHF, uhfNorm_toUHF, uhfNorm_toUHF]
    exact norm_add_le X Y
  neg' := fun x => by
    rcases exists_toUHF x with ⟨n, X, rfl⟩
    rw [neg_toUHF, uhfNorm_toUHF, uhfNorm_toUHF, norm_neg]
  eq_zero_of_map_eq_zero' := eq_zero_of_toUHF_norm_zero

noncomputable instance instNormedAddCommGroupUHFAlg : NormedAddCommGroup UHFAlg :=
  uhfAddGroupNorm.toNormedAddCommGroup

@[simp] private lemma norm_toUHF (n : ℕ) (X : UHFStage n) :
    ‖toUHF n X‖ = ‖X‖ := by
  show ‖toUHF n X‖ = ‖X‖
  rfl

/-- Auxiliary additive map for star on `UHFAlg`. -/
def uhfStarAddMonoidHom : UHFAlg →+ UHFAlg where
  toFun := Star.star
  map_zero' := by rw [← toUHF_zero 0, star_toUHF, star_zero]
  map_add' := fun x y => star_add x y

theorem uhfStar_isometry : Isometry (Star.star : UHFAlg → UHFAlg) :=
  AddMonoidHomClass.isometry_of_norm uhfStarAddMonoidHom norm_star_uhf

/-- Genuine `NormedRing` structure on `UHFAlg`. -/
noncomputable instance instNormedRingUHFAlg : NormedRing UHFAlg where
  __ : NormedAddCommGroup UHFAlg := inferInstance
  __ : Ring UHFAlg := inferInstance
  norm_mul_le x y := by
    rcases toUHF_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
    rw [mul_toUHF, norm_toUHF, norm_toUHF, norm_toUHF]
    exact norm_mul_le X Y

/-- **Certified C*-Identity on `UHFAlg`**:
Every element satisfies $\|x^* x\| \ge \|x\|^2$. -/
noncomputable instance instCStarRingUHFAlg : CStarRing UHFAlg where
  norm_mul_self_le x := by
    rcases exists_toUHF x with ⟨n, X, rfl⟩
    rw [star_toUHF, mul_toUHF, norm_toUHF, norm_toUHF]
    exact CStarRing.norm_mul_self_le X

/-- Certified unit norm: $\|1\| = 1$. -/
theorem uhf_norm_one : ‖(1 : UHFAlg)‖ = 1 := by
  change ‖toUHF 0 1‖ = 1
  rw [norm_toUHF]
  exact norm_one

/-- **OpenGauss T16 Non-Commutativity Certification**:
The inductive colimit algebra $\mathcal{UHF}$ is strictly non-commutative. -/
theorem uhf_noncomm : ∃ (x y : UHFAlg), x * y ≠ y * x := by
  set X : UHFStage 1 := ![![0, 1], ![0, 0]]
  set Y : UHFStage 1 := ![![0, 0], ![1, 0]]
  use toUHF 1 X, toUHF 1 Y
  rw [mul_toUHF, mul_toUHF]
  intro h_eq
  have h_rel : UHFRel ⟨1, X * Y⟩ ⟨1, Y * X⟩ := Quotient.exact h_eq
  rcases h_rel with ⟨k₁, k₂, h_dim, h_heq⟩
  dsimp at h_dim
  have hk : k₁ = k₂ := by omega
  subst hk
  have h_eq_mat : uhfStepIter k₁ (X * Y) = uhfStepIter k₁ (Y * X) := eq_of_heq h_heq
  have h_iso : ‖uhfStepIter k₁ (X * Y) - uhfStepIter k₁ (Y * X)‖ = ‖X * Y - Y * X‖ := by
    have h_sub : uhfStepIter k₁ (X * Y) - uhfStepIter k₁ (Y * X) =
        uhfStepIter k₁ (X * Y - Y * X) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, uhfStepIter_add, uhfStepIter_neg]
    rw [h_sub, uhfStepIter_norm]
  rw [h_eq_mat, sub_self, norm_zero] at h_iso
  have h_zero : X * Y - Y * X = 0 := norm_eq_zero.mp h_iso.symm
  have h_contra : (X * Y - Y * X) 0 0 = 0 := by
    rw [h_zero, Matrix.zero_apply]
  have h_val : (X * Y - Y * X) 0 0 = 1 := by
    change (∑ j : Fin 2, (X 0 j * Y j 0)) - (∑ j : Fin 2, (Y 0 j * X j 0)) = 1
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    dsimp [X, Y]
    ring
  rw [h_val] at h_contra
  exact one_ne_zero h_contra

/-!
## Part 5: Complete C*-Algebra Completion `UHFCStar`
-/

/-- Complete $2^\infty$ UHF C*-algebra $\widehat{\mathcal{UHF}} = \mathrm{Completion}(\mathcal{UHF})$. -/
abbrev UHFCStar := UniformSpace.Completion UHFAlg

noncomputable instance instNormedRingUHFCStar : NormedRing UHFCStar :=
  inferInstance

noncomputable instance instCompleteSpaceUHFCStar : CompleteSpace UHFCStar :=
  inferInstance

/-- Canonical dense inclusion $\iota : \mathcal{UHF} \to \widehat{\mathcal{UHF}}$. -/
noncomputable def toUHFCStar (x : UHFAlg) : UHFCStar := (x : UHFCStar)

/-- Continuous extension of $\star$-involution to `UHFCStar`. -/
noncomputable def uhfCStar_star : UHFCStar → UHFCStar :=
  UniformSpace.Completion.map Star.star

noncomputable instance instStarUHFCStar : Star UHFCStar where
  star := uhfCStar_star

lemma toUHFCStar_star (x : UHFAlg) :
    star (toUHFCStar x) = toUHFCStar (star x) :=
  UniformSpace.Completion.map_coe uhfStar_isometry.uniformContinuous x

noncomputable instance instInvolutiveStarUHFCStar : InvolutiveStar UHFCStar where
  star_involutive z := by
    induction z using UniformSpace.Completion.induction_on with
    | hp =>
        exact isClosed_eq
          ((UniformSpace.Completion.continuous_map (f := (Star.star : UHFAlg → UHFAlg))).comp
            (UniformSpace.Completion.continuous_map (f := (Star.star : UHFAlg → UHFAlg))))
          continuous_id
    | ih x =>
        change uhfCStar_star (uhfCStar_star (x : UHFCStar)) = (x : UHFCStar)
        dsimp only [uhfCStar_star]
        rw [UniformSpace.Completion.map_coe uhfStar_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe uhfStar_isometry.uniformContinuous,
            star_star]

noncomputable instance instStarAddMonoidUHFCStar : StarAddMonoid UHFCStar where
  star_add z w := by
    induction z, w using UniformSpace.Completion.induction_on₂ with
    | hp =>
        exact isClosed_eq
          ((UniformSpace.Completion.continuous_map (f := (Star.star : UHFAlg → UHFAlg))).comp
            continuous_add)
          (((UniformSpace.Completion.continuous_map (f := (Star.star : UHFAlg → UHFAlg))).comp
            continuous_fst).add
           ((UniformSpace.Completion.continuous_map (f := (Star.star : UHFAlg → UHFAlg))).comp
            continuous_snd))
    | ih x y =>
        change uhfCStar_star ((x : UHFCStar) + (y : UHFCStar)) =
          uhfCStar_star (x : UHFCStar) + uhfCStar_star (y : UHFCStar)
        dsimp only [uhfCStar_star]
        rw [← UniformSpace.Completion.coe_add,
            UniformSpace.Completion.map_coe uhfStar_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe uhfStar_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe uhfStar_isometry.uniformContinuous,
            ← UniformSpace.Completion.coe_add, star_add]

noncomputable instance instStarMulUHFCStar : StarMul UHFCStar where
  star_mul z w := by
    induction z, w using UniformSpace.Completion.induction_on₂ with
    | hp =>
        exact isClosed_eq
          ((UniformSpace.Completion.continuous_map (f := (Star.star : UHFAlg → UHFAlg))).comp
            continuous_mul)
          (((UniformSpace.Completion.continuous_map (f := (Star.star : UHFAlg → UHFAlg))).comp
            continuous_snd).mul
           ((UniformSpace.Completion.continuous_map (f := (Star.star : UHFAlg → UHFAlg))).comp
            continuous_fst))
    | ih x y =>
        change uhfCStar_star ((x : UHFCStar) * (y : UHFCStar)) =
          uhfCStar_star (y : UHFCStar) * uhfCStar_star (x : UHFCStar)
        dsimp only [uhfCStar_star]
        rw [← UniformSpace.Completion.coe_mul,
            UniformSpace.Completion.map_coe uhfStar_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe uhfStar_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe uhfStar_isometry.uniformContinuous,
            ← UniformSpace.Completion.coe_mul, star_mul]

/-- Genuine `StarRing` structure on `UHFCStar`. -/
noncomputable instance instStarRingUHFCStar : StarRing UHFCStar where
  star_involutive := instInvolutiveStarUHFCStar.star_involutive
  star_mul := instStarMulUHFCStar.star_mul
  star_add := instStarAddMonoidUHFCStar.star_add

/-- **Full C*-Algebra Structure on `UHFCStar`**:
The completion satisfies the exact C*-norm identity $\|z^* z\| \ge \|z\|^2$. -/
noncomputable instance instCStarRingUHFCStar : CStarRing UHFCStar where
  norm_mul_self_le z := by
    induction z using UniformSpace.Completion.induction_on with
    | hp =>
        exact isClosed_le
          (continuous_norm.mul continuous_norm)
          (continuous_norm.comp
            (((UniformSpace.Completion.continuous_map (f := (Star.star : UHFAlg → UHFAlg)))).mul
              continuous_id))
    | ih x =>
        change ‖(x : UHFCStar)‖ * ‖(x : UHFCStar)‖ ≤
          ‖uhfCStar_star (x : UHFCStar) * (x : UHFCStar)‖
        dsimp only [uhfCStar_star]
        rw [UniformSpace.Completion.map_coe uhfStar_isometry.uniformContinuous,
            ← UniformSpace.Completion.coe_mul]
        simp only [UniformSpace.Completion.norm_coe]
        exact CStarRing.norm_mul_self_le x

end InfoGeometry.Algebra.UHFColimitCStarCompletion
