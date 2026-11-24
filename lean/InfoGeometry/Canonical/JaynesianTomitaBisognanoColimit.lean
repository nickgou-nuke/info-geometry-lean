/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteMatrixTomitaPolar
import InfoGeometry.Canonical.Pin55BisognanoWichmannBoost
import InfoGeometry.NCG.CategoricalInductiveColimitKMSBridge

/-!
# Jaynesian Inductive Colimit Tomita Polar & Pin(5,5) Bisognano–Wichmann Closure (`D20–D22`)

Under the repository's colimit-continuum law, the admissible infinite limit is
the **Jaynesian inductive colimit** of finite matrix stages rather than a
postulated non-inductive von Neumann or AQFT continuum.  This module lifts
`FiniteMatrixTomitaPolar` (`D20`) and `Pin55BisognanoWichmannBoost` (`D21`, `D22`)
into the directed block-doubling colimit algebra `RealBlockColimit m`:

1. **Real Block-Doubling Tower `RealBlockStage m k`**:
   Doubling embeddings `realBlockStep m k : M_{m·2^k}(ℝ) → M_{m·2^{k+1}}(ℝ)`,
   iterated embeddings `realBlockIter`, injectivity, and exact invariance of the
   normalized Hilbert–Schmidt inner product `normHSInner`.
2. **Jaynesian Inductive Colimit Ring `RealBlockColimit m`**:
   Directed quotient `Quotient (realBlockSetoid m)` carrying genuine `Ring`,
   `Module ℝ`, `StarRing` (transpose involution), faithful `colimitHSInner`, and
   exact instantiation of `InfoGeometry.NCG.ColimitKMS.InductiveSystem` and
   `StarAlgebraCocone`.
3. **Colimit Tomita–Takesaki Polar Decomposition & KMS (`D20`)**:
   Lifts any finite density factor `ρ : PositiveRealDensityFactor m` across all
   stages `towerDensity ρ k` to `colimitTomitaOp`, `colimitTomitaAdjOp`,
   `colimitModularOp`, `colimitModularSqrt`, and `colimitState`, proving
   `S = J Δ^{1/2}`, `S² = id`, `F ∘ S = Δ`, HS adjointness, `ModularFlow`,
   `colimit_modularOp_kms_identity`, and non-commutativity (`colimit_diag2_noncomm`).
4. **Colimit Pin(5,5) Bisognano–Wichmann Boost & Wedge KMS Semigroup (`D21–D22`)**:
   Lifts `J55`, `pin55Boost η`, `wedgeBoostFlow t`, `lightconeModePlus`, and
   `lightconeModeMinus` to `RealBlockColimit 10`, proving Krein isometry,
   `Δ_{ρ(2π)} = σ₁`, the boost semigroup, the wedge KMS boundary condition at
   inverse Unruh temperature `1 / unruhTemperature a`, forward lightcone
   contractivity, and opposite-mode expansion in the Jaynesian inductive colimit.
-/

noncomputable section

namespace InfoGeometry.Canonical.JaynesianTomitaBisognanoColimit

open Matrix
open InfoGeometry.Canonical.FiniteMatrixTomitaPolar
open InfoGeometry.Canonical.BisognanoPeirceProjectionCore
open InfoGeometry.Lie.Pin55NondegenerateKreinBridge
open InfoGeometry.Canonical.Pin55BisognanoWichmannBoost
open InfoGeometry.NCG.ColimitKMS

/-!
## 1. Real Block-Doubling Inductive Tower
-/

/-- Stage dimension `m * 2^k` defined recursively so `blockDim m 0 = m` is definitional. -/
@[reducible]
def blockDim (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => 2 * blockDim m k

@[simp]
theorem blockDim_zero (m : ℕ) : blockDim m 0 = m := rfl

/-- Stage-`k` real matrix algebra of size `(m * 2^k) × (m * 2^k)`. -/
abbrev RealBlockStage (m k : ℕ) : Type :=
  Matrix (Fin (blockDim m k)) (Fin (blockDim m k)) ℝ

/-- Index equivalence `(Fin (blockDim m k)) ⊕ (Fin (blockDim m k)) ≃ Fin (blockDim m (k + 1))`. -/
def finSumBlock (m k : ℕ) :
    Fin (blockDim m k) ⊕ Fin (blockDim m k) ≃ Fin (blockDim m (k + 1)) :=
  finSumFinEquiv.trans
    (Fin.castOrderIso (by
      change blockDim m k + blockDim m k = 2 * blockDim m k
      exact (two_mul (blockDim m k)).symm)).toEquiv

/-- Real block-doubling step embedding `A ↦ diag(A, A)`. -/
def realBlockStep (m k : ℕ) (A : RealBlockStage m k) : RealBlockStage m (k + 1) :=
  Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k) (Matrix.fromBlocks A 0 0 A)

lemma realBlockStep_zero (m k : ℕ) : realBlockStep m k 0 = 0 := by
  change Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k) (Matrix.fromBlocks 0 0 0 0) = 0
  rw [Matrix.fromBlocks_zero, map_zero]

lemma realBlockStep_one (m k : ℕ) : realBlockStep m k 1 = 1 := by
  change Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k) (Matrix.fromBlocks 1 0 0 1) = 1
  rw [Matrix.fromBlocks_one, map_one]

lemma realBlockStep_add (m k : ℕ) (A B : RealBlockStage m k) :
    realBlockStep m k (A + B) = realBlockStep m k A + realBlockStep m k B := by
  change Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k)
      (Matrix.fromBlocks (A + B) 0 0 (A + B)) =
    Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k) (Matrix.fromBlocks A 0 0 A) +
    Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k) (Matrix.fromBlocks B 0 0 B)
  rw [← map_add]
  congr 1
  ext (i | i) (j | j) <;> simp

lemma realBlockStep_neg (m k : ℕ) (A : RealBlockStage m k) :
    realBlockStep m k (-A) = -realBlockStep m k A := by
  change Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k)
      (Matrix.fromBlocks (-A) 0 0 (-A)) =
    -Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k) (Matrix.fromBlocks A 0 0 A)
  rw [← map_neg]
  congr 1
  ext (i | i) (j | j) <;> simp

lemma realBlockStep_smul (m k : ℕ) (c : ℝ) (A : RealBlockStage m k) :
    realBlockStep m k (c • A) = c • realBlockStep m k A := by
  change Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k)
      (Matrix.fromBlocks (c • A) 0 0 (c • A)) =
    c • Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k) (Matrix.fromBlocks A 0 0 A)
  rw [← map_smul]
  congr 1
  ext (i | i) (j | j) <;> simp

lemma realBlockStep_mul (m k : ℕ) (A B : RealBlockStage m k) :
    realBlockStep m k (A * B) = realBlockStep m k A * realBlockStep m k B := by
  change Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k)
      (Matrix.fromBlocks (A * B) 0 0 (A * B)) =
    Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k) (Matrix.fromBlocks A 0 0 A) *
    Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k) (Matrix.fromBlocks B 0 0 B)
  rw [← map_mul]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

lemma realBlockStep_transpose (m k : ℕ) (A : RealBlockStage m k) :
    realBlockStep m k Aᵀ = (realBlockStep m k A)ᵀ := by
  change Matrix.reindex (finSumBlock m k) (finSumBlock m k)
      (Matrix.fromBlocks Aᵀ 0 0 Aᵀ) =
    (Matrix.reindex (finSumBlock m k) (finSumBlock m k) (Matrix.fromBlocks A 0 0 A))ᵀ
  rw [Matrix.transpose_reindex]
  congr 1
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero]

lemma realBlockStep_star (m k : ℕ) (A : RealBlockStage m k) :
    realBlockStep m k (star A) = star (realBlockStep m k A) := by
  have hst : ∀ {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ), star M = Mᵀ := by
    intro p M
    ext i j
    simp [Matrix.star_apply]
  rw [hst, hst, realBlockStep_transpose]

lemma realBlockStep_injective (m k : ℕ) :
    Function.Injective (realBlockStep m k) := by
  intro A B h
  dsimp [realBlockStep] at h
  have hfb : Matrix.fromBlocks A 0 0 A = Matrix.fromBlocks B 0 0 B :=
    (Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k)).injective h
  ext i j
  have hij := congr_fun (congr_fun hfb (Sum.inl i)) (Sum.inl j)
  simpa only [Matrix.fromBlocks_apply₁₁] using hij

/-- Exact trace doubling under `realBlockStep`. -/
theorem trace_realBlockStep (m k : ℕ) (A : RealBlockStage m k) :
    Matrix.trace (realBlockStep m k A) = 2 * Matrix.trace A := by
  unfold realBlockStep Matrix.trace Matrix.diag
  rw [← Equiv.sum_comp (finSumBlock m k)]
  have hsum : (∑ s : Fin (blockDim m k) ⊕ Fin (blockDim m k),
      (Matrix.reindexAlgEquiv ℝ ℝ (finSumBlock m k) (Matrix.fromBlocks A 0 0 A))
        (finSumBlock m k s) (finSumBlock m k s)) =
      ∑ s : Fin (blockDim m k) ⊕ Fin (blockDim m k), Matrix.fromBlocks A 0 0 A s s := by
    apply Finset.sum_congr rfl
    intro s _
    change (Matrix.reindex (finSumBlock m k) (finSumBlock m k) (Matrix.fromBlocks A 0 0 A))
      (finSumBlock m k s) (finSumBlock m k s) = Matrix.fromBlocks A 0 0 A s s
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [hsum, Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  ring

/-- Hilbert–Schmidt inner product doubles under `realBlockStep`. -/
theorem hsInner_realBlockStep (m k : ℕ) (A B : RealBlockStage m k) :
    hsInner (realBlockStep m k A) (realBlockStep m k B) = 2 * hsInner A B := by
  unfold hsInner
  rw [← realBlockStep_transpose, ← realBlockStep_mul, trace_realBlockStep]

/-- Stage-normalized Hilbert–Schmidt inner product `2⁻ᵏ ⟨A, B⟩_HS`. -/
def normHSInner (m k : ℕ) (A B : RealBlockStage m k) : ℝ :=
  (1 / (2 ^ k : ℝ)) * hsInner A B

/-- `realBlockStep` is an exact isometry for `normHSInner`. -/
theorem normHSInner_realBlockStep (m k : ℕ) (A B : RealBlockStage m k) :
    normHSInner m (k + 1) (realBlockStep m k A) (realBlockStep m k B) =
      normHSInner m k A B := by
  unfold normHSInner
  rw [hsInner_realBlockStep]
  have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  rw [pow_succ']
  field_simp [hpow, htwo]

/-- Iterated block-doubling transition `RealBlockStage m k → RealBlockStage m (k + d)`. -/
def realBlockIter {m : ℕ} : ∀ {k : ℕ} (d : ℕ), RealBlockStage m k → RealBlockStage m (k + d)
  | _, 0, X => X
  | _, d + 1, X => realBlockStep m _ (realBlockIter d X)

lemma realBlockIter_zero {m k : ℕ} (d : ℕ) :
    realBlockIter d (0 : RealBlockStage m k) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      dsimp [realBlockIter]
      rw [ih, realBlockStep_zero]

lemma realBlockIter_one {m k : ℕ} (d : ℕ) :
    realBlockIter d (1 : RealBlockStage m k) = 1 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      dsimp [realBlockIter]
      rw [ih, realBlockStep_one]

lemma realBlockIter_add {m k : ℕ} (d : ℕ) (X Y : RealBlockStage m k) :
    realBlockIter d (X + Y) = realBlockIter d X + realBlockIter d Y := by
  induction d with
  | zero => rfl
  | succ d ih =>
      dsimp [realBlockIter]
      rw [ih, realBlockStep_add]

lemma realBlockIter_neg {m k : ℕ} (d : ℕ) (X : RealBlockStage m k) :
    realBlockIter d (-X) = -realBlockIter d X := by
  induction d with
  | zero => rfl
  | succ d ih =>
      dsimp [realBlockIter]
      rw [ih, realBlockStep_neg]

lemma realBlockIter_smul {m k : ℕ} (d : ℕ) (c : ℝ) (X : RealBlockStage m k) :
    realBlockIter d (c • X) = c • realBlockIter d X := by
  induction d with
  | zero => rfl
  | succ d ih =>
      dsimp [realBlockIter]
      rw [ih, realBlockStep_smul]

lemma realBlockIter_mul {m k : ℕ} (d : ℕ) (X Y : RealBlockStage m k) :
    realBlockIter d (X * Y) = realBlockIter d X * realBlockIter d Y := by
  induction d with
  | zero => rfl
  | succ d ih =>
      dsimp [realBlockIter]
      rw [ih, realBlockStep_mul]

lemma realBlockIter_transpose {m k : ℕ} (d : ℕ) (X : RealBlockStage m k) :
    realBlockIter d Xᵀ = (realBlockIter d X)ᵀ := by
  induction d with
  | zero => rfl
  | succ d ih =>
      dsimp [realBlockIter]
      rw [ih, realBlockStep_transpose]

lemma realBlockIter_star {m k : ℕ} (d : ℕ) (X : RealBlockStage m k) :
    realBlockIter d (star X) = star (realBlockIter d X) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      dsimp [realBlockIter]
      rw [ih, realBlockStep_star]

lemma realBlockIter_injective {m k : ℕ} (d : ℕ) :
    Function.Injective (realBlockIter (m := m) (k := k) d) := by
  induction d with
  | zero => exact fun _ _ h => h
  | succ d ih =>
      intro X Y h
      exact ih (realBlockStep_injective m _ h)

theorem normHSInner_realBlockIter {m k : ℕ} (d : ℕ) (X Y : RealBlockStage m k) :
    normHSInner m (k + d) (realBlockIter d X) (realBlockIter d Y) = normHSInner m k X Y := by
  induction d with
  | zero => rfl
  | succ d ih =>
      dsimp [realBlockIter]
      change normHSInner m ((k + d) + 1)
        (realBlockStep m (k + d) (realBlockIter d X))
        (realBlockStep m (k + d) (realBlockIter d Y)) = normHSInner m k X Y
      rw [normHSInner_realBlockStep, ih]

/-!
## 2. Jaynesian Inductive Colimit Ring `RealBlockColimit m` & `ColimitKMS` Instantiation
-/

/-- Equal-stage cast for `RealBlockStage m`. -/
def castBlock {m k₁ k₂ : ℕ} (h : k₁ = k₂) (X : RealBlockStage m k₁) : RealBlockStage m k₂ :=
  h ▸ X

lemma castBlock_heq {m k₁ k₂ : ℕ} (h : k₁ = k₂) (X : RealBlockStage m k₁) :
    HEq (castBlock h X) X := by
  subst h
  rfl

lemma castBlock_add {m k₁ k₂ : ℕ} (h : k₁ = k₂) (X Y : RealBlockStage m k₁) :
    castBlock h (X + Y) = castBlock h X + castBlock h Y := by
  subst h; rfl

lemma castBlock_mul {m k₁ k₂ : ℕ} (h : k₁ = k₂) (X Y : RealBlockStage m k₁) :
    castBlock h (X * Y) = castBlock h X * castBlock h Y := by
  subst h; rfl

lemma castBlock_smul {m k₁ k₂ : ℕ} (h : k₁ = k₂) (c : ℝ) (X : RealBlockStage m k₁) :
    castBlock h (c • X) = c • castBlock h X := by
  subst h; rfl

lemma realBlockIter_castBlock {m k₁ k₂ : ℕ} (h : k₁ = k₂) (d : ℕ) (X : RealBlockStage m k₁) :
    realBlockIter d (castBlock h X) =
      castBlock (congrArg (· + d) h) (realBlockIter d X) := by
  subst h; rfl

lemma eq_of_heq_block {m k₁ k₂ : ℕ} (h : k₁ = k₂)
    {X : RealBlockStage m k₁} {Y : RealBlockStage m k₂}
    (heq : HEq X Y) : castBlock h X = Y := by
  subst h
  exact eq_of_heq heq

lemma realBlockStep_congr_heq {m k₁ k₂ : ℕ} {X : RealBlockStage m k₁} {Y : RealBlockStage m k₂}
    (h_dim : k₁ = k₂) (h_heq : HEq X Y) :
    HEq (realBlockStep m k₁ X) (realBlockStep m k₂ Y) := by
  subst h_dim
  cases eq_of_heq h_heq
  exact HEq.rfl

lemma realBlockIter_congr_heq {m k₁ k₂ : ℕ} (d : ℕ)
    {X : RealBlockStage m k₁} {Y : RealBlockStage m k₂}
    (h_dim : k₁ = k₂) (h_heq : HEq X Y) :
    HEq (realBlockIter d X) (realBlockIter d Y) := by
  induction d with
  | zero => exact h_heq
  | succ d ih => exact realBlockStep_congr_heq (by simp [h_dim]) ih

lemma realBlockIter_add_heq {m k : ℕ} (a b : ℕ) (X : RealBlockStage m k) :
    HEq (realBlockIter (a + b) X) (realBlockIter b (realBlockIter a X)) := by
  induction b with
  | zero => exact HEq.rfl
  | succ b ih => exact realBlockStep_congr_heq (by simp [Nat.add_assoc]) ih

lemma realBlockIter_comm_heq {m k : ℕ} (a b : ℕ) (X : RealBlockStage m k) :
    HEq (realBlockIter (a + b) X) (realBlockIter (b + a) X) := by
  have h : a + b = b + a := Nat.add_comm a b
  rw [h]

private lemma realBlockIter_split_heq {m k a b c : ℕ} (X : RealBlockStage m k)
    (h : a + b = c) :
    HEq (realBlockIter b (realBlockIter a X)) (realBlockIter c X) := by
  refine HEq.trans (realBlockIter_add_heq a b X).symm ?_
  subst h
  rfl

private lemma realBlockIter_congr_heq_dim {m k₁ k₂ : ℕ} (d₁ d₂ : ℕ)
    {X : RealBlockStage m k₁} {Y : RealBlockStage m k₂}
    (h_dim : k₁ = k₂) (hd : d₁ = d₂) (h_heq : HEq X Y) :
    HEq (realBlockIter d₁ X) (realBlockIter d₂ Y) := by
  subst hd
  exact realBlockIter_congr_heq d₁ h_dim h_heq

private lemma heq_zero_block {m k₁ k₂ : ℕ} (h : k₁ = k₂) :
    HEq (0 : RealBlockStage m k₁) (0 : RealBlockStage m k₂) := by
  subst h; rfl

private lemma heq_one_block {m k₁ k₂ : ℕ} (h : k₁ = k₂) :
    HEq (1 : RealBlockStage m k₁) (1 : RealBlockStage m k₂) := by
  subst h; rfl

private lemma heq_neg_block {m k₁ k₂ : ℕ} (h : k₁ = k₂)
    {X : RealBlockStage m k₁} {Y : RealBlockStage m k₂} (heq : HEq X Y) :
    HEq (-X) (-Y) := by
  subst h; cases eq_of_heq heq; rfl

private lemma heq_smul_block {m k₁ k₂ : ℕ} (h : k₁ = k₂) (c : ℝ)
    {X : RealBlockStage m k₁} {Y : RealBlockStage m k₂} (heq : HEq X Y) :
    HEq (c • X) (c • Y) := by
  subst h; cases eq_of_heq heq; rfl

private lemma heq_star_block {m k₁ k₂ : ℕ} (h : k₁ = k₂)
    {X : RealBlockStage m k₁} {Y : RealBlockStage m k₂} (heq : HEq X Y) :
    HEq (star X) (star Y) := by
  subst h; cases eq_of_heq heq; rfl

/-- Directed colimit equivalence relation on `Σ k : ℕ, RealBlockStage m k`. -/
def RealBlockRel (m : ℕ) (u v : Σ k : ℕ, RealBlockStage m k) : Prop :=
  ∃ (d₁ d₂ : ℕ), u.1 + d₁ = v.1 + d₂ ∧
    HEq (realBlockIter d₁ u.2) (realBlockIter d₂ v.2)

theorem realBlockRel_trans {m : ℕ} {u v w : Σ k : ℕ, RealBlockStage m k}
    (huv : RealBlockRel m u v) (hvw : RealBlockRel m v w) : RealBlockRel m u w := by
  rcases huv with ⟨d₁, d₂, h12, heq12⟩
  rcases hvw with ⟨e₁, e₂, h23, heq23⟩
  refine ⟨d₁ + e₁, e₂ + d₂, by omega, ?_⟩
  exact (realBlockIter_add_heq d₁ e₁ u.2).trans <|
    (realBlockIter_congr_heq e₁ h12 heq12).trans <|
    (realBlockIter_add_heq d₂ e₁ v.2).symm.trans <|
    (realBlockIter_comm_heq d₂ e₁ v.2).trans <|
    (realBlockIter_add_heq e₁ d₂ v.2).trans <|
    (realBlockIter_congr_heq d₂ h23 heq23).trans <|
    (realBlockIter_add_heq e₂ d₂ w.2).symm

/-- Certified `Setoid` for the Jaynesian real matrix inductive colimit. -/
instance realBlockSetoid (m : ℕ) : Setoid (Σ k : ℕ, RealBlockStage m k) where
  r := RealBlockRel m
  iseqv := {
    refl := fun _ => ⟨0, 0, rfl, HEq.rfl⟩
    symm := fun ⟨d₁, d₂, h, heq⟩ => ⟨d₂, d₁, h.symm, heq.symm⟩
    trans := realBlockRel_trans
  }

/-- Jaynesian inductive colimit carrier over the block-doubling tower `RealBlockStage m`. -/
abbrev RealBlockColimit (m : ℕ) : Type :=
  Quotient (realBlockSetoid m)

/-- Canonical inductive colimit injection `RealBlockStage m k → RealBlockColimit m`. -/
def toBlockColimit {m : ℕ} (k : ℕ) (X : RealBlockStage m k) : RealBlockColimit m :=
  Quotient.mk (realBlockSetoid m) ⟨k, X⟩

lemma toBlockColimit_castBlock {m k₁ k₂ : ℕ} (h : k₁ = k₂) (X : RealBlockStage m k₁) :
    toBlockColimit k₂ (castBlock h X) = toBlockColimit k₁ X := by
  subst h; rfl

lemma toBlockColimit_iter {m k : ℕ} (d : ℕ) (X : RealBlockStage m k) :
    toBlockColimit (k + d) (realBlockIter d X) = toBlockColimit k X := by
  apply Quotient.sound
  exact ⟨0, d, rfl, HEq.rfl⟩

lemma toBlockColimit_step {m k : ℕ} (X : RealBlockStage m k) :
    toBlockColimit (k + 1) (realBlockStep m k X) = toBlockColimit k X :=
  toBlockColimit_iter 1 X

lemma exists_toBlockColimit {m : ℕ} (x : RealBlockColimit m) :
    ∃ (k : ℕ) (X : RealBlockStage m k), x = toBlockColimit k X := by
  rcases Quotient.exists_rep x with ⟨⟨k, X⟩, rfl⟩
  exact ⟨k, X, rfl⟩

theorem toBlockColimit_injective {m : ℕ} (k : ℕ) :
    Function.Injective (toBlockColimit (m := m) k) := by
  intro X Y h
  rcases Quotient.exact h with ⟨d₁, d₂, hdim, heq⟩
  dsimp at hdim
  have hd : d₁ = d₂ := by omega
  subst hd
  exact realBlockIter_injective d₁ (eq_of_heq heq)

private lemma toBlockColimit_binop_stabilize {m : ℕ}
    (op : ∀ k : ℕ, RealBlockStage m k → RealBlockStage m k → RealBlockStage m k)
    (h_emb : ∀ (k d : ℕ) (X Y : RealBlockStage m k),
      realBlockIter d (op k X Y) = op (k + d) (realBlockIter d X) (realBlockIter d Y))
    (h_cast : ∀ {k₁ k₂ : ℕ} (h : k₁ = k₂) (X Y : RealBlockStage m k₁),
      castBlock h (op k₁ X Y) = op k₂ (castBlock h X) (castBlock h Y))
    (u v : Σ k : ℕ, RealBlockStage m k) {M N : ℕ}
    (huM : u.1 ≤ M) (hvM : v.1 ≤ M) (hMN : M ≤ N) :
    toBlockColimit M
      (op M (castBlock (Nat.add_sub_cancel' huM) (realBlockIter (M - u.1) u.2))
            (castBlock (Nat.add_sub_cancel' hvM) (realBlockIter (M - v.1) v.2))) =
    toBlockColimit N
      (op N (castBlock (Nat.add_sub_cancel' (le_trans huM hMN)) (realBlockIter (N - u.1) u.2))
            (castBlock (Nat.add_sub_cancel' (le_trans hvM hMN)) (realBlockIter (N - v.1) v.2))) := by
  rw [← toBlockColimit_iter (N - M), h_emb]
  have h_dim : M + (N - M) = N := Nat.add_sub_cancel' hMN
  rw [← toBlockColimit_castBlock h_dim, h_cast h_dim]
  congr 2
  · apply eq_of_heq_block rfl
    refine HEq.trans (castBlock_heq _ _) ?_
    rw [realBlockIter_castBlock]
    refine HEq.trans (castBlock_heq _ _) ?_
    refine HEq.trans (realBlockIter_split_heq u.2 (by omega)) (castBlock_heq _ _).symm
  · apply eq_of_heq_block rfl
    refine HEq.trans (castBlock_heq _ _) ?_
    rw [realBlockIter_castBlock]
    refine HEq.trans (castBlock_heq _ _) ?_
    refine HEq.trans (realBlockIter_split_heq v.2 (by omega)) (castBlock_heq _ _).symm

private lemma lift_block_binop_wd {m : ℕ}
    (op : ∀ k : ℕ, RealBlockStage m k → RealBlockStage m k → RealBlockStage m k)
    (h_emb : ∀ (k d : ℕ) (X Y : RealBlockStage m k),
      realBlockIter d (op k X Y) = op (k + d) (realBlockIter d X) (realBlockIter d Y))
    (h_cast : ∀ {k₁ k₂ : ℕ} (h : k₁ = k₂) (X Y : RealBlockStage m k₁),
      castBlock h (op k₁ X Y) = op k₂ (castBlock h X) (castBlock h Y))
    {u₁ u₂ v₁ v₂ : Σ k : ℕ, RealBlockStage m k}
    (hu : RealBlockRel m u₁ u₂) (hv : RealBlockRel m v₁ v₂) :
    toBlockColimit (max u₁.1 v₁.1)
      (op (max u₁.1 v₁.1)
        (castBlock (Nat.add_sub_cancel' (le_max_left u₁.1 v₁.1))
          (realBlockIter (max u₁.1 v₁.1 - u₁.1) u₁.2))
        (castBlock (Nat.add_sub_cancel' (le_max_right u₁.1 v₁.1))
          (realBlockIter (max u₁.1 v₁.1 - v₁.1) v₁.2))) =
    toBlockColimit (max u₂.1 v₂.1)
      (op (max u₂.1 v₂.1)
        (castBlock (Nat.add_sub_cancel' (le_max_left u₂.1 v₂.1))
          (realBlockIter (max u₂.1 v₂.1 - u₂.1) u₂.2))
        (castBlock (Nat.add_sub_cancel' (le_max_right u₂.1 v₂.1))
          (realBlockIter (max u₂.1 v₂.1 - v₂.1) v₂.2))) := by
  rcases hu with ⟨d₁, d₂, h_u, heq_u⟩
  rcases hv with ⟨e₁, e₂, h_v, heq_v⟩
  set M₁ := max u₁.1 v₁.1
  set M₂ := max u₂.1 v₂.1
  set M := max (u₁.1 + d₁) (v₁.1 + e₁)
  set N := M₁ + M₂ + M
  have hN₁ : M₁ ≤ N := le_trans (Nat.le_add_right M₁ M₂) (Nat.le_add_right _ M)
  have hN₂ : M₂ ≤ N := le_trans (Nat.le_add_left M₂ M₁) (Nat.le_add_right _ M)
  rw [toBlockColimit_binop_stabilize op h_emb h_cast u₁ v₁ (le_max_left _ _) (le_max_right _ _) hN₁]
  rw [toBlockColimit_binop_stabilize op h_emb h_cast u₂ v₂ (le_max_left _ _) (le_max_right _ _) hN₂]
  have hu_eq :
      castBlock (Nat.add_sub_cancel' (le_trans (le_max_left u₁.1 v₁.1) hN₁))
        (realBlockIter (N - u₁.1) u₁.2) =
      castBlock (Nat.add_sub_cancel' (le_trans (le_max_left u₂.1 v₂.1) hN₂))
        (realBlockIter (N - u₂.1) u₂.2) := by
    apply eq_of_heq_block rfl
    refine HEq.trans (castBlock_heq _ _) ?_
    refine HEq.trans ?_ (castBlock_heq _ _).symm
    have heq_step :
        HEq (realBlockIter (N - (u₁.1 + d₁)) (realBlockIter d₁ u₁.2))
            (realBlockIter (N - (u₂.1 + d₂)) (realBlockIter d₂ u₂.2)) :=
      realBlockIter_congr_heq_dim (N - (u₁.1 + d₁)) (N - (u₂.1 + d₂)) h_u (by omega) heq_u
    exact (realBlockIter_split_heq u₁.2 (by omega : d₁ + (N - (u₁.1 + d₁)) = N - u₁.1)).symm.trans
      (heq_step.trans (realBlockIter_split_heq u₂.2 (by omega : d₂ + (N - (u₂.1 + d₂)) = N - u₂.1)))
  have hv_eq :
      castBlock (Nat.add_sub_cancel' (le_trans (le_max_right u₁.1 v₁.1) hN₁))
        (realBlockIter (N - v₁.1) v₁.2) =
      castBlock (Nat.add_sub_cancel' (le_trans (le_max_right u₂.1 v₂.1) hN₂))
        (realBlockIter (N - v₂.1) v₂.2) := by
    apply eq_of_heq_block rfl
    refine HEq.trans (castBlock_heq _ _) ?_
    refine HEq.trans ?_ (castBlock_heq _ _).symm
    have heq_step :
        HEq (realBlockIter (N - (v₁.1 + e₁)) (realBlockIter e₁ v₁.2))
            (realBlockIter (N - (v₂.1 + e₂)) (realBlockIter e₂ v₂.2)) :=
      realBlockIter_congr_heq_dim (N - (v₁.1 + e₁)) (N - (v₂.1 + e₂)) h_v (by omega) heq_v
    exact (realBlockIter_split_heq v₁.2 (by omega : e₁ + (N - (v₁.1 + e₁)) = N - v₁.1)).symm.trans
      (heq_step.trans (realBlockIter_split_heq v₂.2 (by omega : e₂ + (N - (v₂.1 + e₂)) = N - v₂.1)))
  rw [hu_eq, hv_eq]

private def addBlock {m : ℕ} (x y : RealBlockColimit m) : RealBlockColimit m :=
  Quotient.liftOn₂ x y
    (fun u v =>
      let M := max u.1 v.1
      toBlockColimit M
        (castBlock (Nat.add_sub_cancel' (le_max_left u.1 v.1))
          (realBlockIter (M - u.1) u.2) +
         castBlock (Nat.add_sub_cancel' (le_max_right u.1 v.1))
          (realBlockIter (M - v.1) v.2)))
    (fun _ _ _ _ hu hv =>
      lift_block_binop_wd (fun _ X Y => X + Y)
        (fun _ _ _ _ => realBlockIter_add _ _ _)
        (fun h _ _ => castBlock_add h _ _) hu hv)

private def mulBlock {m : ℕ} (x y : RealBlockColimit m) : RealBlockColimit m :=
  Quotient.liftOn₂ x y
    (fun u v =>
      let M := max u.1 v.1
      toBlockColimit M
        (castBlock (Nat.add_sub_cancel' (le_max_left u.1 v.1))
          (realBlockIter (M - u.1) u.2) *
         castBlock (Nat.add_sub_cancel' (le_max_right u.1 v.1))
          (realBlockIter (M - v.1) v.2)))
    (fun _ _ _ _ hu hv =>
      lift_block_binop_wd (fun _ X Y => X * Y)
        (fun _ _ _ _ => realBlockIter_mul _ _ _)
        (fun h _ _ => castBlock_mul h _ _) hu hv)

private def negBlock {m : ℕ} (x : RealBlockColimit m) : RealBlockColimit m :=
  Quotient.liftOn x
    (fun u => toBlockColimit u.1 (-u.2))
    (fun _ _ ⟨d₁, d₂, h_dim, heq_u⟩ => by
      apply Quotient.sound
      refine ⟨d₁, d₂, h_dim, ?_⟩
      rw [realBlockIter_neg, realBlockIter_neg]
      exact heq_neg_block h_dim heq_u)

private def smulBlock {m : ℕ} (c : ℝ) (x : RealBlockColimit m) : RealBlockColimit m :=
  Quotient.liftOn x
    (fun u => toBlockColimit u.1 (c • u.2))
    (fun _ _ ⟨d₁, d₂, h_dim, heq_u⟩ => by
      apply Quotient.sound
      refine ⟨d₁, d₂, h_dim, ?_⟩
      rw [realBlockIter_smul, realBlockIter_smul]
      exact heq_smul_block h_dim c heq_u)

private def starBlock {m : ℕ} (x : RealBlockColimit m) : RealBlockColimit m :=
  Quotient.liftOn x
    (fun u => toBlockColimit u.1 (star u.2))
    (fun _ _ ⟨d₁, d₂, h_dim, heq_u⟩ => by
      apply Quotient.sound
      refine ⟨d₁, d₂, h_dim, ?_⟩
      rw [realBlockIter_star, realBlockIter_star]
      exact heq_star_block h_dim heq_u)

instance instAddRealBlockColimit (m : ℕ) : Add (RealBlockColimit m) := ⟨addBlock⟩
instance instMulRealBlockColimit (m : ℕ) : Mul (RealBlockColimit m) := ⟨mulBlock⟩
instance instNegRealBlockColimit (m : ℕ) : Neg (RealBlockColimit m) := ⟨negBlock⟩
instance instSMulRealBlockColimit (m : ℕ) : SMul ℝ (RealBlockColimit m) := ⟨smulBlock⟩
instance instStarRealBlockColimit (m : ℕ) : Star (RealBlockColimit m) := ⟨starBlock⟩
instance instZeroRealBlockColimit (m : ℕ) : Zero (RealBlockColimit m) := ⟨toBlockColimit 0 0⟩
instance instOneRealBlockColimit (m : ℕ) : One (RealBlockColimit m) := ⟨toBlockColimit 0 1⟩

lemma toBlockColimit_zero {m : ℕ} (k : ℕ) :
    toBlockColimit k (0 : RealBlockStage m k) = (0 : RealBlockColimit m) := by
  change toBlockColimit k 0 = toBlockColimit 0 0
  apply Quotient.sound
  refine ⟨0, k, (Nat.zero_add k).symm, ?_⟩
  have hiter : realBlockIter k (0 : RealBlockStage m 0) = 0 := realBlockIter_zero k
  change HEq (0 : RealBlockStage m k) (realBlockIter k (0 : RealBlockStage m 0))
  rw [hiter]
  exact heq_zero_block (Nat.zero_add k).symm

lemma toBlockColimit_one {m : ℕ} (k : ℕ) :
    toBlockColimit k (1 : RealBlockStage m k) = (1 : RealBlockColimit m) := by
  change toBlockColimit k 1 = toBlockColimit 0 1
  apply Quotient.sound
  refine ⟨0, k, (Nat.zero_add k).symm, ?_⟩
  have hiter : realBlockIter k (1 : RealBlockStage m 0) = 1 := realBlockIter_one k
  change HEq (1 : RealBlockStage m k) (realBlockIter k (1 : RealBlockStage m 0))
  rw [hiter]
  exact heq_one_block (Nat.zero_add k).symm

private lemma castBlock_realBlockIter_max {m k : ℕ} (h : k + (max k k - k) = max k k)
    (X : RealBlockStage m k) :
    castBlock h (realBlockIter (max k k - k) X) = castBlock (max_self k).symm X := by
  apply eq_of_heq_block rfl
  refine HEq.trans (castBlock_heq _ _) ?_
  refine HEq.trans ?_ (castBlock_heq _ _).symm
  have hz : max k k - k = 0 := by omega
  rw [hz]
  rfl

@[simp]
lemma add_toBlockColimit {m : ℕ} (k : ℕ) (X Y : RealBlockStage m k) :
    toBlockColimit k X + toBlockColimit k Y = toBlockColimit k (X + Y) := by
  change addBlock (toBlockColimit k X) (toBlockColimit k Y) = toBlockColimit k (X + Y)
  simp only [addBlock, toBlockColimit, Quotient.liftOn₂_mk]
  rw [castBlock_realBlockIter_max (Nat.add_sub_cancel' (le_max_left k k)),
      castBlock_realBlockIter_max (Nat.add_sub_cancel' (le_max_right k k)),
      ← castBlock_add]
  exact toBlockColimit_castBlock _ _

@[simp]
lemma mul_toBlockColimit {m : ℕ} (k : ℕ) (X Y : RealBlockStage m k) :
    toBlockColimit k X * toBlockColimit k Y = toBlockColimit k (X * Y) := by
  change mulBlock (toBlockColimit k X) (toBlockColimit k Y) = toBlockColimit k (X * Y)
  simp only [mulBlock, toBlockColimit, Quotient.liftOn₂_mk]
  rw [castBlock_realBlockIter_max (Nat.add_sub_cancel' (le_max_left k k)),
      castBlock_realBlockIter_max (Nat.add_sub_cancel' (le_max_right k k)),
      ← castBlock_mul]
  exact toBlockColimit_castBlock _ _

@[simp]
lemma neg_toBlockColimit {m : ℕ} (k : ℕ) (X : RealBlockStage m k) :
    -(toBlockColimit k X) = toBlockColimit k (-X) := rfl

@[simp]
lemma smul_toBlockColimit {m : ℕ} (k : ℕ) (c : ℝ) (X : RealBlockStage m k) :
    c • toBlockColimit k X = toBlockColimit k (c • X) := rfl

@[simp]
lemma star_toBlockColimit {m : ℕ} (k : ℕ) (X : RealBlockStage m k) :
    star (toBlockColimit k X) = toBlockColimit k (star X) := rfl

lemma star_toBlockColimit_transpose {m : ℕ} (k : ℕ) (X : RealBlockStage m k) :
    star (toBlockColimit k X) = toBlockColimit k Xᵀ := by
  rw [star_toBlockColimit]
  rfl

lemma toBlockColimit_lift_three {m : ℕ} (x y z : RealBlockColimit m) :
    ∃ (k : ℕ) (X Y Z : RealBlockStage m k),
      x = toBlockColimit k X ∧ y = toBlockColimit k Y ∧ z = toBlockColimit k Z := by
  rcases Quotient.exists_rep x with ⟨⟨k₁, X₁⟩, rfl⟩
  rcases Quotient.exists_rep y with ⟨⟨k₂, X₂⟩, rfl⟩
  rcases Quotient.exists_rep z with ⟨⟨k₃, X₃⟩, rfl⟩
  set N := max k₁ (max k₂ k₃)
  refine ⟨N,
    castBlock (by omega : k₁ + (N - k₁) = N) (realBlockIter (N - k₁) X₁),
    castBlock (by omega : k₂ + (N - k₂) = N) (realBlockIter (N - k₂) X₂),
    castBlock (by omega : k₃ + (N - k₃) = N) (realBlockIter (N - k₃) X₃),
    ?_, ?_, ?_⟩ <;>
  · rw [toBlockColimit_castBlock, toBlockColimit_iter]
    rfl

lemma toBlockColimit_lift_two {m : ℕ} (x y : RealBlockColimit m) :
    ∃ (k : ℕ) (X Y : RealBlockStage m k),
      x = toBlockColimit k X ∧ y = toBlockColimit k Y := by
  rcases toBlockColimit_lift_three x y 0 with ⟨k, X, Y, _, hx, hy, _⟩
  exact ⟨k, X, Y, hx, hy⟩

/-- Genuine unital `Ring` structure on `RealBlockColimit m`. -/
instance instRingRealBlockColimit (m : ℕ) : Ring (RealBlockColimit m) where
  add_assoc x y z := by
    rcases toBlockColimit_lift_three x y z with ⟨k, X, Y, Z, rfl, rfl, rfl⟩
    simp [add_assoc]
  zero_add x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    rw [← toBlockColimit_zero k, add_toBlockColimit, zero_add]
  add_zero x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    rw [← toBlockColimit_zero k, add_toBlockColimit, add_zero]
  neg_add_cancel x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    rw [neg_toBlockColimit, add_toBlockColimit, neg_add_cancel, toBlockColimit_zero]
  add_comm x y := by
    rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
    simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc x y z := by
    rcases toBlockColimit_lift_three x y z with ⟨k, X, Y, Z, rfl, rfl, rfl⟩
    simp [mul_assoc]
  zero_mul x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    rw [← toBlockColimit_zero k, mul_toBlockColimit, zero_mul, toBlockColimit_zero]
  mul_zero x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    rw [← toBlockColimit_zero k, mul_toBlockColimit, mul_zero, toBlockColimit_zero]
  one_mul x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    rw [← toBlockColimit_one k, mul_toBlockColimit, one_mul]
  mul_one x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    rw [← toBlockColimit_one k, mul_toBlockColimit, mul_one]
  left_distrib x y z := by
    rcases toBlockColimit_lift_three x y z with ⟨k, X, Y, Z, rfl, rfl, rfl⟩
    simp [left_distrib]
  right_distrib x y z := by
    rcases toBlockColimit_lift_three x y z with ⟨k, X, Y, Z, rfl, rfl, rfl⟩
    simp [right_distrib]

/-- Genuine real `Module ℝ` structure on `RealBlockColimit m`. -/
instance instModuleRealBlockColimit (m : ℕ) : Module ℝ (RealBlockColimit m) where
  one_smul x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    rw [smul_toBlockColimit, one_smul]
  mul_smul a b x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    simp only [smul_toBlockColimit, mul_smul]
  smul_zero a := by
    change a • toBlockColimit 0 (0 : RealBlockStage m 0) = toBlockColimit 0 0
    rw [smul_toBlockColimit, smul_zero]
  smul_add a x y := by
    rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
    simp only [add_toBlockColimit, smul_toBlockColimit, smul_add]
  add_smul a b x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    simp only [smul_toBlockColimit, add_toBlockColimit, add_smul]
  zero_smul x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    rw [smul_toBlockColimit, zero_smul, toBlockColimit_zero]

/-- Genuine `StarRing` structure on `RealBlockColimit m`. -/
instance instStarRingRealBlockColimit (m : ℕ) : StarRing (RealBlockColimit m) where
  star_involutive x := by
    rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
    rw [star_toBlockColimit, star_toBlockColimit, star_star]
  star_mul x y := by
    rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
    rw [mul_toBlockColimit, star_toBlockColimit, star_toBlockColimit, star_toBlockColimit,
      star_mul, mul_toBlockColimit]
  star_add x y := by
    rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
    rw [add_toBlockColimit, star_toBlockColimit, star_toBlockColimit, star_toBlockColimit,
      star_add, add_toBlockColimit]

/-- Transition linear map `RealBlockStage m i →ₗ[ℝ] RealBlockStage m j` for `i ≤ j`. -/
def realBlockTrans (m : ℕ) {i j : ℕ} (hij : i ≤ j) :
    RealBlockStage m i →ₗ[ℝ] RealBlockStage m j where
  toFun X := castBlock (Nat.add_sub_cancel' hij) (realBlockIter (j - i) X)
  map_add' X Y := by rw [realBlockIter_add, castBlock_add]
  map_smul' c X := by rw [realBlockIter_smul, castBlock_smul, RingHom.id_apply]

/-- Instantiation of `InfoGeometry.NCG.ColimitKMS.InductiveSystem` on `RealBlockStage m`. -/
def realBlockInductiveSystem (m : ℕ) :
    InductiveSystem (R := ℝ) (RealBlockStage m) where
  trans {i j} hij := realBlockTrans m hij
  trans_id i := by
    ext1 X
    dsimp [realBlockTrans]
    apply eq_of_heq_block rfl
    refine HEq.trans (castBlock_heq _ _) ?_
    have hz : i - i = 0 := Nat.sub_self i
    rw [hz]
    rfl
  trans_comp {i j k} hij hjk := by
    ext1 X
    dsimp [realBlockTrans]
    apply eq_of_heq_block rfl
    refine HEq.trans (castBlock_heq _ _) ?_
    refine HEq.trans ?_ (castBlock_heq _ _).symm
    rw [realBlockIter_castBlock]
    refine HEq.trans (castBlock_heq _ _) ?_
    exact realBlockIter_split_heq X (by omega : (j - i) + (k - j) = k - i)

/-- Instantiation of `InfoGeometry.NCG.ColimitKMS.StarAlgebraCocone` into `RealBlockColimit m`. -/
def realBlockStarAlgebraCocone (m : ℕ) :
    StarAlgebraCocone (realBlockInductiveSystem m) (RealBlockColimit m) where
  leg k :=
    { toFun := toBlockColimit k
      map_add' := fun X Y => (add_toBlockColimit k X Y).symm
      map_smul' := fun c X => (smul_toBlockColimit k c X).symm }
  compatible {i j} hij := by
    ext1 X
    change toBlockColimit j (castBlock (Nat.add_sub_cancel' hij) (realBlockIter (j - i) X)) =
      toBlockColimit i X
    rw [toBlockColimit_castBlock, toBlockColimit_iter]
  map_mul k X Y := (mul_toBlockColimit k X Y).symm
  map_star k X := (star_toBlockColimit k X).symm

private lemma normHSInner_castBlock {m k₁ k₂ : ℕ} (h : k₁ = k₂)
    (X Y : RealBlockStage m k₁) :
    normHSInner m k₂ (castBlock h X) (castBlock h Y) = normHSInner m k₁ X Y := by
  subst h
  rfl

private lemma colimitHSInner_wd {m : ℕ}
    (u₁ u₂ v₁ v₂ : Σ k : ℕ, RealBlockStage m k)
    (hu : RealBlockRel m u₁ u₂) (hv : RealBlockRel m v₁ v₂) :
    normHSInner m (max u₁.1 v₁.1)
      (castBlock (Nat.add_sub_cancel' (le_max_left u₁.1 v₁.1))
        (realBlockIter (max u₁.1 v₁.1 - u₁.1) u₁.2))
      (castBlock (Nat.add_sub_cancel' (le_max_right u₁.1 v₁.1))
        (realBlockIter (max u₁.1 v₁.1 - v₁.1) v₁.2)) =
    normHSInner m (max u₂.1 v₂.1)
      (castBlock (Nat.add_sub_cancel' (le_max_left u₂.1 v₂.1))
        (realBlockIter (max u₂.1 v₂.1 - u₂.1) u₂.2))
      (castBlock (Nat.add_sub_cancel' (le_max_right u₂.1 v₂.1))
        (realBlockIter (max u₂.1 v₂.1 - v₂.1) v₂.2)) := by
  rcases hu with ⟨d₁, d₂, h_u, heq_u⟩
  rcases hv with ⟨e₁, e₂, h_v, heq_v⟩
  set M₁ := max u₁.1 v₁.1
  set M₂ := max u₂.1 v₂.1
  set M := max (u₁.1 + d₁) (v₁.1 + e₁)
  set N := M₁ + M₂ + M
  have hN₁ : M₁ ≤ N := le_trans (Nat.le_add_right M₁ M₂) (Nat.le_add_right _ M)
  have hN₂ : M₂ ≤ N := le_trans (Nat.le_add_left M₂ M₁) (Nat.le_add_right _ M)
  have hstab :
      ∀ (u v : Σ k : ℕ, RealBlockStage m k) {M₀ N₀ : ℕ}
        (huM : u.1 ≤ M₀) (hvM : v.1 ≤ M₀) (hMN : M₀ ≤ N₀),
      normHSInner m M₀
        (castBlock (Nat.add_sub_cancel' huM) (realBlockIter (M₀ - u.1) u.2))
        (castBlock (Nat.add_sub_cancel' hvM) (realBlockIter (M₀ - v.1) v.2)) =
      normHSInner m N₀
        (castBlock (Nat.add_sub_cancel' (le_trans huM hMN)) (realBlockIter (N₀ - u.1) u.2))
        (castBlock (Nat.add_sub_cancel' (le_trans hvM hMN)) (realBlockIter (N₀ - v.1) v.2)) := by
    intro u v M₀ N₀ huM hvM hMN
    rw [← normHSInner_realBlockIter (N₀ - M₀)]
    have h_dim : M₀ + (N₀ - M₀) = N₀ := Nat.add_sub_cancel' hMN
    have hL :
        realBlockIter (N₀ - M₀)
          (castBlock (Nat.add_sub_cancel' huM) (realBlockIter (M₀ - u.1) u.2)) =
        castBlock h_dim.symm
          (castBlock (Nat.add_sub_cancel' (le_trans huM hMN)) (realBlockIter (N₀ - u.1) u.2)) := by
      apply eq_of_heq_block rfl
      rw [realBlockIter_castBlock]
      refine HEq.trans (castBlock_heq _ _) ?_
      refine HEq.trans (realBlockIter_split_heq u.2
        ((Nat.add_comm _ _).trans (Nat.sub_add_sub_cancel hMN huM))) ?_
      exact ((castBlock_heq _ _).trans (castBlock_heq _ _)).symm
    have hR :
        realBlockIter (N₀ - M₀)
          (castBlock (Nat.add_sub_cancel' hvM) (realBlockIter (M₀ - v.1) v.2)) =
        castBlock h_dim.symm
          (castBlock (Nat.add_sub_cancel' (le_trans hvM hMN)) (realBlockIter (N₀ - v.1) v.2)) := by
      apply eq_of_heq_block rfl
      rw [realBlockIter_castBlock]
      refine HEq.trans (castBlock_heq _ _) ?_
      refine HEq.trans (realBlockIter_split_heq v.2
        ((Nat.add_comm _ _).trans (Nat.sub_add_sub_cancel hMN hvM))) ?_
      exact ((castBlock_heq _ _).trans (castBlock_heq _ _)).symm
    rw [hL, hR, normHSInner_castBlock]
  rw [hstab u₁ v₁ (le_max_left _ _) (le_max_right _ _) hN₁,
      hstab u₂ v₂ (le_max_left _ _) (le_max_right _ _) hN₂]
  have hu_eq :
      castBlock (Nat.add_sub_cancel' (le_trans (le_max_left u₁.1 v₁.1) hN₁))
        (realBlockIter (N - u₁.1) u₁.2) =
      castBlock (Nat.add_sub_cancel' (le_trans (le_max_left u₂.1 v₂.1) hN₂))
        (realBlockIter (N - u₂.1) u₂.2) := by
    apply eq_of_heq_block rfl
    refine HEq.trans (castBlock_heq _ _) ?_
    refine HEq.trans ?_ (castBlock_heq _ _).symm
    have heq_step :
        HEq (realBlockIter (N - (u₁.1 + d₁)) (realBlockIter d₁ u₁.2))
            (realBlockIter (N - (u₂.1 + d₂)) (realBlockIter d₂ u₂.2)) :=
      realBlockIter_congr_heq_dim (N - (u₁.1 + d₁)) (N - (u₂.1 + d₂)) h_u (by omega) heq_u
    exact (realBlockIter_split_heq u₁.2 (by omega : d₁ + (N - (u₁.1 + d₁)) = N - u₁.1)).symm.trans
      (heq_step.trans (realBlockIter_split_heq u₂.2 (by omega : d₂ + (N - (u₂.1 + d₂)) = N - u₂.1)))
  have hv_eq :
      castBlock (Nat.add_sub_cancel' (le_trans (le_max_right u₁.1 v₁.1) hN₁))
        (realBlockIter (N - v₁.1) v₁.2) =
      castBlock (Nat.add_sub_cancel' (le_trans (le_max_right u₂.1 v₂.1) hN₂))
        (realBlockIter (N - v₂.1) v₂.2) := by
    apply eq_of_heq_block rfl
    refine HEq.trans (castBlock_heq _ _) ?_
    refine HEq.trans ?_ (castBlock_heq _ _).symm
    have heq_step :
        HEq (realBlockIter (N - (v₁.1 + e₁)) (realBlockIter e₁ v₁.2))
            (realBlockIter (N - (v₂.1 + e₂)) (realBlockIter e₂ v₂.2)) :=
      realBlockIter_congr_heq_dim (N - (v₁.1 + e₁)) (N - (v₂.1 + e₂)) h_v (by omega) heq_v
    exact (realBlockIter_split_heq v₁.2 (by omega : e₁ + (N - (v₁.1 + e₁)) = N - v₁.1)).symm.trans
      (heq_step.trans (realBlockIter_split_heq v₂.2 (by omega : e₂ + (N - (v₂.1 + e₂)) = N - v₂.1)))
  rw [hu_eq, hv_eq]

/-- Normalized Hilbert–Schmidt inner product lifted to `RealBlockColimit m`. -/
def colimitHSInner {m : ℕ} (x y : RealBlockColimit m) : ℝ :=
  Quotient.liftOn₂ x y
    (fun u v =>
      let M := max u.1 v.1
      normHSInner m M
        (castBlock (Nat.add_sub_cancel' (le_max_left u.1 v.1)) (realBlockIter (M - u.1) u.2))
        (castBlock (Nat.add_sub_cancel' (le_max_right u.1 v.1)) (realBlockIter (M - v.1) v.2)))
    (fun u₁ v₁ u₂ v₂ hu hv => colimitHSInner_wd u₁ u₂ v₁ v₂ hu hv)

@[simp]
theorem colimitHSInner_toBlockColimit {m : ℕ} (k : ℕ) (X Y : RealBlockStage m k) :
    colimitHSInner (toBlockColimit k X) (toBlockColimit k Y) = normHSInner m k X Y := by
  change normHSInner m (max k k)
    (castBlock (Nat.add_sub_cancel' (le_max_left k k)) (realBlockIter (max k k - k) X))
    (castBlock (Nat.add_sub_cancel' (le_max_right k k)) (realBlockIter (max k k - k) Y)) =
    normHSInner m k X Y
  rw [castBlock_realBlockIter_max (Nat.add_sub_cancel' (le_max_left k k)),
      castBlock_realBlockIter_max (Nat.add_sub_cancel' (le_max_right k k))]
  have hmax : max k k = k := max_self k
  exact normHSInner_castBlock hmax.symm X Y

theorem colimitHSInner_symm {m : ℕ} (x y : RealBlockColimit m) :
    colimitHSInner x y = colimitHSInner y x := by
  rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
  rw [colimitHSInner_toBlockColimit, colimitHSInner_toBlockColimit]
  unfold normHSInner
  rw [hsInner_symm]

theorem colimitHSInner_add_right {m : ℕ} (x y z : RealBlockColimit m) :
    colimitHSInner x (y + z) = colimitHSInner x y + colimitHSInner x z := by
  rcases toBlockColimit_lift_three x y z with ⟨k, X, Y, Z, rfl, rfl, rfl⟩
  rw [add_toBlockColimit, colimitHSInner_toBlockColimit,
      colimitHSInner_toBlockColimit, colimitHSInner_toBlockColimit]
  unfold normHSInner hsInner
  rw [Matrix.mul_add, Matrix.trace_add, mul_add]

theorem colimitHSInner_smul_right {m : ℕ} (c : ℝ) (x y : RealBlockColimit m) :
    colimitHSInner x (c • y) = c * colimitHSInner x y := by
  rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
  rw [smul_toBlockColimit, colimitHSInner_toBlockColimit, colimitHSInner_toBlockColimit]
  unfold normHSInner hsInner
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem colimitHSInner_self_nonneg {m : ℕ} (x : RealBlockColimit m) :
    0 ≤ colimitHSInner x x := by
  rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
  rw [colimitHSInner_toBlockColimit]
  unfold normHSInner
  exact mul_nonneg (by positivity) (hsInner_self_nonneg X)

/-- Faithfulness of `colimitHSInner` across the Jaynesian inductive colimit. -/
theorem colimitHSInner_self_eq_zero_iff {m : ℕ} (x : RealBlockColimit m) :
    colimitHSInner x x = 0 ↔ x = 0 := by
  rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
  rw [colimitHSInner_toBlockColimit]
  unfold normHSInner
  have hpos : (0 : ℝ) < 1 / (2 ^ k : ℝ) := by positivity
  rw [mul_eq_zero, or_iff_right hpos.ne', hsInner_self_eq_zero_iff]
  constructor
  · intro h
    rw [h, toBlockColimit_zero]
  · intro h
    exact toBlockColimit_injective k (h.trans (toBlockColimit_zero k).symm)

/-!
## 3. Jaynesian Inductive Colimit Tomita Polar Decomposition & KMS (`D20`)
-/

/-- Propagated density square-root factor `towerDensity ρ k` at every stage `k`. -/
def towerDensity {m : ℕ} (ρ : PositiveRealDensityFactor m) :
    (k : ℕ) → PositiveRealDensityFactor (blockDim m k)
  | 0 => ρ
  | k + 1 =>
      { r := realBlockStep m k (towerDensity ρ k).r
        rInv := realBlockStep m k (towerDensity ρ k).rInv
        r_symm := by rw [← realBlockStep_transpose, (towerDensity ρ k).r_symm]
        rInv_symm := by rw [← realBlockStep_transpose, (towerDensity ρ k).rInv_symm]
        r_mul_rInv := by rw [← realBlockStep_mul, (towerDensity ρ k).r_mul_rInv, realBlockStep_one]
        rInv_mul_r := by rw [← realBlockStep_mul, (towerDensity ρ k).rInv_mul_r, realBlockStep_one] }

@[simp]
theorem toBlockColimit_towerDensity_r {m : ℕ} (ρ : PositiveRealDensityFactor m) (k : ℕ) :
    toBlockColimit k (towerDensity ρ k).r = toBlockColimit 0 ρ.r := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change toBlockColimit (k + 1) (realBlockStep m k (towerDensity ρ k).r) = toBlockColimit 0 ρ.r
      rw [toBlockColimit_step, ih]

@[simp]
theorem toBlockColimit_towerDensity_rInv {m : ℕ} (ρ : PositiveRealDensityFactor m) (k : ℕ) :
    toBlockColimit k (towerDensity ρ k).rInv = toBlockColimit 0 ρ.rInv := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change toBlockColimit (k + 1) (realBlockStep m k (towerDensity ρ k).rInv) = toBlockColimit 0 ρ.rInv
      rw [toBlockColimit_step, ih]

@[simp]
theorem toBlockColimit_towerDensity_rho {m : ℕ} (ρ : PositiveRealDensityFactor m) (k : ℕ) :
    toBlockColimit k (towerDensity ρ k).rho = toBlockColimit 0 ρ.rho := by
  unfold PositiveRealDensityFactor.rho
  rw [← mul_toBlockColimit, toBlockColimit_towerDensity_r, mul_toBlockColimit]

@[simp]
theorem toBlockColimit_towerDensity_rhoInv {m : ℕ} (ρ : PositiveRealDensityFactor m) (k : ℕ) :
    toBlockColimit k (towerDensity ρ k).rhoInv = toBlockColimit 0 ρ.rhoInv := by
  unfold PositiveRealDensityFactor.rhoInv
  rw [← mul_toBlockColimit, toBlockColimit_towerDensity_rInv, mul_toBlockColimit]

/-- Tomita operator on the Jaynesian inductive colimit `RealBlockColimit m`. -/
def colimitTomitaOp {m : ℕ} (ρ : PositiveRealDensityFactor m) (x : RealBlockColimit m) :
    RealBlockColimit m :=
  toBlockColimit 0 ρ.rInv * star x * toBlockColimit 0 ρ.r

/-- Hilbert–Schmidt adjoint of the colimit Tomita operator. -/
def colimitTomitaAdjOp {m : ℕ} (ρ : PositiveRealDensityFactor m) (x : RealBlockColimit m) :
    RealBlockColimit m :=
  toBlockColimit 0 ρ.r * star x * toBlockColimit 0 ρ.rInv

/-- Modular operator `Δ_ρ` on the Jaynesian inductive colimit. -/
def colimitModularOp {m : ℕ} (ρ : PositiveRealDensityFactor m) (x : RealBlockColimit m) :
    RealBlockColimit m :=
  toBlockColimit 0 ρ.rho * x * toBlockColimit 0 ρ.rhoInv

/-- Modular square root `Δ_ρ^{1/2}` on the Jaynesian inductive colimit. -/
def colimitModularSqrt {m : ℕ} (ρ : PositiveRealDensityFactor m) (x : RealBlockColimit m) :
    RealBlockColimit m :=
  toBlockColimit 0 ρ.r * x * toBlockColimit 0 ρ.rInv

/-- Stage compatibility for `colimitTomitaOp`. -/
theorem colimitTomitaOp_toBlockColimit {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (k : ℕ) (X : RealBlockStage m k) :
    colimitTomitaOp ρ (toBlockColimit k X) =
      toBlockColimit k (tomitaOp (towerDensity ρ k) X) := by
  unfold colimitTomitaOp tomitaOp
  rw [← toBlockColimit_towerDensity_rInv ρ k, ← toBlockColimit_towerDensity_r ρ k,
      star_toBlockColimit_transpose, mul_toBlockColimit, mul_toBlockColimit]

/-- Stage compatibility for `colimitTomitaAdjOp`. -/
theorem colimitTomitaAdjOp_toBlockColimit {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (k : ℕ) (X : RealBlockStage m k) :
    colimitTomitaAdjOp ρ (toBlockColimit k X) =
      toBlockColimit k (tomitaAdjOp (towerDensity ρ k) X) := by
  unfold colimitTomitaAdjOp tomitaAdjOp
  rw [← toBlockColimit_towerDensity_r ρ k, ← toBlockColimit_towerDensity_rInv ρ k,
      star_toBlockColimit_transpose, mul_toBlockColimit, mul_toBlockColimit]

/-- Stage compatibility for `colimitModularOp`. -/
theorem colimitModularOp_toBlockColimit {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (k : ℕ) (X : RealBlockStage m k) :
    colimitModularOp ρ (toBlockColimit k X) =
      toBlockColimit k (modularOp (towerDensity ρ k) X) := by
  unfold colimitModularOp modularOp
  rw [← toBlockColimit_towerDensity_rho ρ k, ← toBlockColimit_towerDensity_rhoInv ρ k,
      mul_toBlockColimit, mul_toBlockColimit]

/-- Stage compatibility for `colimitModularSqrt`. -/
theorem colimitModularSqrt_toBlockColimit {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (k : ℕ) (X : RealBlockStage m k) :
    colimitModularSqrt ρ (toBlockColimit k X) =
      toBlockColimit k (modularSqrt (towerDensity ρ k) X) := by
  unfold colimitModularSqrt modularSqrt
  rw [← toBlockColimit_towerDensity_r ρ k, ← toBlockColimit_towerDensity_rInv ρ k,
      mul_toBlockColimit, mul_toBlockColimit]

/-- Normalized colimit state functional `φ_∞ : RealBlockColimit m →ₗ[ℝ] ℝ`. -/
def colimitState {m : ℕ} (ρ : PositiveRealDensityFactor m) :
    RealBlockColimit m →ₗ[ℝ] ℝ where
  toFun x := colimitHSInner (toBlockColimit 0 ρ.rho) x
  map_add' x y := colimitHSInner_add_right _ x y
  map_smul' c x := by
    rw [colimitHSInner_smul_right, smul_eq_mul, RingHom.id_apply]

@[simp]
theorem colimitState_toBlockColimit_stage {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (k : ℕ) (X : RealBlockStage m k) :
    colimitState ρ (toBlockColimit k X) =
      (1 / (2 ^ k : ℝ)) * state (towerDensity ρ k) X := by
  change colimitHSInner (toBlockColimit 0 ρ.rho) (toBlockColimit k X) = _
  rw [← toBlockColimit_towerDensity_rho ρ k, colimitHSInner_toBlockColimit]
  unfold normHSInner hsInner state
  rw [(towerDensity ρ k).rho_symm]

/-- Exact Tomita polar decomposition on the Jaynesian inductive colimit:
`S_ρ(x) = J (Δ_ρ^{1/2}(x))` where `J = star`. -/
theorem colimit_tomita_polar_decomposition {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (x : RealBlockColimit m) :
    colimitTomitaOp ρ x = star (colimitModularSqrt ρ x) := by
  unfold colimitTomitaOp colimitModularSqrt
  have hr : star (toBlockColimit 0 ρ.r) = toBlockColimit 0 ρ.r := by
    rw [star_toBlockColimit_transpose, ρ.r_symm]
  have hrInv : star (toBlockColimit 0 ρ.rInv) = toBlockColimit 0 ρ.rInv := by
    rw [star_toBlockColimit_transpose, ρ.rInv_symm]
  rw [star_mul, star_mul, hr, hrInv, mul_assoc]

/-- Involution `S_ρ(S_ρ(x)) = x` on the Jaynesian inductive colimit. -/
theorem colimit_tomitaOp_involution {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (x : RealBlockColimit m) :
    colimitTomitaOp ρ (colimitTomitaOp ρ x) = x := by
  unfold colimitTomitaOp
  have hr : star (toBlockColimit 0 ρ.r) = toBlockColimit 0 ρ.r := by
    rw [star_toBlockColimit_transpose, ρ.r_symm]
  have hrInv : star (toBlockColimit 0 ρ.rInv) = toBlockColimit 0 ρ.rInv := by
    rw [star_toBlockColimit_transpose, ρ.rInv_symm]
  have hinv : toBlockColimit 0 ρ.rInv * toBlockColimit 0 ρ.r = 1 := by
    rw [mul_toBlockColimit, ρ.rInv_mul_r, toBlockColimit_one]
  rw [star_mul, star_mul, star_star, hr, hrInv]
  calc
    toBlockColimit 0 ρ.rInv * (toBlockColimit 0 ρ.r * (x * toBlockColimit 0 ρ.rInv)) *
        toBlockColimit 0 ρ.r
        = (toBlockColimit 0 ρ.rInv * toBlockColimit 0 ρ.r) * x *
            (toBlockColimit 0 ρ.rInv * toBlockColimit 0 ρ.r) := by
          simp only [mul_assoc]
    _ = 1 * x * 1 := by rw [hinv]
    _ = x := by simp

/-- Fundamental colimit Tomita identity `F_ρ ∘ S_ρ = Δ_ρ`. -/
theorem colimit_modularOp_eq_adj_comp_tomita {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (x : RealBlockColimit m) :
    colimitTomitaAdjOp ρ (colimitTomitaOp ρ x) = colimitModularOp ρ x := by
  unfold colimitTomitaAdjOp colimitTomitaOp colimitModularOp
  have hr : star (toBlockColimit 0 ρ.r) = toBlockColimit 0 ρ.r := by
    rw [star_toBlockColimit_transpose, ρ.r_symm]
  have hrInv : star (toBlockColimit 0 ρ.rInv) = toBlockColimit 0 ρ.rInv := by
    rw [star_toBlockColimit_transpose, ρ.rInv_symm]
  have hrho : toBlockColimit 0 ρ.rho = toBlockColimit 0 ρ.r * toBlockColimit 0 ρ.r := by
    rw [mul_toBlockColimit]
    rfl
  have hrhoInv : toBlockColimit 0 ρ.rhoInv = toBlockColimit 0 ρ.rInv * toBlockColimit 0 ρ.rInv := by
    rw [mul_toBlockColimit]
    rfl
  rw [star_mul, star_mul, star_star, hr, hrInv, hrho, hrhoInv]
  simp only [mul_assoc]

/-- Hilbert–Schmidt adjointness `⟨x, S_ρ y⟩ = ⟨y, F_ρ x⟩` on `RealBlockColimit m`. -/
theorem colimit_hsInner_tomitaOp_eq {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (x y : RealBlockColimit m) :
    colimitHSInner x (colimitTomitaOp ρ y) = colimitHSInner y (colimitTomitaAdjOp ρ x) := by
  rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
  rw [colimitTomitaOp_toBlockColimit, colimitTomitaAdjOp_toBlockColimit,
      colimitHSInner_toBlockColimit, colimitHSInner_toBlockColimit]
  unfold normHSInner
  rw [hsInner_tomitaOp_eq]

/-- Algebraic KMS boundary condition on the Jaynesian inductive colimit:
`φ_∞(x · Δ_ρ(y)) = φ_∞(y · x)`. -/
theorem colimit_modularOp_kms_identity {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (x y : RealBlockColimit m) :
    colimitState ρ (x * colimitModularOp ρ y) = colimitState ρ (y * x) := by
  rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
  rw [colimitModularOp_toBlockColimit, mul_toBlockColimit, mul_toBlockColimit,
      colimitState_toBlockColimit_stage, colimitState_toBlockColimit_stage,
      modularOp_kms_identity]

/-- Linear modular operator at stage `k` for `InductiveCocone.ModularFlow`. -/
def stageModularLinearMap {m : ℕ} (ρ : PositiveRealDensityFactor m) (k : ℕ) :
    RealBlockStage m k →ₗ[ℝ] RealBlockStage m k where
  toFun X := modularOp (towerDensity ρ k) X
  map_add' X Y := by
    unfold modularOp
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    unfold modularOp
    rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- Instantiation of `InductiveCocone.ModularFlow` on `realBlockInductiveSystem m`,
discharging `kms_colimit_descent` for the entire inductive tower. -/
def colimitModularFlow {m : ℕ} (ρ : PositiveRealDensityFactor m) :
    InductiveCocone.ModularFlow (R := ℝ) (realBlockInductiveSystem m) where
  flow k := stageModularLinearMap ρ k
  commute {i j} hij := by
    ext1 X
    apply toBlockColimit_injective j
    change toBlockColimit j
        (castBlock (Nat.add_sub_cancel' hij) (realBlockIter (j - i) (modularOp (towerDensity ρ i) X))) =
      toBlockColimit j
        (modularOp (towerDensity ρ j) (castBlock (Nat.add_sub_cancel' hij) (realBlockIter (j - i) X)))
    rw [toBlockColimit_castBlock, toBlockColimit_iter, ← colimitModularOp_toBlockColimit,
        ← colimitModularOp_toBlockColimit, toBlockColimit_castBlock, toBlockColimit_iter]

/-- `ModularFlow`-driven KMS descent matching `StarAlgebraCocone.kms_colimit_descent`. -/
theorem colimit_kms_descent {m : ℕ} (ρ : PositiveRealDensityFactor m)
    (k : ℕ) (X Y : RealBlockStage m k) :
    colimitState ρ ((realBlockStarAlgebraCocone m).leg k X * (realBlockStarAlgebraCocone m).leg k Y) =
      colimitState ρ ((realBlockStarAlgebraCocone m).leg k Y *
        (realBlockStarAlgebraCocone m).leg k ((colimitModularFlow ρ).flow k X)) := by
  refine (realBlockStarAlgebraCocone m).kms_colimit_descent
    (colimitModularFlow ρ) (colimitState ρ) ?_ k X Y
  intro i A B
  change colimitState ρ (toBlockColimit i (A * B)) =
    colimitState ρ (toBlockColimit i (B * modularOp (towerDensity ρ i) A))
  rw [colimitState_toBlockColimit_stage, colimitState_toBlockColimit_stage,
      modularOp_kms_identity]

/-- OpenGauss T16 non-commutativity witness preserved in `RealBlockColimit 2`. -/
theorem colimit_diag2_noncomm :
    toBlockColimit (m := 2) 0 matE01 * toBlockColimit (m := 2) 0 matE10 ≠
      toBlockColimit (m := 2) 0 matE10 * toBlockColimit (m := 2) 0 matE01 := by
  intro h
  rw [mul_toBlockColimit, mul_toBlockColimit] at h
  exact matE01_matE10_noncomm (toBlockColimit_injective 0 h)

/-!
## 4. Jaynesian Inductive Colimit Pin(5,5) Bisognano–Wichmann Boost & Wedge KMS (`D21–D22`)
-/

/-- Signature `(5,5)` Krein fundamental symmetry `J55` inside `RealBlockColimit 10`. -/
def colimitJ55 : RealBlockColimit 10 :=
  toBlockColimit 0 J55

/-- One-parameter hyperbolic `Pin(5,5)` boost inside `RealBlockColimit 10`. -/
def colimitPin55Boost (η : ℝ) : RealBlockColimit 10 :=
  toBlockColimit 0 (pin55Boost η)

/-- Euclideanized boost modular flow `σ_τ(x) = Λ(-2πτ) x Λ(2πτ)` inside `RealBlockColimit 10`. -/
def colimitWedgeBoostFlow (t : ℝ) (x : RealBlockColimit 10) : RealBlockColimit 10 :=
  colimitPin55Boost (-2 * Real.pi * t) * x * colimitPin55Boost (2 * Real.pi * t)

/-- Forward lightcone mode `uPlus ⊗ uMinus` lifted to `RealBlockColimit 10`. -/
def colimitLightconeModePlus : RealBlockColimit 10 :=
  toBlockColimit 0 lightconeModePlus

/-- Opposite lightcone mode `uMinus ⊗ uPlus` lifted to `RealBlockColimit 10`. -/
def colimitLightconeModeMinus : RealBlockColimit 10 :=
  toBlockColimit 0 lightconeModeMinus

theorem colimitJ55_sq : colimitJ55 * colimitJ55 = 1 := by
  unfold colimitJ55
  rw [mul_toBlockColimit, J55_mul_self, toBlockColimit_one]

theorem colimitJ55_star : star colimitJ55 = colimitJ55 := by
  unfold colimitJ55
  rw [star_toBlockColimit_transpose, J55_transpose]

@[simp]
theorem colimitPin55Boost_zero : colimitPin55Boost 0 = 1 := by
  unfold colimitPin55Boost
  rw [pin55Boost_zero, toBlockColimit_one]

theorem colimitPin55Boost_add (η₁ η₂ : ℝ) :
    colimitPin55Boost (η₁ + η₂) = colimitPin55Boost η₁ * colimitPin55Boost η₂ := by
  unfold colimitPin55Boost
  rw [pin55Boost_add, mul_toBlockColimit]

theorem colimitPin55Boost_J55_conj (η : ℝ) :
    colimitJ55 * colimitPin55Boost η * colimitJ55 = colimitPin55Boost (-η) := by
  unfold colimitJ55 colimitPin55Boost
  rw [mul_toBlockColimit, mul_toBlockColimit, pin55Boost_J55_conj]

theorem colimitPin55Boost_krein_isometry (η : ℝ) :
    star (colimitPin55Boost η) * colimitJ55 * colimitPin55Boost η = colimitJ55 := by
  unfold colimitJ55 colimitPin55Boost
  rw [star_toBlockColimit_transpose, mul_toBlockColimit, mul_toBlockColimit,
      pin55Boost_krein_isometry]

@[simp]
theorem colimitWedgeBoostFlow_zero_stage (t : ℝ) (X : Matrix (Fin 10) (Fin 10) ℝ) :
    colimitWedgeBoostFlow t (toBlockColimit 0 X) = toBlockColimit 0 (wedgeBoostFlow t X) := by
  unfold colimitWedgeBoostFlow colimitPin55Boost wedgeBoostFlow
  rw [mul_toBlockColimit, mul_toBlockColimit]

theorem colimitWedgeBoostFlow_toBlockColimit (t : ℝ) (k : ℕ) (X : RealBlockStage 10 k) :
    colimitWedgeBoostFlow t (toBlockColimit k X) =
      toBlockColimit k
        ((realBlockInductiveSystem 10).trans (Nat.zero_le k) (pin55Boost (-2 * Real.pi * t)) * X *
          (realBlockInductiveSystem 10).trans (Nat.zero_le k) (pin55Boost (2 * Real.pi * t))) := by
  unfold colimitWedgeBoostFlow colimitPin55Boost
  have h1 : toBlockColimit k ((realBlockInductiveSystem 10).trans (Nat.zero_le k)
      (pin55Boost (-2 * Real.pi * t))) = toBlockColimit 0 (pin55Boost (-2 * Real.pi * t)) :=
    (realBlockStarAlgebraCocone 10).eval_comm (Nat.zero_le k) (pin55Boost (-2 * Real.pi * t))
  have h2 : toBlockColimit k ((realBlockInductiveSystem 10).trans (Nat.zero_le k)
      (pin55Boost (2 * Real.pi * t))) = toBlockColimit 0 (pin55Boost (2 * Real.pi * t)) :=
    (realBlockStarAlgebraCocone 10).eval_comm (Nat.zero_le k) (pin55Boost (2 * Real.pi * t))
  rw [← h1, ← h2, mul_toBlockColimit, mul_toBlockColimit]

/-- Bisognano–Wichmann identification in the Jaynesian inductive colimit:
`Δ_{ρ(2π)} = σ₁` on all elements `x : RealBlockColimit 10`. -/
theorem colimit_bisognanoWichmann_modularOp_eq_wedgeBoostFlow_one (x : RealBlockColimit 10) :
    colimitModularOp (rindlerThermalDensity (2 * Real.pi)) x = colimitWedgeBoostFlow 1 x := by
  unfold colimitModularOp colimitWedgeBoostFlow colimitPin55Boost
  rw [rindlerThermalDensity_rho, rindlerThermalDensity_rhoInv]
  simp [mul_one]

@[simp]
theorem colimit_wedgeBoostFlow_zero (x : RealBlockColimit 10) :
    colimitWedgeBoostFlow 0 x = x := by
  unfold colimitWedgeBoostFlow
  simp [colimitPin55Boost_zero]

/-- One-parameter boost semigroup composition in `RealBlockColimit 10`. -/
theorem colimit_wedgeBoostFlow_semigroup (t₁ t₂ : ℝ) (x : RealBlockColimit 10) :
    colimitWedgeBoostFlow (t₁ + t₂) x =
      colimitWedgeBoostFlow t₁ (colimitWedgeBoostFlow t₂ x) := by
  unfold colimitWedgeBoostFlow
  have hL : -2 * Real.pi * (t₁ + t₂) = (-2 * Real.pi * t₁) + (-2 * Real.pi * t₂) := by ring
  have hR : 2 * Real.pi * (t₁ + t₂) = 2 * Real.pi * t₂ + 2 * Real.pi * t₁ := by ring
  rw [hL, hR, colimitPin55Boost_add, colimitPin55Boost_add]
  simp only [mul_assoc]

/-- Multiplicative *-automorphism property of the colimit boost flow. -/
theorem colimit_wedgeBoostFlow_mul (t : ℝ) (x y : RealBlockColimit 10) :
    colimitWedgeBoostFlow t (x * y) =
      colimitWedgeBoostFlow t x * colimitWedgeBoostFlow t y := by
  have hinv : colimitPin55Boost (2 * Real.pi * t) * colimitPin55Boost (-2 * Real.pi * t) = 1 := by
    rw [← colimitPin55Boost_add, show 2 * Real.pi * t + -2 * Real.pi * t = 0 by ring,
      colimitPin55Boost_zero]
  unfold colimitWedgeBoostFlow
  calc
    colimitPin55Boost (-2 * Real.pi * t) * (x * y) * colimitPin55Boost (2 * Real.pi * t)
        = colimitPin55Boost (-2 * Real.pi * t) * x * 1 * y *
            colimitPin55Boost (2 * Real.pi * t) := by
          simp only [mul_assoc, mul_one]
    _ = colimitPin55Boost (-2 * Real.pi * t) * x *
          (colimitPin55Boost (2 * Real.pi * t) * colimitPin55Boost (-2 * Real.pi * t)) *
          y * colimitPin55Boost (2 * Real.pi * t) := by rw [hinv]
    _ = (colimitPin55Boost (-2 * Real.pi * t) * x * colimitPin55Boost (2 * Real.pi * t)) *
          (colimitPin55Boost (-2 * Real.pi * t) * y * colimitPin55Boost (2 * Real.pi * t)) := by
          simp only [mul_assoc]

/-- Exact wedge KMS boundary condition in `RealBlockColimit 10` at inverse Unruh
temperature `β = 1 / unruhTemperature a = 2π / a`: `φ_β(x · σ_{1/a}(y)) = φ_β(y · x)`. -/
theorem colimit_wedge_kms_condition (a : ℝ) (ha : a > 0) (x y : RealBlockColimit 10) :
    colimitState (rindlerThermalDensity (1 / unruhTemperature a))
        (x * colimitWedgeBoostFlow (1 / a) y) =
      colimitState (rindlerThermalDensity (1 / unruhTemperature a)) (y * x) := by
  rw [← wedge_inverseTemp_eq_inv_unruh a ha]
  have hmod :
      colimitModularOp (rindlerThermalDensity (2 * Real.pi / a)) y =
        colimitWedgeBoostFlow (1 / a) y := by
    unfold colimitModularOp colimitWedgeBoostFlow colimitPin55Boost
    rw [rindlerThermalDensity_rho, rindlerThermalDensity_rhoInv]
    have hL : -(2 * Real.pi / a) = -2 * Real.pi * (1 / a) := by ring
    have hR : 2 * Real.pi / a = 2 * Real.pi * (1 / a) := by ring
    rw [hL, hR]
  rw [← hmod]
  exact colimit_modularOp_kms_identity (rindlerThermalDensity (2 * Real.pi / a)) x y

/-- Forward boost semigroup `t ≥ 0` is strictly contractive on `colimitLightconeModePlus`. -/
theorem colimit_wedgeBoostFlow_hsNormSq_contractive_plus (t : ℝ) (ht : 0 ≤ t) :
    colimitHSInner (colimitWedgeBoostFlow t colimitLightconeModePlus)
        (colimitWedgeBoostFlow t colimitLightconeModePlus) ≤
      colimitHSInner colimitLightconeModePlus colimitLightconeModePlus := by
  unfold colimitLightconeModePlus
  rw [colimitWedgeBoostFlow_zero_stage, colimitHSInner_toBlockColimit,
      colimitHSInner_toBlockColimit]
  unfold normHSInner
  simpa using wedgeBoostFlow_hsNormSq_contractive_plus t ht

/-- Forward boost semigroup `t > 0` expands the opposite mode `colimitLightconeModeMinus`. -/
theorem colimit_wedgeBoostFlow_hsNormSq_expanding_minus (t : ℝ) (ht : 0 < t) :
    colimitHSInner colimitLightconeModeMinus colimitLightconeModeMinus <
      colimitHSInner (colimitWedgeBoostFlow t colimitLightconeModeMinus)
        (colimitWedgeBoostFlow t colimitLightconeModeMinus) := by
  unfold colimitLightconeModeMinus
  rw [colimitWedgeBoostFlow_zero_stage, colimitHSInner_toBlockColimit,
      colimitHSInner_toBlockColimit]
  unfold normHSInner
  simpa using wedgeBoostFlow_hsNormSq_expanding_minus t ht

end InfoGeometry.Canonical.JaynesianTomitaBisognanoColimit
