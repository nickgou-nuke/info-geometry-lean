/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.MarkovCategoryAndColimitInformation

/-!
# Markov Category Comonoid Laws, Bayesian Disintegration, and Blackwell Sufficiency

This module strengthens the `FinSampleSpace` (`FinStoch`) Markov-category pillar with:

1. **Copy–Discard Commutative Comonoid & Symmetric Monoidal Coherence**:
   - Defines `copyKernel`, `swapKernel`, `projLeftKernel`, `projRightKernel`, and
     `assocKernel` as deterministic Markov kernels.
   - Proves the counit (left/right marginal), cocommutativity, and coassociativity comonoid
     laws together with projection naturality for parallel `tensorKernel` channels.
2. **Cho–Jacobs / Fritz Determinism Characterization**:
   - Proves `markov_deterministic_iff_comonoid_hom`: a finite Markov kernel `K : α → β → ℝ`
     commutes with copying (`compose K (copyKernel β) = compose (copyKernel α) (tensorKernel K K)`)
     if and only if every entry lies in `{0, 1}`, if and only if `K = detKernel f` for some
     function `f : α → β`.
3. **Categorical Bayesian Disintegration & Self-Recovery**:
   - Packages prior–channel joint synthesis `jointKernel P K` via `copyKernel` and proves
     exact categorical disintegration: swapping the reversed joint of `(K_* P, posteriorMarkovKernel K P)`
     recovers `jointKernel P K` identically, and pushing `K_* P` back recovers `P`.
4. **Conditional KL Chain Rule & Halmos–Savage–Petz–Blackwell Sufficiency**:
   - Proves the exact conditional KL divergence chain rule
     `KL(P ∥ Q) - KL(K_* P ∥ K_* Q) = ∑ b, (K_* P)_b * KL(P(·|b) ∥ Q(·|b))`.
   - Proves the exact sufficiency equivalence: KL is preserved iff all Bayesian posteriors
     coincide iff likelihood ratios `P(a)/Q(a)` factor through `(K_* P)(b)/(K_* Q)(b)` on
     positive transitions, guaranteeing simultaneous recovery of `P` via `posteriorMarkovKernel K Q`
     and isometric preservation of every Csiszár `f`-divergence and Amari `α`-divergence.
-/

noncomputable section

namespace InfoGeometry.Categorical.MarkovComonoidAndBlackwellSufficiency

open Finset CategoryTheory
open scoped BigOperators
open InfoGeometry.Epistemology.VariationalRG
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.InformationGeometry
open InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity
open InfoGeometry.Categorical.MarkovCategoryAndColimitInformation

/-! ### 1. Copy–Discard Comonoid & Symmetric Monoidal Structure -/

/-- Diagonal copy Markov kernel `δ_α : α → α × α` induced by `a ↦ (a, a)`. -/
def copyKernel (α : Type*) [Fintype α] [DecidableEq α] : MarkovKernel α (α × α) :=
  detKernel (fun a : α => (a, a))

/-- Swap isomorphism Markov kernel `σ : α × β → β × α`. -/
def swapKernel (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    MarkovKernel (α × β) (β × α) :=
  detKernel Prod.swap

/-- Left marginal projection Markov kernel `π₁ : α × β → α`. -/
def projLeftKernel (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] :
    MarkovKernel (α × β) α :=
  detKernel Prod.fst

/-- Right marginal projection Markov kernel `π₂ : α × β → β`. -/
def projRightKernel (α β : Type*) [Fintype α] [Fintype β] [DecidableEq β] :
    MarkovKernel (α × β) β :=
  detKernel Prod.snd

/-- Associator Markov kernel `(α × β) × γ → α × (β × γ)`. -/
def assocKernel (α β γ : Type*) [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    MarkovKernel ((α × β) × γ) (α × (β × γ)) :=
  detKernel (Equiv.prodAssoc α β γ)

theorem tensorKernel_detKernel {α₁ β₁ α₂ β₂ : Type*}
    [Fintype α₁] [Fintype β₁] [Fintype α₂] [Fintype β₂] [DecidableEq β₁] [DecidableEq β₂]
    (f : α₁ → β₁) (g : α₂ → β₂) :
    tensorKernel (detKernel f) (detKernel g) = detKernel (Prod.map f g) := by
  apply markovKernel_ext
  intro p q
  dsimp [tensorKernel, detKernel, Prod.map]
  by_cases h1 : f p.1 = q.1 <;> by_cases h2 : g p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff]

@[simp]
theorem copyKernel_projLeft (α : Type*) [Fintype α] [DecidableEq α] :
    InfoGeometry.Epistemology.VariationalRG.compose (copyKernel α) (projLeftKernel α α) =
      idKernel α := by
  dsimp [copyKernel, projLeftKernel]
  rw [detKernel_comp]
  rfl

@[simp]
theorem copyKernel_projRight (α : Type*) [Fintype α] [DecidableEq α] :
    InfoGeometry.Epistemology.VariationalRG.compose (copyKernel α) (projRightKernel α α) =
      idKernel α := by
  dsimp [copyKernel, projRightKernel]
  rw [detKernel_comp]
  rfl

@[simp]
theorem copyKernel_cocomm (α : Type*) [Fintype α] [DecidableEq α] :
    InfoGeometry.Epistemology.VariationalRG.compose (copyKernel α) (swapKernel α α) =
      copyKernel α := by
  dsimp [copyKernel, swapKernel]
  rw [detKernel_comp]
  rfl

theorem copyKernel_coassoc (α : Type*) [Fintype α] [DecidableEq α] :
    InfoGeometry.Epistemology.VariationalRG.compose
        (InfoGeometry.Epistemology.VariationalRG.compose (copyKernel α)
          (tensorKernel (copyKernel α) (idKernel α)))
        (assocKernel α α α) =
      InfoGeometry.Epistemology.VariationalRG.compose (copyKernel α)
        (tensorKernel (idKernel α) (copyKernel α)) := by
  have hid : idKernel α = detKernel (id : α → α) := rfl
  dsimp [copyKernel, assocKernel]
  rw [hid, tensorKernel_detKernel, tensorKernel_detKernel, detKernel_comp, detKernel_comp,
    detKernel_comp]
  rfl

theorem detKernel_copy_natural {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (f : α → β) :
    InfoGeometry.Epistemology.VariationalRG.compose (detKernel f) (copyKernel β) =
      InfoGeometry.Epistemology.VariationalRG.compose (copyKernel α)
        (tensorKernel (detKernel f) (detKernel f)) := by
  dsimp [copyKernel]
  rw [tensorKernel_detKernel, detKernel_comp, detKernel_comp]
  rfl

/-- Marginal naturality (left projection) of parallel `tensorKernel` channels. -/
theorem tensorKernel_projLeft {α₁ β₁ α₂ β₂ : Type*}
    [Fintype α₁] [Fintype β₁] [Fintype α₂] [Fintype β₂] [DecidableEq α₁] [DecidableEq β₁]
    (K₁ : MarkovKernel α₁ β₁) (K₂ : MarkovKernel α₂ β₂) :
    InfoGeometry.Epistemology.VariationalRG.compose (tensorKernel K₁ K₂) (projLeftKernel β₁ β₂) =
      InfoGeometry.Epistemology.VariationalRG.compose (projLeftKernel α₁ α₂) K₁ := by
  apply markovKernel_ext
  intro p b₁
  rcases p with ⟨a₁, a₂⟩
  dsimp [InfoGeometry.Epistemology.VariationalRG.compose, tensorKernel, projLeftKernel, detKernel]
  have hL :
      ∑ q : β₁ × β₂, (K₁.T a₁ q.1 * K₂.T a₂ q.2) * (if q.1 = b₁ then (1 : ℝ) else 0) =
        K₁.T a₁ b₁ := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ b₁', ∑ b₂', (K₁.T a₁ b₁' * K₂.T a₂ b₂') * (if b₁' = b₁ then (1 : ℝ) else 0)
          = ∑ b₁', (K₁.T a₁ b₁' * (if b₁' = b₁ then (1 : ℝ) else 0)) * ∑ b₂', K₂.T a₂ b₂' := by
              refine Finset.sum_congr rfl ?_
              intro b₁' _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro b₂' _
              ring
      _ = ∑ b₁', K₁.T a₁ b₁' * (if b₁' = b₁ then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro b₁' _
            rw [K₂.sum_one a₂, mul_one]
      _ = K₁.T a₁ b₁ := by
            rw [Finset.sum_eq_single b₁]
            · simp
            · intro b' _ hne
              simp [hne]
            · intro hmem
              exact (hmem (Finset.mem_univ b₁)).elim
  have hR :
      ∑ a₁', (if a₁ = a₁' then (1 : ℝ) else 0) * K₁.T a₁' b₁ = K₁.T a₁ b₁ := by
    rw [Finset.sum_eq_single a₁]
    · simp
    · intro a' _ hne
      simp [hne.symm]
    · intro hmem
      exact (hmem (Finset.mem_univ a₁)).elim
  rw [hL, hR]

/-- Marginal naturality (right projection) of parallel `tensorKernel` channels. -/
theorem tensorKernel_projRight {α₁ β₁ α₂ β₂ : Type*}
    [Fintype α₁] [Fintype β₁] [Fintype α₂] [Fintype β₂] [DecidableEq α₂] [DecidableEq β₂]
    (K₁ : MarkovKernel α₁ β₁) (K₂ : MarkovKernel α₂ β₂) :
    InfoGeometry.Epistemology.VariationalRG.compose (tensorKernel K₁ K₂) (projRightKernel β₁ β₂) =
      InfoGeometry.Epistemology.VariationalRG.compose (projRightKernel α₁ α₂) K₂ := by
  apply markovKernel_ext
  intro p b₂
  rcases p with ⟨a₁, a₂⟩
  dsimp [InfoGeometry.Epistemology.VariationalRG.compose, tensorKernel, projRightKernel, detKernel]
  have hL :
      ∑ q : β₁ × β₂, (K₁.T a₁ q.1 * K₂.T a₂ q.2) * (if q.2 = b₂ then (1 : ℝ) else 0) =
        K₂.T a₂ b₂ := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ b₁', ∑ b₂', (K₁.T a₁ b₁' * K₂.T a₂ b₂') * (if b₂' = b₂ then (1 : ℝ) else 0)
          = ∑ b₁', K₁.T a₁ b₁' * ∑ b₂', K₂.T a₂ b₂' * (if b₂' = b₂ then (1 : ℝ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro b₁' _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro b₂' _
              ring
      _ = ∑ b₁', K₁.T a₁ b₁' * K₂.T a₂ b₂ := by
            refine Finset.sum_congr rfl ?_
            intro b₁' _
            rw [Finset.sum_eq_single b₂]
            · simp
            · intro b' _ hne
              simp [hne]
            · intro hmem
              exact (hmem (Finset.mem_univ b₂)).elim
      _ = (∑ b₁', K₁.T a₁ b₁') * K₂.T a₂ b₂ := by rw [← Finset.sum_mul]
      _ = K₂.T a₂ b₂ := by rw [K₁.sum_one a₁, one_mul]
  have hR :
      ∑ a₂', (if a₂ = a₂' then (1 : ℝ) else 0) * K₂.T a₂' b₂ = K₂.T a₂ b₂ := by
    rw [Finset.sum_eq_single a₂]
    · simp
    · intro a' _ hne
      simp [hne.symm]
    · intro hmem
      exact (hmem (Finset.mem_univ a₂)).elim
  rw [hL, hR]

/-! ### 2. Cho–Jacobs / Fritz Determinism Characterization Theorem -/

lemma compose_copyKernel_right_apply {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (K : MarkovKernel α β) (a : α) (b₁ b₂ : β) :
    (InfoGeometry.Epistemology.VariationalRG.compose K (copyKernel β)).T a (b₁, b₂) =
      if b₁ = b₂ then K.T a b₁ else 0 := by
  dsimp [InfoGeometry.Epistemology.VariationalRG.compose, copyKernel, detKernel]
  by_cases h : b₁ = b₂
  · subst h
    simp only [↓reduceIte, Prod.mk.injEq, and_self]
    rw [Finset.sum_eq_single b₁]
    · simp
    · intro b' _ hne
      simp [hne]
    · intro hmem
      exact (hmem (Finset.mem_univ b₁)).elim
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero ?_
    intro b _
    have hneq : (b, b) ≠ (b₁, b₂) := by
      intro heq
      apply h
      have hb1 : b = b₁ := congrArg Prod.fst heq
      have hb2 : b = b₂ := congrArg Prod.snd heq
      exact hb1.symm.trans hb2
    simp [hneq]

lemma copyKernel_compose_tensorKernel_apply {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (K : MarkovKernel α β) (a : α) (b₁ b₂ : β) :
    (InfoGeometry.Epistemology.VariationalRG.compose (copyKernel α) (tensorKernel K K)).T a (b₁, b₂) =
      K.T a b₁ * K.T a b₂ := by
  dsimp [InfoGeometry.Epistemology.VariationalRG.compose, copyKernel, tensorKernel, detKernel]
  rw [Finset.sum_eq_single (a, a)]
  · simp
  · intro p _ hne
    simp [hne.symm]
  · intro hmem
    exact (hmem (Finset.mem_univ (a, a))).elim

lemma markov_zero_one_off_diag_zero {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (K : MarkovKernel α β)
    (hzo : ∀ a b, K.T a b = 0 ∨ K.T a b = 1)
    {a : α} {b₁ b₂ : β} (hne : b₁ ≠ b₂) (hb₁ : K.T a b₁ = 1) :
    K.T a b₂ = 0 := by
  rcases hzo a b₂ with h0 | h1
  · exact h0
  · exfalso
    have hsum : ∑ b : β, K.T a b = 1 := K.sum_one a
    have hge : K.T a b₁ + K.T a b₂ ≤ ∑ b : β, K.T a b := by
      have hsub : ({b₁, b₂} : Finset β) ⊆ Finset.univ := Finset.subset_univ _
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun b _ _ => K.nonneg a b)
      rw [Finset.sum_pair hne] at hle
      exact hle
    rw [hb₁, h1] at hge
    linarith

/-- Comonoid homomorphism condition (`K ≫ copy = copy ≫ (K ⊗ K)`) holds iff every kernel
entry lies in `{0, 1}`. -/
theorem copy_commutes_iff_zero_one {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (K : MarkovKernel α β) :
    InfoGeometry.Epistemology.VariationalRG.compose K (copyKernel β) =
        InfoGeometry.Epistemology.VariationalRG.compose (copyKernel α) (tensorKernel K K) ↔
      ∀ a b, K.T a b = 0 ∨ K.T a b = 1 := by
  constructor
  · intro h a b
    have hent := congrArg (fun M : MarkovKernel α (β × β) => M.T a (b, b)) h
    rw [compose_copyKernel_right_apply, copyKernel_compose_tensorKernel_apply] at hent
    simp only [↓reduceIte] at hent
    have hfac : K.T a b * (K.T a b - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · intro hzo
    apply markovKernel_ext
    intro a q
    rcases q with ⟨b₁, b₂⟩
    rw [compose_copyKernel_right_apply, copyKernel_compose_tensorKernel_apply]
    by_cases h : b₁ = b₂
    · subst h
      simp only [↓reduceIte]
      rcases hzo a b₁ with h0 | h1
      · simp [h0]
      · simp [h1]
    · simp only [h, ↓reduceIte]
      rcases hzo a b₁ with h0 | h1
      · simp [h0]
      · have hb2 : K.T a b₂ = 0 := markov_zero_one_off_diag_zero K hzo h h1
        simp [hb2]

/-- A Markov kernel has all entries in `{0, 1}` iff it is induced deterministically by a
function `f : α → β`. -/
theorem zero_one_iff_exists_detKernel {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (K : MarkovKernel α β) :
    (∀ a b, K.T a b = 0 ∨ K.T a b = 1) ↔ ∃ f : α → β, K = detKernel f := by
  classical
  constructor
  · intro hzo
    have huniq (a : α) : ∃ b : β, K.T a b = 1 := by
      by_contra hnone
      push Not at hnone
      have hall0 : ∀ b : β, K.T a b = 0 := by
        intro b
        rcases hzo a b with h0 | h1
        · exact h0
        · exact (hnone b h1).elim
      have hsum0 : ∑ b : β, K.T a b = 0 := Finset.sum_eq_zero (fun b _ => hall0 b)
      linarith [K.sum_one a]
    choose f hf using huniq
    refine ⟨f, markovKernel_ext ?_⟩
    intro a b
    dsimp [detKernel]
    by_cases hfab : f a = b
    · simp [hfab]
      rw [← hfab]
      exact hf a
    · simp [hfab]
      exact markov_zero_one_off_diag_zero K hzo hfab (hf a)
  · rintro ⟨f, rfl⟩ a b
    dsimp [detKernel]
    by_cases hfab : f a = b
    · exact Or.inr (by simp [hfab])
    · exact Or.inl (by simp [hfab])

/-- **Cho–Jacobs / Fritz Determinism Theorem**: a finite Markov kernel is deterministic
(`∃ f, K = detKernel f`) if and only if it is a comonoid homomorphism with respect to
`copyKernel`. -/
theorem markov_deterministic_iff_comonoid_hom {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (K : MarkovKernel α β) :
    InfoGeometry.Epistemology.VariationalRG.compose K (copyKernel β) =
        InfoGeometry.Epistemology.VariationalRG.compose (copyKernel α) (tensorKernel K K) ↔
      ∃ f : α → β, K = detKernel f :=
  (copy_commutes_iff_zero_one K).trans (zero_one_iff_exists_detKernel K)

/-! ### 3. Categorical Bayesian Disintegration & Self-Recovery -/

/-- State preparation Markov kernel `PUnit → α` determined by `P : ProbDist α`. -/
def stateKernel {α : Type*} [Fintype α] (P : ProbDist α) : MarkovKernel PUnit α where
  T _ a := P.p a
  nonneg _ a := P.nonneg a
  sum_one _ := P.sum_one

/-- Bayesian bloom (joint conditional emission) `α → α × β` of a Markov channel `K`. -/
def bloomKernel {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (K : MarkovKernel α β) : MarkovKernel α (α × β) :=
  InfoGeometry.Epistemology.VariationalRG.compose (copyKernel α) (tensorKernel (idKernel α) K)

/-- Joint distribution kernel `PUnit → α × β` generated by prior `P` followed by channel `K`. -/
def jointKernel {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (P : ProbDist α) (K : MarkovKernel α β) : MarkovKernel PUnit (α × β) :=
  InfoGeometry.Epistemology.VariationalRG.compose (stateKernel P) (bloomKernel K)

@[simp]
theorem bloomKernel_apply {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (K : MarkovKernel α β) (a a' : α) (b : β) :
    (bloomKernel K).T a (a', b) = if a = a' then K.T a b else 0 := by
  dsimp [bloomKernel, InfoGeometry.Epistemology.VariationalRG.compose, copyKernel, detKernel,
    tensorKernel, idKernel]
  rw [Finset.sum_eq_single (a, a)]
  · by_cases h : a = a'
    · subst h; simp
    · simp [h]
  · intro p _ hne
    simp [hne.symm]
  · intro hmem
    exact (hmem (Finset.mem_univ (a, a))).elim

@[simp]
theorem jointKernel_apply {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (P : ProbDist α) (K : MarkovKernel α β) (u : PUnit) (a : α) (b : β) :
    (jointKernel P K).T u (a, b) = P.p a * K.T a b := by
  dsimp [jointKernel, InfoGeometry.Epistemology.VariationalRG.compose, stateKernel]
  calc
    ∑ a', P.p a' * (bloomKernel K).T a' (a, b)
        = ∑ a', P.p a' * (if a' = a then K.T a' b else 0) := by
            refine Finset.sum_congr rfl ?_
            intro a' _
            rw [bloomKernel_apply]
    _ = P.p a * K.T a b := by
          rw [Finset.sum_eq_single a]
          · simp
          · intro a' _ hne
            simp [hne]
          · intro hmem
            exact (hmem (Finset.mem_univ a)).elim

/-- **Categorical Bayesian Disintegration**: for any simplex-interior prior `P : ProbInterior α`
and column-non-degenerate channel `K : α → β`, the joint distribution synthesized by
`(P, K)` equals the swapped joint distribution synthesized by `(K_* P, posteriorMarkovKernel K P hcol)`. -/
theorem categorical_bayesian_disintegration {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (K : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate K) :
    jointKernel (toProbDist P) K =
      InfoGeometry.Epistemology.VariationalRG.compose
        (jointKernel (toProbDist (pushInterior K P hcol)) (posteriorMarkovKernel K P hcol))
        (swapKernel β α) := by
  apply markovKernel_ext
  intro u q
  rcases q with ⟨a, b⟩
  rw [jointKernel_apply]
  dsimp [InfoGeometry.Epistemology.VariationalRG.compose, swapKernel, detKernel]
  rw [Fintype.sum_prod_type]
  calc
    (toProbDist P).p a * K.T a b
        = (toProbDist (pushInterior K P hcol)).p b * posteriorKernel K P hcol b a := by
            unfold posteriorKernel
            have hpos : (pushInterior K P hcol).p b ≠ 0 :=
              ne_of_gt ((pushInterior K P hcol).pos b)
            dsimp [toProbDist]
            exact (mul_div_cancel₀ _ hpos).symm
    _ = ∑ b', ∑ a',
          (jointKernel (toProbDist (pushInterior K P hcol)) (posteriorMarkovKernel K P hcol)).T u
              (b', a') *
            (if (b', a').swap = (a, b) then 1 else 0) := by
          rw [Finset.sum_eq_single b]
          · rw [Finset.sum_eq_single a]
            · simp [jointKernel_apply, posteriorMarkovKernel]
            · intro a' _ hne
              simp [hne]
            · intro hmem
              exact (hmem (Finset.mem_univ a)).elim
          · intro b' _ hne
            refine Finset.sum_eq_zero ?_
            intro a' _
            simp [hne]
          · intro hmem
            exact (hmem (Finset.mem_univ b)).elim

/-- Marginal consistency of Bayesian inversion: pushing `(K_* P)` back along the Bayesian
posterior kernel `posteriorMarkovKernel K P hcol` recovers `P` identically. -/
theorem posteriorMarkovKernel_self_recovery {α β : Type*} [Fintype α] [Fintype β]
    (K : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate K) :
    pushforward (posteriorMarkovKernel K P hcol) (toProbDist (pushInterior K P hcol)) =
      toProbDist P := by
  apply probDist_ext
  funext a
  dsimp [pushforward, toProbDist, posteriorMarkovKernel, posteriorKernel]
  calc
    ∑ b, (pushInterior K P hcol).p b * ((P.p a * K.T a b) / (pushInterior K P hcol).p b)
        = ∑ b, P.p a * K.T a b := by
            refine Finset.sum_congr rfl ?_
            intro b _
            exact mul_div_cancel₀ _ (ne_of_gt ((pushInterior K P hcol).pos b))
    _ = P.p a * ∑ b, K.T a b := by rw [← Finset.mul_sum]
    _ = P.p a := by rw [K.sum_one a, mul_one]

/-! ### 4. Conditional KL Chain Rule & Halmos–Savage–Petz–Blackwell Sufficiency -/

lemma log_lt_sub_one_of_pos_ne_one {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    Real.log x < x - 1 := by
  have hlog_ne : Real.log x ≠ 0 := by
    intro h0
    exact hne ((Real.log_eq_zero.mp h0).resolve_left hx.ne' |>.resolve_right (by linarith))
  have hexp := Real.add_one_lt_exp hlog_ne
  rw [Real.exp_log hx] at hexp
  linarith

/-- **Exact Conditional KL Divergence Chain Rule**:
`KL(P ∥ Q) - KL(K_* P ∥ K_* Q) = ∑ b, (K_* P)_b * KL(P(·|b) ∥ Q(·|b))`. -/
theorem relativeEntropy_markov_chain_rule {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (K : MarkovKernel α β) (hcol : ColNondegenerate K) (P Q : ProbInterior α) :
    ArakiDonald.relativeEntropy P.p Q.p -
        ArakiDonald.relativeEntropy (pushInterior K P hcol).p (pushInterior K Q hcol).p =
      ∑ b, (pushInterior K P hcol).p b *
        ArakiDonald.relativeEntropy (posteriorKernel K P hcol b) (posteriorKernel K Q hcol b) := by
  let P' := pushInterior K P hcol
  let Q' := pushInterior K Q hcol
  have hterm (b : β) (a : α) :
      P'.p b * (posteriorKernel K P hcol b a *
          Real.log (posteriorKernel K P hcol b a / posteriorKernel K Q hcol b a)) =
        P.p a * K.T a b * (Real.log (P.p a / Q.p a) - Real.log (P'.p b / Q'.p b)) := by
    by_cases hK : K.T a b = 0
    · simp [posteriorKernel, hK]
    · have hP'ne : P'.p b ≠ 0 := ne_of_gt (P'.pos b)
      have hQ'ne : Q'.p b ≠ 0 := ne_of_gt (Q'.pos b)
      have hQne : Q.p a ≠ 0 := ne_of_gt (Q.pos a)
      have hPne : P.p a ≠ 0 := ne_of_gt (P.pos a)
      have hratio :
          posteriorKernel K P hcol b a / posteriorKernel K Q hcol b a =
            (P.p a / Q.p a) / (P'.p b / Q'.p b) := by
        unfold posteriorKernel
        dsimp only [P', Q'] at hP'ne hQ'ne ⊢
        field_simp [hK, hP'ne, hQ'ne, hQne]
      have hmul : P'.p b * posteriorKernel K P hcol b a = P.p a * K.T a b := by
        unfold posteriorKernel
        exact mul_div_cancel₀ _ hP'ne
      rw [← mul_assoc, hmul, hratio,
        Real.log_div (div_ne_zero hPne hQne) (div_ne_zero hP'ne hQ'ne)]
  symm
  calc
    ∑ b, P'.p b * ArakiDonald.relativeEntropy (posteriorKernel K P hcol b)
        (posteriorKernel K Q hcol b)
        = ∑ b, ∑ a, P'.p b * (posteriorKernel K P hcol b a *
            Real.log (posteriorKernel K P hcol b a / posteriorKernel K Q hcol b a)) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            unfold ArakiDonald.relativeEntropy
            rw [Finset.mul_sum]
    _ = ∑ b, ∑ a, (P.p a * K.T a b * Real.log (P.p a / Q.p a) -
            P.p a * K.T a b * Real.log (P'.p b / Q'.p b)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [hterm b a]
          ring
    _ = (∑ b, ∑ a, P.p a * K.T a b * Real.log (P.p a / Q.p a)) -
          (∑ b, ∑ a, P.p a * K.T a b * Real.log (P'.p b / Q'.p b)) := by
          simp_rw [Finset.sum_sub_distrib]
    _ = (∑ a, ∑ b, P.p a * Real.log (P.p a / Q.p a) * K.T a b) -
          (∑ b, (∑ a, P.p a * K.T a b) * Real.log (P'.p b / Q'.p b)) := by
          congr 1
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            ring
          · refine Finset.sum_congr rfl ?_
            intro b _
            rw [← Finset.sum_mul]
    _ = (∑ a, P.p a * Real.log (P.p a / Q.p a) * ∑ b, K.T a b) -
          ∑ b, P'.p b * Real.log (P'.p b / Q'.p b) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← Finset.mul_sum]
    _ = ArakiDonald.relativeEntropy P.p Q.p - ArakiDonald.relativeEntropy P'.p Q'.p := by
          congr 1
          unfold ArakiDonald.relativeEntropy
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [K.sum_one a, mul_one]

lemma posterior_relativeEntropy_nonneg {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α]
    (K : MarkovKernel α β) (hcol : ColNondegenerate K) (P Q : ProbInterior α) (b : β) :
    0 ≤ ArakiDonald.relativeEntropy (posteriorKernel K P hcol b) (posteriorKernel K Q hcol b) := by
  have hterm (a : α) :
      posteriorKernel K P hcol b a - posteriorKernel K Q hcol b a ≤
        posteriorKernel K P hcol b a *
          Real.log (posteriorKernel K P hcol b a / posteriorKernel K Q hcol b a) := by
    by_cases hK : K.T a b = 0
    · simp [posteriorKernel, hK]
    · have hKpos : 0 < K.T a b := lt_of_le_of_ne (K.nonneg a b) (Ne.symm hK)
      have hr : 0 < posteriorKernel K P hcol b a := by
        unfold posteriorKernel
        exact div_pos (mul_pos (P.pos a) hKpos) ((pushInterior K P hcol).pos b)
      have hs : 0 < posteriorKernel K Q hcol b a := by
        unfold posteriorKernel
        exact div_pos (mul_pos (Q.pos a) hKpos) ((pushInterior K Q hcol).pos b)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hs hr)
      rw [← inv_div (posteriorKernel K P hcol b a) (posteriorKernel K Q hcol b a),
        Real.log_inv] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hr.le
      rw [mul_sub, mul_one, inv_div, mul_div_cancel₀ _ hr.ne'] at hmul
      linarith
  have hdiff_sum :
      ∑ a, (posteriorKernel K P hcol b a - posteriorKernel K Q hcol b a) = 0 := by
    rw [Finset.sum_sub_distrib, posteriorKernel_sum_one K P hcol b,
      posteriorKernel_sum_one K Q hcol b, sub_self]
  calc
    0 = ∑ a, (posteriorKernel K P hcol b a - posteriorKernel K Q hcol b a) := hdiff_sum.symm
    _ ≤ ArakiDonald.relativeEntropy (posteriorKernel K P hcol b) (posteriorKernel K Q hcol b) :=
          Finset.sum_le_sum (fun a _ => hterm a)

lemma posterior_relativeEntropy_eq_zero_iff {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α]
    (K : MarkovKernel α β) (hcol : ColNondegenerate K) (P Q : ProbInterior α) (b : β) :
    ArakiDonald.relativeEntropy (posteriorKernel K P hcol b) (posteriorKernel K Q hcol b) = 0 ↔
      ∀ a : α, posteriorKernel K P hcol b a = posteriorKernel K Q hcol b a := by
  have hterm_ge (a : α) :
      0 ≤ posteriorKernel K P hcol b a *
          Real.log (posteriorKernel K P hcol b a / posteriorKernel K Q hcol b a) -
        (posteriorKernel K P hcol b a - posteriorKernel K Q hcol b a) := by
    by_cases hK : K.T a b = 0
    · simp [posteriorKernel, hK]
    · have hKpos : 0 < K.T a b := lt_of_le_of_ne (K.nonneg a b) (Ne.symm hK)
      have hr : 0 < posteriorKernel K P hcol b a := by
        unfold posteriorKernel
        exact div_pos (mul_pos (P.pos a) hKpos) ((pushInterior K P hcol).pos b)
      have hs : 0 < posteriorKernel K Q hcol b a := by
        unfold posteriorKernel
        exact div_pos (mul_pos (Q.pos a) hKpos) ((pushInterior K Q hcol).pos b)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hs hr)
      rw [← inv_div (posteriorKernel K P hcol b a) (posteriorKernel K Q hcol b a),
        Real.log_inv] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hr.le
      rw [mul_sub, mul_one, inv_div, mul_div_cancel₀ _ hr.ne'] at hmul
      linarith
  have hgap :
      ArakiDonald.relativeEntropy (posteriorKernel K P hcol b) (posteriorKernel K Q hcol b) =
        ∑ a, (posteriorKernel K P hcol b a *
            Real.log (posteriorKernel K P hcol b a / posteriorKernel K Q hcol b a) -
          (posteriorKernel K P hcol b a - posteriorKernel K Q hcol b a)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, posteriorKernel_sum_one K P hcol b,
      posteriorKernel_sum_one K Q hcol b, sub_self, sub_zero]
    rfl
  constructor
  · intro hzero a
    rw [hgap] at hzero
    have hterm0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a' _ => hterm_ge a')).mp hzero a
      (Finset.mem_univ a)
    by_cases hK : K.T a b = 0
    · simp [posteriorKernel, hK]
    · have hKpos : 0 < K.T a b := lt_of_le_of_ne (K.nonneg a b) (Ne.symm hK)
      have hr : 0 < posteriorKernel K P hcol b a := by
        unfold posteriorKernel
        exact div_pos (mul_pos (P.pos a) hKpos) ((pushInterior K P hcol).pos b)
      have hs : 0 < posteriorKernel K Q hcol b a := by
        unfold posteriorKernel
        exact div_pos (mul_pos (Q.pos a) hKpos) ((pushInterior K Q hcol).pos b)
      by_contra hne
      have hsr_ne : posteriorKernel K Q hcol b a / posteriorKernel K P hcol b a ≠ 1 := by
        intro h1
        exact hne ((div_eq_one_iff_eq hr.ne').mp h1).symm
      have hlt := log_lt_sub_one_of_pos_ne_one (div_pos hs hr) hsr_ne
      rw [← inv_div (posteriorKernel K P hcol b a) (posteriorKernel K Q hcol b a),
        Real.log_inv] at hlt
      have hmul := mul_lt_mul_of_pos_left hlt hr
      rw [mul_sub, mul_one, inv_div, mul_div_cancel₀ _ hr.ne'] at hmul
      linarith
  · intro hpost
    unfold ArakiDonald.relativeEntropy
    refine Finset.sum_eq_zero ?_
    intro a _
    rw [hpost a]
    by_cases hK : K.T a b = 0
    · simp [posteriorKernel, hK]
    · have hKpos : 0 < K.T a b := lt_of_le_of_ne (K.nonneg a b) (Ne.symm hK)
      have hs : posteriorKernel K Q hcol b a ≠ 0 := by
        unfold posteriorKernel
        exact div_ne_zero (mul_ne_zero (Q.pos a).ne' hKpos.ne') ((pushInterior K Q hcol).pos b).ne'
      rw [div_self hs, Real.log_one, mul_zero]

/-- **KL–Bayesian Sufficiency Characterization**: pushing along `K` preserves KL relative
entropy (`KL(K_* P ∥ K_* Q) = KL(P ∥ Q)`) if and only if every Bayesian posterior conditional
matches (`P(a | b) = Q(a | b)` for all `a, b`). -/
theorem relativeEntropy_pushInterior_eq_iff_posterior_eq {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (K : MarkovKernel α β) (hcol : ColNondegenerate K) (P Q : ProbInterior α) :
    ArakiDonald.relativeEntropy (pushInterior K P hcol).p (pushInterior K Q hcol).p =
        ArakiDonald.relativeEntropy P.p Q.p ↔
      ∀ b a, posteriorKernel K P hcol b a = posteriorKernel K Q hcol b a := by
  have hchain := relativeEntropy_markov_chain_rule K hcol P Q
  have hnonneg :
      ∀ b ∈ (Finset.univ : Finset β),
        0 ≤ (pushInterior K P hcol).p b *
          ArakiDonald.relativeEntropy (posteriorKernel K P hcol b) (posteriorKernel K Q hcol b) :=
    fun b _ => mul_nonneg ((pushInterior K P hcol).pos b).le
      (posterior_relativeEntropy_nonneg K hcol P Q b)
  constructor
  · intro heq b a
    have hsum0 :
        ∑ b', (pushInterior K P hcol).p b' *
          ArakiDonald.relativeEntropy (posteriorKernel K P hcol b')
            (posteriorKernel K Q hcol b') = 0 := by
      linarith [hchain, heq]
    have hb0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0 b (Finset.mem_univ b)
    have hkl0 :
        ArakiDonald.relativeEntropy (posteriorKernel K P hcol b) (posteriorKernel K Q hcol b) = 0 :=
      (mul_eq_zero.mp hb0).resolve_left ((pushInterior K P hcol).pos b).ne'
    exact (posterior_relativeEntropy_eq_zero_iff K hcol P Q b).mp hkl0 a
  · intro hpost
    have hsum0 :
        ∑ b, (pushInterior K P hcol).p b *
          ArakiDonald.relativeEntropy (posteriorKernel K P hcol b)
            (posteriorKernel K Q hcol b) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b _
      have hkl0 := (posterior_relativeEntropy_eq_zero_iff K hcol P Q b).mpr (hpost b)
      rw [hkl0, mul_zero]
    linarith [hchain, hsum0]

/-- Halmos–Savage likelihood-ratio factorization equivalence: coinciding Bayesian posteriors
for `P` and `Q` hold iff the likelihood ratio `P(a) / Q(a)` factors through `(K_* P)(b) / (K_* Q)(b)`
across every positive transition `0 < K.T a b`. -/
theorem posterior_eq_iff_likelihood_ratio {α β : Type*} [Fintype α] [Fintype β]
    (K : MarkovKernel α β) (hcol : ColNondegenerate K) (P Q : ProbInterior α) :
    (∀ b a, posteriorKernel K P hcol b a = posteriorKernel K Q hcol b a) ↔
      ∀ a b, 0 < K.T a b →
        P.p a / Q.p a = (pushInterior K P hcol).p b / (pushInterior K Q hcol).p b := by
  constructor
  · intro hpost a b hK
    have hb := hpost b a
    unfold posteriorKernel at hb
    have hKne : K.T a b ≠ 0 := ne_of_gt hK
    have hP'ne : (pushInterior K P hcol).p b ≠ 0 := ne_of_gt ((pushInterior K P hcol).pos b)
    have hQ'ne : (pushInterior K Q hcol).p b ≠ 0 := ne_of_gt ((pushInterior K Q hcol).pos b)
    have hQne : Q.p a ≠ 0 := ne_of_gt (Q.pos a)
    exact (div_eq_div_iff hQne hQ'ne).mpr (by
      calc
        P.p a * (pushInterior K Q hcol).p b
            = ((P.p a * K.T a b) / (pushInterior K P hcol).p b) *
                ((pushInterior K P hcol).p b * (pushInterior K Q hcol).p b) / K.T a b := by
                field_simp [hP'ne, hKne]
        _ = ((Q.p a * K.T a b) / (pushInterior K Q hcol).p b) *
                ((pushInterior K P hcol).p b * (pushInterior K Q hcol).p b) / K.T a b := by rw [hb]
        _ = (pushInterior K P hcol).p b * Q.p a := by
              field_simp [hQ'ne, hKne])
  · intro hlr b a
    by_cases hK : K.T a b = 0
    · simp [posteriorKernel, hK]
    · have hKpos : 0 < K.T a b := lt_of_le_of_ne (K.nonneg a b) (Ne.symm hK)
      have hrat := hlr a b hKpos
      have hP'ne : (pushInterior K P hcol).p b ≠ 0 := ne_of_gt ((pushInterior K P hcol).pos b)
      have hQ'ne : (pushInterior K Q hcol).p b ≠ 0 := ne_of_gt ((pushInterior K Q hcol).pos b)
      have hQne : Q.p a ≠ 0 := ne_of_gt (Q.pos a)
      have hcross : P.p a * (pushInterior K Q hcol).p b = (pushInterior K P hcol).p b * Q.p a :=
        (div_eq_div_iff hQne hQ'ne).mp hrat
      unfold posteriorKernel
      exact (div_eq_div_iff hP'ne hQ'ne).mpr (by
        calc
          P.p a * K.T a b * (pushInterior K Q hcol).p b
              = (P.p a * (pushInterior K Q hcol).p b) * K.T a b := by ring
          _ = ((pushInterior K P hcol).p b * Q.p a) * K.T a b := by rw [hcross]
          _ = Q.p a * K.T a b * (pushInterior K P hcol).p b := by ring)

/-- **Blackwell–Petz Universal Recovery from KL Preservation**:
whenever `K` preserves `KL(P ∥ Q)`, the fixed Bayesian Petz transpose channel
`posteriorMarkovKernel K Q hcol` simultaneously recovers `P` from `K_* P`
(`pushforward (posteriorMarkovKernel K Q hcol) (K_* P) = P`), matching its recovery of `Q`. -/
theorem relativeEntropy_eq_implies_petz_simultaneous_recovery
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (K : MarkovKernel α β) (hcol : ColNondegenerate K) (P Q : ProbInterior α)
    (heq : ArakiDonald.relativeEntropy (pushInterior K P hcol).p (pushInterior K Q hcol).p =
      ArakiDonald.relativeEntropy P.p Q.p) :
    pushforward (posteriorMarkovKernel K Q hcol) (toProbDist (pushInterior K P hcol)) =
      toProbDist P := by
  have hpost := (relativeEntropy_pushInterior_eq_iff_posterior_eq K hcol P Q).mp heq
  apply probDist_ext
  funext a
  have hsub :
      (posteriorMarkovKernel K Q hcol).T = (posteriorMarkovKernel K P hcol).T := by
    funext b a'
    exact (hpost b a').symm
  have hrec := congrFun (congrArg ProbDist.p (posteriorMarkovKernel_self_recovery K P hcol)) a
  simpa [pushforward, hsub] using hrec

/-- Isometric preservation of every Csiszár `f`-divergence under a sufficient Markov kernel
(whenever KL is preserved between `P` and `Q`). -/
theorem csiszarFDivergence_preserved_of_kl_sufficient
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (K : MarkovKernel α β) (hcol : ColNondegenerate K) (P Q : ProbInterior α)
    (f : ℝ → ℝ)
    (heq : ArakiDonald.relativeEntropy (pushInterior K P hcol).p (pushInterior K Q hcol).p =
      ArakiDonald.relativeEntropy P.p Q.p) :
    csiszarFDivergence f (pushInterior K P hcol).p (pushInterior K Q hcol).p =
      csiszarFDivergence f P.p Q.p := by
  have hlr := (posterior_eq_iff_likelihood_ratio K hcol P Q).mp
    ((relativeEntropy_pushInterior_eq_iff_posterior_eq K hcol P Q).mp heq)
  unfold csiszarFDivergence
  calc
    ∑ b, (pushInterior K Q hcol).p b *
        f ((pushInterior K P hcol).p b / (pushInterior K Q hcol).p b)
        = ∑ b, (∑ a, Q.p a * K.T a b) *
            f ((pushInterior K P hcol).p b / (pushInterior K Q hcol).p b) := rfl
    _ = ∑ b, ∑ a, Q.p a * K.T a b *
            f ((pushInterior K P hcol).p b / (pushInterior K Q hcol).p b) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_mul]
    _ = ∑ b, ∑ a, Q.p a * K.T a b * f (P.p a / Q.p a) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases hK : K.T a b = 0
          · simp [hK]
          · have hKpos : 0 < K.T a b := lt_of_le_of_ne (K.nonneg a b) (Ne.symm hK)
            rw [hlr a b hKpos]
    _ = ∑ a, ∑ b, (Q.p a * f (P.p a / Q.p a)) * K.T a b := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro b _
          ring
    _ = ∑ a, (Q.p a * f (P.p a / Q.p a)) * ∑ b, K.T a b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← Finset.mul_sum]
    _ = ∑ a, Q.p a * f (P.p a / Q.p a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [K.sum_one a, mul_one]

/-- Isometric preservation of every Amari `α`-divergence under a sufficient Markov kernel
(whenever KL is preserved between `P` and `Q`). -/
theorem amariAlphaDivergence_preserved_of_kl_sufficient
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (K : MarkovKernel α β) (hcol : ColNondegenerate K) (P Q : ProbInterior α)
    (αParam : ℝ)
    (heq : ArakiDonald.relativeEntropy (pushInterior K P hcol).p (pushInterior K Q hcol).p =
      ArakiDonald.relativeEntropy P.p Q.p) :
    amariAlphaDivergence αParam (pushInterior K P hcol).p (pushInterior K Q hcol).p =
      amariAlphaDivergence αParam P.p Q.p := by
  rw [← csiszarFDivergence_amariAlphaGenerator_eq αParam (pushInterior K P hcol)
        (pushInterior K Q hcol),
      ← csiszarFDivergence_amariAlphaGenerator_eq αParam P Q]
  exact csiszarFDivergence_preserved_of_kl_sufficient K hcol P Q
    (amariAlphaGenerator αParam) heq

end InfoGeometry.Categorical.MarkovComonoidAndBlackwellSufficiency

end section
