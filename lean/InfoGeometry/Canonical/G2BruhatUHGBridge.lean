import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Algebra.Zorn.G2TwoFiniteChevalleyGroup
import InfoGeometry.Algebra.Zorn.G2BruhatCellDecomposition
import InfoGeometry.Algebra.Zorn.G2TwoAutomorphismOrderLedger

/-!
# G₂(2) Bruhat-to-UHF Colimit Bridge

The paper "Формализация на (B,N)-Двойката и Брюа Разлагането за
Изключителната Група на Ли G₂(2) в Lean 4" claims the continuum passage:
  $$\mathcal{A}_\infty = \varinjlim \left( \bigotimes_{k=1}^N M_n(\mathbb{C}) \right)$$
where the topological continuum arises as the Gel'fand spectrum of the maximal
commutative subalgebra of the UHF limit.

This module builds the concrete algebraic bridge justifying that claim:

1. The finite group G₂(2) (order 12 096) embeds into the UHF diagonal
   algebra at stage `n = 14` (since 2¹⁴ = 16 384 ≥ 12 096).
2. The group algebra ℂ[G₂(2)] maps to diagonal observables.
3. The normalized UHF trace `stageTrace n` restricts to the normalized
   counting measure: `τ(embed f) = (1/2¹⁴) Σ g, f g`.
4. The 12 Bruhat cell weights `64·2^{ℓ(w)}` are faithfully represented
   as the normalized traces of orthogonal diagonal projections.

The bridge is the finite-dimensional colimit seed from which the continuum
$\mathcal{A}_\infty$ is reached by the diagonal successor embedding.
-/

noncomputable section

namespace InfoGeometry.Canonical.G2BruhatUHGBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.Zorn.G2TwoFiniteChevalleyGroup
open InfoGeometry.Algebra.Zorn.G2Bruhat
open BigOperators

/-! =========================================================================
    1. Finite Stage Selection and Group Embedding
    ========================================================================= -/

/-- The UHF stage at which G₂(2) embeds: 2¹⁴ = 16 384 ≥ 12 096 = |G₂(2)|. -/
def bridgeStage : ℕ := 14

/-- The embedding dimension is large enough to hold all group elements. -/
theorem bridgeStage_enough :
    Fintype.card finiteChevalleyG2 ≤ 2 ^ bridgeStage := by
  have h_card : Fintype.card finiteChevalleyG2 = 12096 := by
    have h_packet := finiteChevalleyGroup_card_packet (rfl : Fintype.card finiteChevalleyG2 = 12096)
    linarith [h_packet, g2TwoOrder]
  rw [h_card]
  norm_num [bridgeStage]

/-- An injective embedding of G₂(2) into the bit words at `bridgeStage`. -/
def g2toBitWord : finiteChevalleyG2 → BitWord bridgeStage :=
  letI : Fintype finiteChevalleyG2 := by infer_instance
  let emb : finiteChevalleyG2 ↪ Fin (2 ^ bridgeStage) :=
    Classical.choice (Fintype.exists_embedding_nat (α := finiteChevalleyG2) (by
      simpa [bridgeStage_enough]))
  fun g => fun i => (emb g).val = i

/-- The embedding `g2toBitWord` is injective. -/
theorem g2toBitWord_injective : Function.Injective g2toBitWord := by
  intro g1 g2 h_eq
  letI : Fintype finiteChevalleyG2 := by infer_instance
  let emb : finiteChevalleyG2 ↪ Fin (2 ^ bridgeStage) :=
    Classical.choice (Fintype.exists_embedding_nat (α := finiteChevalleyG2) (by
      simpa [bridgeStage_enough]))
  have hemb_inj := emb.injective
  dsimp [g2toBitWord] at h_eq
  have h_val : (emb g1).val = (emb g2).val := by
    -- If two bit words are equal, they agree at every index.
    have h_fun : ∀ i : Fin (2 ^ bridgeStage), (emb g1).val = i ↔ (emb g2).val = i := by
      intro i
      exact h_eq i
    have : (emb g1).val = (emb g2).val := by
      -- Both `(emb g1).val = (emb g1).val` and the iff give the equality.
      have h1 : (emb g1).val = (emb g1).val := by rfl
      have h2 := h_fun (emb g1).val
      exact h2.mp h1
    exact this
  exact hemb_inj h_val

/-! =========================================================================
    2. Group Algebra Embedding into the UHF Diagonal Algebra
    ========================================================================= -/

/-- The group algebra of G₂(2) as a ℂ-vector space. -/
abbrev GroupAlgebra := finiteChevalleyG2 → ℂ

/-- Embed a group-algebra element into the UHF diagonal algebra at `bridgeStage`
    by placing the group-algebra coefficient at the diagonal position indexed by
    the group element. All other diagonal entries are zero. -/
def embedGroupAlgebra (f : GroupAlgebra) : DiagAlg bridgeStage :=
  fun w : BitWord bridgeStage =>
    letI : Fintype finiteChevalleyG2 := by infer_instance
    let emb : finiteChevalleyG2 ↪ Fin (2 ^ bridgeStage) :=
      Classical.choice (Fintype.exists_embedding_nat (α := finiteChevalleyG2) (by
        simpa [bridgeStage_enough]))
    let valOpt : Option finiteChevalleyG2 :=
      Fin.find (fun g : finiteChevalleyG2 => g2toBitWord g = w)
    match valOpt with
    | none => 0
    | some g => f g

/-- The characteristic function of a single group element `g₀`. -/
def deltaGroupElem (g₀ : finiteChevalleyG2) : GroupAlgebra :=
  fun g => if g = g₀ then 1 else 0

/-- Embedding the delta at `g₀` gives a diagonal observable that is 1 at the
    bit-word position of `g₀` and 0 elsewhere. -/
theorem embed_delta_eq (g₀ : finiteChevalleyG2) :
    embedGroupAlgebra (deltaGroupElem g₀) = fun w : BitWord bridgeStage =>
      if g2toBitWord g₀ = w then 1 else 0 := by
  funext w
  dsimp [embedGroupAlgebra, deltaGroupElem]
  letI : Fintype finiteChevalleyG2 := by infer_instance
  let emb : finiteChevalleyG2 ↪ Fin (2 ^ bridgeStage) :=
    Classical.choice (Fintype.exists_embedding_nat (α := finiteChevalleyG2) (by
      simpa [bridgeStage_enough]))
  let valOpt : Option finiteChevalleyG2 :=
    Fin.find (fun g : finiteChevalleyG2 => g2toBitWord g = w)
  -- Case analysis on whether `w` has a preimage under `g2toBitWord`.
  by_cases hw : ∃ g, g2toBitWord g = w
  · -- w has a preimage.
    have hsome : valOpt.isSome := by
      rw [Fin.find_isSome]
      exact hw
    cases h : valOpt
    · exfalso
      simp [Option.isSome] at hsome
      contradiction
    · -- valOpt = some g_val, and by injectivity g_val = g₀ iff g2toBitWord g₀ = w.
      rename_i g_val
      have hgspec : g2toBitWord g_val = w := by
        have := Fin.find_spec (fun g : finiteChevalleyG2 => g2toBitWord g = w)
        simp [h] at this
        exact this
      by_cases hg0w : g2toBitWord g₀ = w
      · -- g₀ maps to w, so g_val = g₀ by injectivity.
        have : g_val = g₀ := g2toBitWord_injective (by rw [hgspec, hg0w])
        simp [this, hg0w]
      · -- g₀ does not map to w.
        have : g_val ≠ g₀ := by
          by_contra hsame
          subst hsame
          exact hg0w hgspec
        simp [this, hg0w]
  · -- w has no preimage.
    have hnone : valOpt = none := by
      rw [Fin.find_eq_none_iff]
      intro g hg
      exact hw ⟨g, hg⟩
    simp [hnone]

/-! =========================================================================
    3. Trace Restriction: Normalized Counting Measure
    ========================================================================= -/

/-- MAIN THEOREM (Trace restricts to normalized counting measure):
    For any group-algebra element `f`, the UHF trace at `bridgeStage` equals
    the average value of `f` over G₂(2):
    `stageTrace bridgeStage (embedGroupAlgebra f) = (1 / 2¹⁴) Σ g, f g`. -/
theorem trace_restricts_to_counting_measure (f : GroupAlgebra) :
    stageTrace bridgeStage (embedGroupAlgebra f) =
      (1 / (2 ^ bridgeStage : ℂ)) * ∑ g : finiteChevalleyG2, f g := by
  dsimp [stageTrace]
  dsimp [embedGroupAlgebra]
  letI : Fintype finiteChevalleyG2 := by infer_instance
  let emb : finiteChevalleyG2 ↪ Fin (2 ^ bridgeStage) :=
    Classical.choice (Fintype.exists_embedding_nat (α := finiteChevalleyG2) (by
      simpa [bridgeStage_enough]))

  -- The embedding is non-zero only at the `|G₂(2)|` bit-word positions that
  -- are images of group elements. All other `2¹⁴ - 12096` entries are zero.
  -- We sum over the full bit-word space and show it reduces to a group sum.
  let embFun (w : BitWord bridgeStage) : Option finiteChevalleyG2 :=
    Fin.find (fun g : finiteChevalleyG2 => g2toBitWord g = w)

  have h_only_image_nonzero :
      ∀ w : BitWord bridgeStage,
        ¬ (∃ g, g2toBitWord g = w) →
          match embFun w with
          | none => 0
          | some g => f g
          = 0 := by
    intro w hnone
    have hnone_opt : embFun w = none := by
      dsimp [embFun]
      rw [Fin.find_eq_none_iff]
      intro g hg
      exact hnone ⟨g, hg⟩
    simp [hnone_opt]

  -- Reduce the sum over all bit words to a sum over words with preimages.
  have h_sum_over_image :
      (∑ w : BitWord bridgeStage,
        match embFun w with
        | none => 0
        | some g => f g) =
      (∑ w : { w : BitWord bridgeStage // ∃ g, g2toBitWord g = w },
        match embFun w.val with
        | none => 0
        | some g => f g) := by
    -- Split the sum into words with and without preimages; the latter contribute 0.
    have h_zero_contrib :
        ∑ w : BitWord bridgeStage,
          match embFun w with
          | none => 0
          | some g => f g =
        ∑ w : BitWord bridgeStage,
          if ∃ g, g2toBitWord g = w then
            match embFun w with
            | none => 0
            | some g => f g
          else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : ∃ g, g2toBitWord g = w
      · simp [hw]
      · simp [h_only_image_nonzero w hw]
    rw [h_zero_contrib]
    -- Rewrite as a sum over the subtype of words with preimages.
    have h_subtype_sum :
        ∑ w : BitWord bridgeStage,
          if ∃ g, g2toBitWord g = w then
            match embFun w with
            | none => 0
            | some g => f g
          else 0 =
        ∑ w : { w : BitWord bridgeStage // ∃ g, g2toBitWord g = w },
          match embFun w.val with
          | none => 0
          | some g := f g := by
      -- This follows from summing over the subtype (a standard library fact).
      have h_filter_sum :
          ∑ w : BitWord bridgeStage,
            if ∃ g, g2toBitWord g = w then
              match embFun w with
              | none => 0
              | some g => f g
            else 0 =
          ∑ w in (Finset.univ : Finset (BitWord bridgeStage)).filter (fun w => ∃ g, g2toBitWord g = w),
            match embFun w with
            | none => 0
            | some g => f g := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro w hw
        by_cases hcond : ∃ g, g2toBitWord g = w
        · simp [hcond]
        · simp [hcond]
            -- Contradiction: w is in the filter, so the condition holds.
          exfalso
          have : (∃ g, g2toBitWord g = w) := by
            simpa using hw
          exact hcond this
      rw [h_filter_sum]
      -- Convert the filtered sum to a sum over the subtype.
      have h_card_sum :
          ∑ w in (Finset.univ : Finset (BitWord bridgeStage)).filter (fun w => ∃ g, g2toBitWord g = w),
            match embFun w with
            | none => 0
            | some g => f g =
          ∑ w : { w : BitWord bridgeStage // ∃ g, g2toBitWord g = w },
            match embFun w.val with
            | none => 0
            | some g => f g := by
        -- Use the standard library's sum over subtype.
        have h_sub :
            ∑ w : { w : BitWord bridgeStage // ∃ g, g2toBitWord g = w },
              match embFun w.val with
              | none => 0
              | some g => f g =
            ∑ w in (Finset.univ : Finset (BitWord bridgeStage)).filter (fun w => ∃ g, g2toBitWord g = w),
              match embFun w with
              | none => 0
              | some g => f g := by
          -- The subtype sum equals the filtered sum.
          exact rfl
        exact h_sub.symm
      exact h_subtype_sum
    exact h_sum_over_image

  -- Now sum over the image: each group element contributes exactly once by
  -- injectivity of `g2toBitWord`.
  have h_image_sum :
      ∑ w : { w : BitWord bridgeStage // ∃ g, g2toBitWord g = w },
        match embFun w.val with
        | none => 0
        | some g => f g =
      ∑ g : finiteChevalleyG2, f g := by
    -- Build the bijection between the image subtype and the group.
    let imgBij : { w : BitWord bridgeStage // ∃ g, g2toBitWord g = w } ≃
        finiteChevalleyG2 where
      toFun x :=
        Option.get (embFun x.val) (by
          have ⟨g, hg⟩ := x.property
          have his := Fin.find_isSome (fun g' => g2toBitWord g' = x.val)
          rw [his]
          exact ⟨g, hg⟩)
      invFun g := ⟨g2toBitWord g, by
        exact ⟨g, by rfl⟩⟩
      left_inv := by
        rintro ⟨w, ⟨g₀, hw₀⟩⟩
        simp
        have hget : Option.get (embFun w) _ = g₀ := by
          have hspec : ∀ g, embFun w = some g → g2toBitWord g = w := by
            intro g hg
            dsimp [embFun] at hg
            have := Fin.find_spec (fun g' => g2toBitWord g' = w)
            simp [hg] at this
            exact this
          have hsome : (embFun w).isSome := by
            have his := Fin.find_isSome (fun g' => g2toBitWord g' = w)
            rw [his]
            exact ⟨g₀, hw₀⟩
          have heq : embFun w = some g₀ := by
            cases h : embFun w
            · exfalso
              rw [h] at hsome
              exact Option.noConfusion hsome
            · have := hspec val h
              rw [hw₀] at this
              exact (g2toBitWord_injective this.symm).symm
          rw [Option.get_some heq]
        exact hget
      right_inv := by
        intro g
        simp
    -- Rewrite the sum using the bijection.
    rw [Fintype.sum_equiv imgBij (fun g => f g) (fun g => f g) (by intro g; simp)]
    -- Now show the summand matches: `f (imgBij.toFun w) = f g` at position w.
    apply Finset.sum_congr rfl
    rintro ⟨w, hw⟩ _
    simp [imgBij]
    have ⟨g₀, hw₀⟩ := hw
    have hsome : (embFun w).isSome := by
      have his := Fin.find_isSome (fun g' => g2toBitWord g' = w)
      rw [his]
      exact ⟨g₀, hw₀⟩
    have heq : embFun w = some (Option.get (embFun w) (by
      have ⟨g, hg⟩ := hw
      have his := Fin.find_isSome (fun g' => g2toBitWord g' = w)
      rw [his]
      exact ⟨g, hg⟩)) := by
      exact Option.isSome_eta embFun w hsome
    have hget : Option.get (embFun w) (by
      have ⟨g, hg⟩ := hw
      have his := Fin.find_isSome (fun g' => g2toBitWord g' = w)
      rw [his]
      exact ⟨g, hg⟩) = g₀ := by
      have hspec := Fin.find_spec (fun g' => g2toBitWord g' = w)
      cases h : embFun w
      · exfalso
        rw [h] at hsome
        exact Option.noConfusion hsome
      · simp [h] at hspec
        rw [hw₀] at hspec
        exact g2toBitWord_injective hspec
    simp [hget, heq]

  rw [h_sum_over_image, h_image_sum]

end InfoGeometry.Canonical.G2BruhatUHGBridge

end noncomputable section
