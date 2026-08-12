import Mathlib
import InfoGeometry.Canonical.CantorCliffordFunctionModel

/-!
# Topology of the symbolic chiral boundary

This owner supplies the first native topological layer for the symbolic
boundary carrier.  The binary arrow alphabet is discrete and the infinite
boundary carries the product topology.  No measure, Cuntz representation, or
spectral-triple claim is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCliffordFunctionModel

open InfoGeometry.Canonical.ChiralLightConeTensorTower

instance : TopologicalSpace CausalArrow := ⊥

instance causalArrowDiscreteTopology : DiscreteTopology CausalArrow := ⟨rfl⟩

instance causalArrowFintype : Fintype CausalArrow :=
  ⟨{ChiralArrow.plus, ChiralArrow.minus}, by
    intro a
    cases a <;> simp⟩

theorem compactSpace_chiralBoundary : CompactSpace ChiralBoundary := by
  infer_instance

theorem isCompact_univ_chiralBoundary :
    IsCompact (Set.univ : Set ChiralBoundary) := by
  exact isCompact_univ

theorem continuous_consBoundary :
    Continuous (fun p : CausalArrow × ChiralBoundary =>
      consBoundary p.1 p.2) := by
  apply continuous_pi
  intro k
  cases k with
  | zero => exact continuous_fst
  | succ k => exact (continuous_apply k).comp continuous_snd

theorem continuous_tailBoundary :
    Continuous tailBoundary := by
  apply continuous_pi
  intro k
  exact continuous_apply (k + 1)

theorem continuous_headBoundary :
    Continuous headBoundary := by
  exact continuous_apply 0

/-- The one-step symbolic boundary decomposition is a homeomorphism. -/
def consBoundaryHomeomorph :
    CausalArrow × ChiralBoundary ≃ₜ ChiralBoundary where
  toEquiv :=
    { toFun := fun p => consBoundary p.1 p.2
      invFun := fun ξ => (headBoundary ξ, tailBoundary ξ)
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro ξ
        exact cons_head_tail ξ }
  continuous_toFun := continuous_consBoundary
  continuous_invFun := continuous_headBoundary.prodMk continuous_tailBoundary

theorem continuous_prefixWordBoundary
    {n : ℕ} (w : CausalWord n) :
    Continuous (prefixWordBoundary w) := by
  apply continuous_pi
  intro k
  by_cases hk : k < n
  · simpa [prefixWordBoundary, hk] using
      (continuous_const : Continuous (fun _ : ChiralBoundary => w ⟨k, hk⟩))
  · simpa [prefixWordBoundary, hk] using
      (continuous_apply (k - n) :
        Continuous (fun ξ : ChiralBoundary => ξ (k - n)))

def prefixReadout {n : ℕ} :
    ChiralBoundary → (Fin n → CausalArrow) :=
  fun ξ k => ξ k.1

theorem continuous_prefixReadout {n : ℕ} :
    Continuous (prefixReadout (n := n)) := by
  apply continuous_pi
  intro k
  exact continuous_apply k.1

theorem prefixCylinder_eq_preimage
    {n : ℕ} (w : CausalWord n) :
    prefixCylinder w =
      prefixReadout ⁻¹' ({w} : Set (Fin n → CausalArrow)) := by
  ext ξ
  constructor
  · intro hξ
    funext k
    exact hξ k
  · intro hξ k
    have h : prefixReadout (n := n) ξ = w := hξ
    exact congrFun h k

theorem isClopen_prefixCylinder
    {n : ℕ} (w : CausalWord n) :
    IsClopen (prefixCylinder w) := by
  rw [prefixCylinder_eq_preimage]
  have hw : IsClopen ({w} : Set (Fin n → CausalArrow)) :=
    ⟨isClosed_discrete _, isOpen_discrete _⟩
  exact ⟨hw.1.preimage (continuous_prefixReadout (n := n)),
    hw.2.preimage (continuous_prefixReadout (n := n))⟩

theorem prefixCylinder_disjoint
    {n : ℕ} {u v : CausalWord n} (h : u ≠ v) :
    Disjoint (prefixCylinder u) (prefixCylinder v) := by
  refine Set.disjoint_left.2 ?_
  intro ξ hu hv
  apply h
  funext k
  exact (hu k).symm.trans (hv k)

theorem prefixCylinder_iUnion_eq_univ (n : ℕ) :
    (⋃ w : CausalWord n, prefixCylinder w) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro ξ
  refine Set.mem_iUnion.2 ⟨prefixReadout (n := n) ξ, ?_⟩
  rw [prefixCylinder_eq_preimage]
  exact Set.mem_preimage.mpr (Set.mem_singleton _)

theorem prefixCylinder_nonempty
    {n : ℕ} (w : CausalWord n) :
    (prefixCylinder w).Nonempty := by
  exact ⟨CausalWord.toBoundary w ChiralArrow.plus,
    toBoundary_mem_prefixCylinder w ChiralArrow.plus⟩

theorem mem_prefixCylinder_iff_prefixReadout_eq
    {n : ℕ} (w : CausalWord n) (ξ : ChiralBoundary) :
    ξ ∈ prefixCylinder w ↔ prefixReadout (n := n) ξ = w := by
  rw [prefixCylinder_eq_preimage]
  rfl

theorem prefixReadout_surjective (n : ℕ) :
    Function.Surjective (prefixReadout (n := n)) := by
  intro w
  refine ⟨CausalWord.toBoundary w ChiralArrow.plus, ?_⟩
  exact (mem_prefixCylinder_iff_prefixReadout_eq w
    (CausalWord.toBoundary w ChiralArrow.plus)).1
    (toBoundary_mem_prefixCylinder w ChiralArrow.plus)

/-! ### Finite-stage truncation compatibility -/

def truncateCausalWord {n m : ℕ} (h : n ≤ m)
    (w : CausalWord m) : CausalWord n :=
  fun k => w ⟨k.1, lt_of_lt_of_le k.2 h⟩

@[simp] theorem truncateCausalWord_apply {n m : ℕ} (h : n ≤ m)
    (w : CausalWord m) (k : Fin n) :
    truncateCausalWord h w k = w ⟨k.1, lt_of_lt_of_le k.2 h⟩ := rfl

theorem truncateCausalWord_refl {n : ℕ} (w : CausalWord n) :
    truncateCausalWord (le_refl n) w = w := by
  funext k
  rfl

theorem truncateCausalWord_trans {n m l : ℕ}
    (h₁ : n ≤ m) (h₂ : m ≤ l) (w : CausalWord l) :
    truncateCausalWord h₁ (truncateCausalWord h₂ w) =
      truncateCausalWord (le_trans h₁ h₂) w := by
  funext k
  rfl

theorem prefixReadout_truncate {n m : ℕ} (h : n ≤ m)
    (ξ : ChiralBoundary) :
    truncateCausalWord h (prefixReadout (n := m) ξ) =
      prefixReadout (n := n) ξ := by
  funext k
  rfl

theorem prefixCylinder_subset_truncate {n m : ℕ} (h : n ≤ m)
    (w : CausalWord m) :
    prefixCylinder w ⊆ prefixCylinder (truncateCausalWord h w) := by
  intro ξ hξ k
  exact hξ ⟨k.1, lt_of_lt_of_le k.2 h⟩

theorem prefixCylinder_eq_iUnion_truncated {n m : ℕ} (h : n ≤ m)
    (w : CausalWord n) :
    prefixCylinder w =
      ⋃ v : {v : CausalWord m // truncateCausalWord h v = w},
        prefixCylinder v.1 := by
  ext ξ
  constructor
  · intro hξ
    let v : CausalWord m := prefixReadout (n := m) ξ
    have hv : truncateCausalWord h v = w := by
      calc
        truncateCausalWord h v = prefixReadout (n := n) ξ :=
          prefixReadout_truncate h ξ
        _ = w := (mem_prefixCylinder_iff_prefixReadout_eq w ξ).1 hξ
    refine Set.mem_iUnion.2 ⟨⟨v, hv⟩, ?_⟩
    exact (mem_prefixCylinder_iff_prefixReadout_eq v ξ).2 rfl
  · intro hξ
    obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hξ
    have hcoarse : ξ ∈ prefixCylinder (truncateCausalWord h v.1) :=
      prefixCylinder_subset_truncate h v.1 hv
    rw [v.2] at hcoarse
    exact hcoarse

theorem prefixCylinder_separates
    {ξ η : ChiralBoundary} (hne : ξ ≠ η) :
    ∃ n : ℕ,
      ξ ∈ prefixCylinder (prefixReadout (n := n) ξ) ∧
        η ∉ prefixCylinder (prefixReadout (n := n) ξ) := by
  have hex : ∃ k : ℕ, ξ k ≠ η k := by
    by_contra h
    apply hne
    funext k
    by_contra hne'
    exact h ⟨k, hne'⟩
  obtain ⟨k, hk⟩ := hex
  refine ⟨k + 1, ?_, ?_⟩
  · exact (mem_prefixCylinder_iff_prefixReadout_eq
      (prefixReadout (n := k + 1) ξ) ξ).2 rfl
  · intro hmem
    have heq := (mem_prefixCylinder_iff_prefixReadout_eq
      (prefixReadout (n := k + 1) ξ) η).1 hmem
    have hcoord := congrFun heq ⟨k, by omega⟩
    exact hk (by simpa [prefixReadout] using hcoord.symm)

def dropPrefixBoundary (n : ℕ) (ξ : ChiralBoundary) : ChiralBoundary :=
  fun k => ξ (n + k)

theorem continuous_dropPrefixBoundary (n : ℕ) :
    Continuous (dropPrefixBoundary n) := by
  apply continuous_pi
  intro k
  exact continuous_apply (n + k)

theorem dropPrefixBoundary_prefixWordBoundary
    {n : ℕ} (w : CausalWord n) (ξ : ChiralBoundary) :
    dropPrefixBoundary n (prefixWordBoundary w ξ) = ξ := by
  funext k
  exact prefixWordBoundary_tail w ξ k

theorem prefixWordBoundary_dropPrefixBoundary
    {n : ℕ} (w : CausalWord n) {ξ : ChiralBoundary}
    (hξ : ξ ∈ prefixCylinder w) :
    prefixWordBoundary w (dropPrefixBoundary n ξ) = ξ := by
  funext k
  by_cases hk : k < n
  · simpa [prefixWordBoundary, dropPrefixBoundary, hk] using
      (hξ ⟨k, hk⟩).symm
  · have hnk : n ≤ k := by omega
    simp [prefixWordBoundary, dropPrefixBoundary, hk, hnk]

theorem prefixWordBoundary_injective
    {n : ℕ} (w : CausalWord n) :
    Function.Injective (prefixWordBoundary w) := by
  intro ξ η h
  calc
    ξ = dropPrefixBoundary n (prefixWordBoundary w ξ) :=
      (dropPrefixBoundary_prefixWordBoundary w ξ).symm
    _ = dropPrefixBoundary n (prefixWordBoundary w η) := congrArg _ h
    _ = η := dropPrefixBoundary_prefixWordBoundary w η

def prefixWordCylinderHomeomorph
    {n : ℕ} (w : CausalWord n) :
    ChiralBoundary ≃ₜ {ξ : ChiralBoundary // ξ ∈ prefixCylinder w} := by
  let e : ChiralBoundary ≃
      {ξ : ChiralBoundary // ξ ∈ prefixCylinder w} :=
    { toFun := fun ξ => ⟨prefixWordBoundary w ξ,
        prefixWordBoundary_extends_prefix w ξ⟩
      invFun := fun ξ => dropPrefixBoundary n ξ.1
      left_inv := fun ξ => dropPrefixBoundary_prefixWordBoundary w ξ
      right_inv := fun ξ =>
        Subtype.ext (prefixWordBoundary_dropPrefixBoundary w ξ.2) }
  exact
    { toEquiv := e
      continuous_toFun := (continuous_prefixWordBoundary w).subtype_mk
        (fun ξ => prefixWordBoundary_extends_prefix w ξ)
      continuous_invFun :=
        (continuous_dropPrefixBoundary n).comp continuous_subtype_val }

theorem isCompact_prefixCylinder
    {n : ℕ} (w : CausalWord n) :
    IsCompact (prefixCylinder w) := by
  rw [isCompact_iff_compactSpace]
  exact (prefixWordCylinderHomeomorph w).compactSpace

/-- Concatenation of two finite causal words. -/
def appendCausalWord
    {n m : ℕ}
    (u : CausalWord n)
    (v : CausalWord m) :
    CausalWord (n + m) :=
  fun k =>
    if h : k.1 < n then
      u ⟨k.1, h⟩
    else
      v ⟨k.1 - n, by omega⟩

@[simp] theorem prefixWordBoundary_append
    {n m : ℕ}
    (u : CausalWord n)
    (v : CausalWord m)
    (ξ : ChiralBoundary) :
    prefixWordBoundary (appendCausalWord u v) ξ =
      prefixWordBoundary u (prefixWordBoundary v ξ) := by
  funext k
  by_cases hkn : k < n
  · have hknm : k < n + m := by omega
    simp [prefixWordBoundary, appendCausalWord, hkn, hknm]
  · by_cases hknm : k < n + m
    · have hsub : k - n < m := by omega
      simp [prefixWordBoundary, appendCausalWord, hkn, hknm, hsub]
    · have hsub : ¬ k - n < m := by omega
      have harith : k - (n + m) = k - n - m := by omega
      simp [prefixWordBoundary, hkn, hknm, hsub, harith]

theorem prefixWordPullback_comp_append
    {Value : Type*} {n m : ℕ}
    (u : CausalWord n)
    (v : CausalWord m)
    (f : ChiralBoundary → Value) :
    prefixWordPullback u (prefixWordPullback v f) =
      prefixWordPullback (appendCausalWord v u) f := by
  funext ξ
  unfold prefixWordPullback
  rw [prefixWordBoundary_append]

theorem prefixWordBoundary_mem_appendCylinder
    {n m : ℕ} (u : CausalWord n) (v : CausalWord m)
    {ξ : ChiralBoundary} (hξ : ξ ∈ prefixCylinder v) :
    prefixWordBoundary u ξ ∈
      prefixCylinder (appendCausalWord u v) := by
  intro k
  by_cases hk : k < n
  · simp [prefixWordBoundary, appendCausalWord, hk]
  · have hsub : k - n < m := by omega
    simp [prefixWordBoundary, appendCausalWord, hk]
    exact hξ ⟨k - n, hsub⟩

theorem dropPrefixBoundary_mem_appendCylinder
    {n m : ℕ} (u : CausalWord n) (v : CausalWord m)
    {ξ : ChiralBoundary}
    (hξ : ξ ∈ prefixCylinder (appendCausalWord u v)) :
    dropPrefixBoundary n ξ ∈ prefixCylinder v := by
  intro k
  have hnk : n + k < n + m := by omega
  have h := hξ ⟨n + k, hnk⟩
  simpa [dropPrefixBoundary, appendCausalWord] using h

theorem prefixWordBoundary_dropPrefixBoundary_append
    {n m : ℕ} (u : CausalWord n) (v : CausalWord m)
    {ξ : ChiralBoundary}
    (hξ : ξ ∈ prefixCylinder (appendCausalWord u v)) :
    prefixWordBoundary u (dropPrefixBoundary n ξ) = ξ := by
  funext k
  by_cases hk : k < n
  · have hknm : k < n + m := by omega
    simpa [prefixWordBoundary, appendCausalWord, hk] using
      (hξ ⟨k, hknm⟩).symm
  · have hnk : n ≤ k := by omega
    simp [prefixWordBoundary, dropPrefixBoundary, hk, hnk]

noncomputable def prefixWordCylinderTransition
    {n m : ℕ} (u : CausalWord n) (v : CausalWord m) :
    {ξ : ChiralBoundary // ξ ∈ prefixCylinder v} ≃ₜ
      {ξ : ChiralBoundary //
        ξ ∈ prefixCylinder (appendCausalWord u v)} := by
  let e : {ξ : ChiralBoundary // ξ ∈ prefixCylinder v} ≃
      {ξ : ChiralBoundary //
        ξ ∈ prefixCylinder (appendCausalWord u v)} :=
    { toFun := fun ξ => ⟨prefixWordBoundary u ξ.1,
        prefixWordBoundary_mem_appendCylinder u v ξ.2⟩
      invFun := fun ξ => ⟨dropPrefixBoundary n ξ.1,
        dropPrefixBoundary_mem_appendCylinder u v ξ.2⟩
      left_inv := fun ξ => Subtype.ext
        (dropPrefixBoundary_prefixWordBoundary u ξ.1)
      right_inv := fun ξ => Subtype.ext
        (prefixWordBoundary_dropPrefixBoundary_append u v ξ.2) }
  exact
    { toEquiv := e
      continuous_toFun :=
        ((continuous_prefixWordBoundary u).comp continuous_subtype_val).subtype_mk
          (fun ξ => prefixWordBoundary_mem_appendCylinder u v ξ.2)
      continuous_invFun :=
        ((continuous_dropPrefixBoundary n).comp continuous_subtype_val).subtype_mk
          (fun ξ => dropPrefixBoundary_mem_appendCylinder u v ξ.2) }

/-! ## Continuous boundary functions -/

/-- Regular boundary functions with the product-topology domain. -/
abbrev ContinuousBoundaryFunction
  (Value : Type*) [TopologicalSpace Value] :=
  C(ChiralBoundary, Value)

noncomputable def prefixCylinderIndicator
    {n : ℕ} (w : CausalWord n) : ContinuousBoundaryFunction ℝ where
  toFun := (prefixCylinder w).indicator (fun _ => (1 : ℝ))
  continuous_toFun := (isClopen_prefixCylinder w).continuous_indicator continuous_const

@[simp] theorem prefixCylinderIndicator_of_mem
    {n : ℕ} (w : CausalWord n) {ξ : ChiralBoundary}
    (hξ : ξ ∈ prefixCylinder w) :
    prefixCylinderIndicator w ξ = 1 := by
  classical
  change (prefixCylinder w).indicator (fun _ => (1 : ℝ)) ξ = 1
  simp [Set.indicator, hξ]

@[simp] theorem prefixCylinderIndicator_of_not_mem
    {n : ℕ} (w : CausalWord n) {ξ : ChiralBoundary}
    (hξ : ξ ∉ prefixCylinder w) :
    prefixCylinderIndicator w ξ = 0 := by
  classical
  change (prefixCylinder w).indicator (fun _ => (1 : ℝ)) ξ = 0
  simp [Set.indicator, hξ]

theorem prefixCylinderIndicator_idempotent
    {n : ℕ} (w : CausalWord n) :
    prefixCylinderIndicator w * prefixCylinderIndicator w =
      prefixCylinderIndicator w := by
  ext ξ
  by_cases hξ : ξ ∈ prefixCylinder w <;>
    simp [hξ]

theorem prefixCylinderIndicator_ne_zero
    {n : ℕ} (w : CausalWord n) :
    prefixCylinderIndicator w ≠ 0 := by
  intro h
  obtain ⟨ξ, hξ⟩ := prefixCylinder_nonempty w
  have hvalue := congrArg (fun f : ContinuousBoundaryFunction ℝ => f ξ) h
  change prefixCylinderIndicator w ξ = 0 at hvalue
  rw [prefixCylinderIndicator_of_mem w hξ] at hvalue
  norm_num at hvalue

theorem prefixCylinderIndicator_mul_eq_refined
    {n m : ℕ} (h : n ≤ m) (w : CausalWord m) :
    prefixCylinderIndicator (truncateCausalWord h w) *
        prefixCylinderIndicator w =
      prefixCylinderIndicator w := by
  ext ξ
  by_cases hξ : ξ ∈ prefixCylinder w
  · have hcoarse : ξ ∈ prefixCylinder (truncateCausalWord h w) :=
      prefixCylinder_subset_truncate h w hξ
    simp [hξ, hcoarse]
  · simp [hξ]

theorem prefixCylinderIndicator_mul_eq_zero_of_truncate_ne
    {n m : ℕ} (h : n ≤ m) (u : CausalWord n) (v : CausalWord m)
    (hne : truncateCausalWord h v ≠ u) :
    prefixCylinderIndicator u * prefixCylinderIndicator v = 0 := by
  ext ξ
  by_cases hu : ξ ∈ prefixCylinder u
  · by_cases hv : ξ ∈ prefixCylinder v
    · have htrunc : truncateCausalWord h v = u := by
        calc
          truncateCausalWord h v =
              truncateCausalWord h (prefixReadout (n := m) ξ) := by
            rw [(mem_prefixCylinder_iff_prefixReadout_eq v ξ).1 hv]
          _ = prefixReadout (n := n) ξ := prefixReadout_truncate h ξ
          _ = u := (mem_prefixCylinder_iff_prefixReadout_eq u ξ).1 hu
      exact False.elim (hne htrunc)
    · simp [hu, hv]
  · simp [hu]

theorem prefixCylinderIndicator_mul_eq_refined_of_truncate_eq
    {n m : ℕ} (h : n ≤ m) (u : CausalWord n) (v : CausalWord m)
    (heq : truncateCausalWord h v = u) :
    prefixCylinderIndicator u * prefixCylinderIndicator v =
      prefixCylinderIndicator v := by
  rw [← heq]
  exact prefixCylinderIndicator_mul_eq_refined h v

theorem prefixCylinderIndicator_mul_eq_zero_of_ne
    {n : ℕ} {u v : CausalWord n} (h : u ≠ v) :
    prefixCylinderIndicator u * prefixCylinderIndicator v = 0 := by
  ext ξ
  by_cases hu : ξ ∈ prefixCylinder u
  · by_cases hv : ξ ∈ prefixCylinder v
    · exact False.elim (Set.disjoint_left.1
        (prefixCylinder_disjoint h) hu hv)
    · simp [hu, hv]
  · simp [hu]

theorem prefixCylinderIndicator_sum_eq_one (n : ℕ) :
    (∑ w : CausalWord n, prefixCylinderIndicator w) = 1 := by
  classical
  ext ξ
  let w₀ : CausalWord n := prefixReadout (n := n) ξ
  have hmem : ξ ∈ prefixCylinder w₀ := by
    exact (mem_prefixCylinder_iff_prefixReadout_eq w₀ ξ).2 rfl
  simp only [ContinuousMap.sum_apply, ContinuousMap.one_apply]
  rw [Finset.sum_eq_single w₀]
  · exact prefixCylinderIndicator_of_mem w₀ hmem
  · intro w _ hne
    apply prefixCylinderIndicator_of_not_mem
    intro hξ
    apply hne
    simpa [w₀] using
      ((mem_prefixCylinder_iff_prefixReadout_eq w ξ).1 hξ).symm
  · simp

theorem prefixCylinderIndicator_oneStep_partition :
    prefixCylinderIndicator (fun _ : Fin 1 => ChiralArrow.plus) +
        prefixCylinderIndicator (fun _ : Fin 1 => ChiralArrow.minus) =
      1 := by
  ext ξ
  cases h : ξ 0 with
  | plus =>
      have hp : ξ ∈ prefixCylinder (fun _ : Fin 1 => ChiralArrow.plus) := by
        intro k
        fin_cases k
        exact h
      have hm : ξ ∉ prefixCylinder (fun _ : Fin 1 => ChiralArrow.minus) := by
        intro hm
        have hminus := hm ⟨0, by decide⟩
        simpa [h] using hminus
      rw [ContinuousMap.add_apply, ContinuousMap.one_apply,
        prefixCylinderIndicator_of_mem _ hp,
        prefixCylinderIndicator_of_not_mem _ hm]
      norm_num
  | minus =>
      have hp : ξ ∉ prefixCylinder (fun _ : Fin 1 => ChiralArrow.plus) := by
        intro hp
        have hplus := hp ⟨0, by decide⟩
        simpa [h] using hplus
      have hm : ξ ∈ prefixCylinder (fun _ : Fin 1 => ChiralArrow.minus) := by
        intro k
        fin_cases k
        exact h
      rw [ContinuousMap.add_apply, ContinuousMap.one_apply,
        prefixCylinderIndicator_of_not_mem _ hp,
        prefixCylinderIndicator_of_mem _ hm]
      norm_num

theorem prefixCylinderIndicator_oneStep_orthogonal :
    prefixCylinderIndicator (fun _ : Fin 1 => ChiralArrow.plus) *
        prefixCylinderIndicator (fun _ : Fin 1 => ChiralArrow.minus) =
      0 := by
  apply prefixCylinderIndicator_mul_eq_zero_of_ne
  intro h
  have h0 := congrFun h ⟨0, by decide⟩
  cases h0

theorem prefixCylinderIndicator_eq_sum_truncated
    {n m : ℕ} (h : n ≤ m) (w : CausalWord n) :
    prefixCylinderIndicator w =
      ∑ v : {v : CausalWord m // truncateCausalWord h v = w},
        prefixCylinderIndicator v.1 := by
  classical
  ext ξ
  by_cases hξ : ξ ∈ prefixCylinder w
  · let v₀ : CausalWord m := prefixReadout (n := m) ξ
    have htrunc : truncateCausalWord h v₀ = w := by
      calc
        truncateCausalWord h v₀ = prefixReadout (n := n) ξ :=
          prefixReadout_truncate h ξ
        _ = w := (mem_prefixCylinder_iff_prefixReadout_eq w ξ).1 hξ
    let v₀' : {v : CausalWord m // truncateCausalWord h v = w} :=
      ⟨v₀, htrunc⟩
    have hv₀ : ξ ∈ prefixCylinder v₀ := by
      exact (mem_prefixCylinder_iff_prefixReadout_eq v₀ ξ).2 rfl
    simp only [ContinuousMap.sum_apply]
    rw [Finset.sum_eq_single v₀']
    · rw [prefixCylinderIndicator_of_mem w hξ,
        prefixCylinderIndicator_of_mem v₀ hv₀]
    · intro v _ hv
      apply prefixCylinderIndicator_of_not_mem
      intro hvξ
      apply hv
      apply Subtype.ext
      simpa [v₀, v₀'] using
        ((mem_prefixCylinder_iff_prefixReadout_eq v.1 ξ).1 hvξ).symm
    · simp
  · rw [prefixCylinderIndicator_of_not_mem w hξ]
    simp only [ContinuousMap.sum_apply]
    symm
    apply Finset.sum_eq_zero
    intro v _
    apply prefixCylinderIndicator_of_not_mem
    intro hvξ
    have hcoarse := prefixCylinder_subset_truncate h v.1 hvξ
    rw [v.2] at hcoarse
    exact hξ hcoarse

abbrev FiniteCausalWord := Σ n : ℕ, CausalWord n

noncomputable def cylinderFunctionSubalgebra :
    Subalgebra ℝ (ContinuousBoundaryFunction ℝ) :=
  Algebra.adjoin ℝ
    (Set.range (fun w : FiniteCausalWord => prefixCylinderIndicator w.2))

theorem prefixCylinderIndicator_mem_cylinderFunctionSubalgebra
    {n : ℕ} (w : CausalWord n) :
    prefixCylinderIndicator w ∈ cylinderFunctionSubalgebra := by
  exact Algebra.subset_adjoin ⟨⟨n, w⟩, rfl⟩

noncomputable def restrictToCylinderContinuous
    {Value : Type*} [TopologicalSpace Value] [Zero Value]
    {n : ℕ} (w : CausalWord n)
    (f : ContinuousBoundaryFunction Value)
    (hw : IsClopen (prefixCylinder w)) :
    ContinuousBoundaryFunction Value where
  toFun ξ := restrictToCylinder w f ξ
  continuous_toFun := by
    classical
    have hfrontier : frontier (prefixCylinder w) = ∅ :=
      (isClopen_iff_frontier_eq_empty).mp hw
    change Continuous (fun ξ =>
      if ξ ∈ prefixCylinder w then f ξ else 0)
    apply Continuous.if
    · intro ξ hξ
      have hempty : ξ ∈ (∅ : Set ChiralBoundary) := by
        simpa [hfrontier] using hξ
      exact hempty.elim
    · exact f.continuous
    · exact continuous_const

theorem restrictToCylinderContinuous_indicator
    {n m : ℕ} (w : CausalWord n) (v : CausalWord m)
    (hw : IsClopen (prefixCylinder w)) :
    restrictToCylinderContinuous w (prefixCylinderIndicator v) hw =
      prefixCylinderIndicator w * prefixCylinderIndicator v := by
  ext ξ
  classical
  by_cases hξ : ξ ∈ prefixCylinder w
  · simp [restrictToCylinderContinuous, restrictToCylinder, hξ]
  · simp [restrictToCylinderContinuous, restrictToCylinder, hξ]

@[simp] theorem restrictToCylinderContinuous_idem
    {Value : Type*} [TopologicalSpace Value] [Zero Value]
    {n : ℕ} (w : CausalWord n)
    (f : ContinuousBoundaryFunction Value)
    (hw : IsClopen (prefixCylinder w)) :
    restrictToCylinderContinuous w
        (restrictToCylinderContinuous w f hw) hw =
      restrictToCylinderContinuous w f hw := by
  ext ξ
  simpa [restrictToCylinderContinuous] using
    congrFun (restrictToCylinder_idem w f) ξ

@[simp] theorem restrictToCylinderContinuous_add
    {Value : Type*} [TopologicalSpace Value] [AddCommGroup Value]
    [ContinuousAdd Value] {n : ℕ} (w : CausalWord n)
    (f g : ContinuousBoundaryFunction Value)
    (hw : IsClopen (prefixCylinder w)) :
    restrictToCylinderContinuous w (f + g) hw =
      restrictToCylinderContinuous w f hw +
        restrictToCylinderContinuous w g hw := by
  ext ξ
  classical
  by_cases hξ : ξ ∈ prefixCylinder w
  · simp [restrictToCylinderContinuous, restrictToCylinder, hξ]
  · simp [restrictToCylinderContinuous, restrictToCylinder, hξ]

@[simp] theorem restrictToCylinderContinuous_smul
    {K Value : Type*} [TopologicalSpace K] [TopologicalSpace Value]
    [Zero Value] [SMulZeroClass K Value] [ContinuousSMul K Value]
    {n : ℕ} (w : CausalWord n) (c : K)
    (f : ContinuousBoundaryFunction Value)
    (hw : IsClopen (prefixCylinder w)) :
    restrictToCylinderContinuous w (c • f) hw =
      c • restrictToCylinderContinuous w f hw := by
  ext ξ
  classical
  by_cases hξ : ξ ∈ prefixCylinder w
  · simp [restrictToCylinderContinuous, restrictToCylinder, hξ]
  · simp [restrictToCylinderContinuous, restrictToCylinder, hξ]

/-- Continuous pullback along one prefixing arrow. -/
def prefixPullbackContinuous
    {Value : Type*} [TopologicalSpace Value]
    (a : CausalArrow)
    (f : ContinuousBoundaryFunction Value) :
    ContinuousBoundaryFunction Value where
  toFun ξ := f (consBoundary a ξ)
  continuous_toFun := f.continuous.comp
    (continuous_consBoundary.comp (continuous_const.prodMk continuous_id))

/-- Continuous pullback along the tail map. -/
def tailPullbackContinuous
    {Value : Type*} [TopologicalSpace Value]
    (f : ContinuousBoundaryFunction Value) :
    ContinuousBoundaryFunction Value where
  toFun ξ := f (tailBoundary ξ)
  continuous_toFun := f.continuous.comp continuous_tailBoundary

/-- Continuous pullback along a finite-prefix insertion. -/
def prefixWordPullbackContinuous
    {Value : Type*} [TopologicalSpace Value] {n : ℕ}
    (w : CausalWord n)
    (f : ContinuousBoundaryFunction Value) :
    ContinuousBoundaryFunction Value where
  toFun ξ := f (prefixWordBoundary w ξ)
  continuous_toFun := f.continuous.comp (continuous_prefixWordBoundary w)

@[simp]
theorem prefixPullbackContinuous_apply
    {Value : Type*} [TopologicalSpace Value]
    (a : CausalArrow) (f : ContinuousBoundaryFunction Value)
    (ξ : ChiralBoundary) :
    prefixPullbackContinuous a f ξ = f (consBoundary a ξ) := rfl

theorem prefixPullbackContinuous_oneStep_indicator_self
    (a : ChiralArrow) :
    prefixPullbackContinuous a
        (prefixCylinderIndicator (fun _ : Fin 1 => a)) =
      1 := by
  ext ξ
  rw [prefixPullbackContinuous_apply, ContinuousMap.one_apply]
  apply prefixCylinderIndicator_of_mem
  intro k
  fin_cases k
  rfl

theorem prefixPullbackContinuous_oneStep_indicator_flip
    (a : ChiralArrow) :
    prefixPullbackContinuous a
        (prefixCylinderIndicator (fun _ : Fin 1 => ChiralArrow.flip a)) =
      0 := by
  ext ξ
  rw [prefixPullbackContinuous_apply]
  apply prefixCylinderIndicator_of_not_mem
  intro hξ
  have hhead := hξ ⟨0, by decide⟩
  cases a <;> simp [ChiralArrow.flip] at hhead

@[simp]
theorem tailPullbackContinuous_apply
    {Value : Type*} [TopologicalSpace Value]
    (f : ContinuousBoundaryFunction Value) (ξ : ChiralBoundary) :
    tailPullbackContinuous f ξ = f (tailBoundary ξ) := rfl

@[simp] theorem prefixPullbackContinuous_add
    {Value : Type*} [TopologicalSpace Value] [Add Value]
    [ContinuousAdd Value] (a : CausalArrow)
    (f g : ContinuousBoundaryFunction Value) :
    prefixPullbackContinuous a (f + g) =
      prefixPullbackContinuous a f + prefixPullbackContinuous a g := by
  ext ξ
  rfl

@[simp] theorem prefixPullbackContinuous_smul
    {K Value : Type*} [TopologicalSpace K] [TopologicalSpace Value]
    [Zero Value] [SMulZeroClass K Value] [ContinuousSMul K Value]
    (a : CausalArrow) (c : K) (f : ContinuousBoundaryFunction Value) :
    prefixPullbackContinuous a (c • f) =
      c • prefixPullbackContinuous a f := by
  ext ξ
  rfl

@[simp] theorem tailPullbackContinuous_add
    {Value : Type*} [TopologicalSpace Value] [Add Value]
    [ContinuousAdd Value] (f g : ContinuousBoundaryFunction Value) :
    tailPullbackContinuous (f + g) =
      tailPullbackContinuous f + tailPullbackContinuous g := by
  ext ξ
  rfl

@[simp] theorem tailPullbackContinuous_smul
    {K Value : Type*} [TopologicalSpace K] [TopologicalSpace Value]
    [Zero Value] [SMulZeroClass K Value] [ContinuousSMul K Value]
    (c : K) (f : ContinuousBoundaryFunction Value) :
    tailPullbackContinuous (c • f) =
      c • tailPullbackContinuous f := by
  ext ξ
  rfl

@[simp] theorem prefixPullbackContinuous_tailPullbackContinuous
    {Value : Type*} [TopologicalSpace Value]
    (a : CausalArrow)
    (f : ContinuousBoundaryFunction Value) :
    prefixPullbackContinuous a (tailPullbackContinuous f) = f := by
  ext ξ
  simp [prefixPullbackContinuous, tailPullbackContinuous,
    tailBoundary_consBoundary]

@[simp]
theorem prefixWordPullbackContinuous_apply
    {Value : Type*} [TopologicalSpace Value] {n : ℕ}
    (w : CausalWord n) (f : ContinuousBoundaryFunction Value)
    (ξ : ChiralBoundary) :
    prefixWordPullbackContinuous w f ξ = f (prefixWordBoundary w ξ) := rfl

theorem prefixWordBoundary_mem_appendCylinder_iff
    {n m : ℕ} (u : CausalWord n) (v : CausalWord m)
    (ξ : ChiralBoundary) :
    prefixWordBoundary u ξ ∈
        prefixCylinder (appendCausalWord u v) ↔
      ξ ∈ prefixCylinder v := by
  constructor
  · intro hξ k
    have h := hξ ⟨n + k, by omega⟩
    simpa [prefixWordBoundary, appendCausalWord] using h
  · exact prefixWordBoundary_mem_appendCylinder u v

theorem prefixWordPullbackContinuous_cylinderIndicator
    {n m : ℕ} (u : CausalWord n) (v : CausalWord m) :
    prefixWordPullbackContinuous u
        (prefixCylinderIndicator (appendCausalWord u v)) =
      prefixCylinderIndicator v := by
  ext ξ
  by_cases hξ : ξ ∈ prefixCylinder v
  · have happ := (prefixWordBoundary_mem_appendCylinder_iff u v ξ).2 hξ
    rw [prefixWordPullbackContinuous_apply]
    rw [prefixCylinderIndicator_of_mem (appendCausalWord u v) happ]
    rw [prefixCylinderIndicator_of_mem v hξ]
  · have happ : prefixWordBoundary u ξ ∉
        prefixCylinder (appendCausalWord u v) := by
      intro h
      exact hξ ((prefixWordBoundary_mem_appendCylinder_iff u v ξ).1 h)
    rw [prefixWordPullbackContinuous_apply]
    rw [prefixCylinderIndicator_of_not_mem (appendCausalWord u v) happ]
    rw [prefixCylinderIndicator_of_not_mem v hξ]

@[simp] theorem prefixWordPullbackContinuous_add
    {Value : Type*} [TopologicalSpace Value] [Add Value]
    [ContinuousAdd Value] {n : ℕ} (w : CausalWord n)
    (f g : ContinuousBoundaryFunction Value) :
    prefixWordPullbackContinuous w (f + g) =
      prefixWordPullbackContinuous w f +
        prefixWordPullbackContinuous w g := by
  ext ξ
  rfl

@[simp] theorem prefixWordPullbackContinuous_smul
    {K Value : Type*} [TopologicalSpace K] [TopologicalSpace Value]
    [Zero Value] [SMulZeroClass K Value] [ContinuousSMul K Value]
    {n : ℕ} (w : CausalWord n) (c : K)
    (f : ContinuousBoundaryFunction Value) :
    prefixWordPullbackContinuous w (c • f) =
      c • prefixWordPullbackContinuous w f := by
  ext ξ
  rfl

@[simp] theorem prefixWordPullbackContinuous_append
    {Value : Type*} [TopologicalSpace Value]
    {n m : ℕ}
    (u : CausalWord n)
    (v : CausalWord m)
    (f : ContinuousBoundaryFunction Value) :
    prefixWordPullbackContinuous (appendCausalWord u v) f =
      prefixWordPullbackContinuous v
        (prefixWordPullbackContinuous u f) := by
  ext ξ
  simp [prefixWordBoundary_append]

@[simp] theorem canonicalContinuousPrefixBoundaryAction_plus_tail
    {Value : Type*} [TopologicalSpace Value]
    (f : ContinuousBoundaryFunction Value) :
    prefixPullbackContinuous ChiralArrow.plus (tailPullbackContinuous f) = f := by
  exact prefixPullbackContinuous_tailPullbackContinuous ChiralArrow.plus f

@[simp] theorem canonicalContinuousPrefixBoundaryAction_minus_tail
    {Value : Type*} [TopologicalSpace Value]
    (f : ContinuousBoundaryFunction Value) :
    prefixPullbackContinuous ChiralArrow.minus (tailPullbackContinuous f) = f := by
  exact prefixPullbackContinuous_tailPullbackContinuous ChiralArrow.minus f

@[simp] theorem restrictToCylinderContinuous_mul
    {Value : Type*} [TopologicalSpace Value] [MulZeroClass Value]
    [ContinuousMul Value] {n : ℕ} (w : CausalWord n)
    (f g : ContinuousBoundaryFunction Value)
    (hw : IsClopen (prefixCylinder w)) :
    restrictToCylinderContinuous w (f * g) hw =
      restrictToCylinderContinuous w f hw *
        restrictToCylinderContinuous w g hw := by
  ext ξ
  classical
  by_cases hξ : ξ ∈ prefixCylinder w
  · simp [restrictToCylinderContinuous, restrictToCylinder, hξ]
  · simp [restrictToCylinderContinuous, restrictToCylinder, hξ]

@[simp] theorem prefixPullbackContinuous_mul
    {Value : Type*} [TopologicalSpace Value] [Mul Value]
    [ContinuousMul Value] (a : CausalArrow)
    (f g : ContinuousBoundaryFunction Value) :
    prefixPullbackContinuous a (f * g) =
      prefixPullbackContinuous a f * prefixPullbackContinuous a g := by
  ext ξ
  rfl

@[simp] theorem tailPullbackContinuous_mul
    {Value : Type*} [TopologicalSpace Value] [Mul Value]
    [ContinuousMul Value] (f g : ContinuousBoundaryFunction Value) :
    tailPullbackContinuous (f * g) =
      tailPullbackContinuous f * tailPullbackContinuous g := by
  ext ξ
  rfl

@[simp] theorem prefixWordPullbackContinuous_mul
    {Value : Type*} [TopologicalSpace Value] [Mul Value]
    [ContinuousMul Value] {n : ℕ} (w : CausalWord n)
    (f g : ContinuousBoundaryFunction Value) :
    prefixWordPullbackContinuous w (f * g) =
      prefixWordPullbackContinuous w f *
        prefixWordPullbackContinuous w g := by
  ext ξ
  rfl

@[simp] theorem restrictToCylinderContinuous_star
    {Value : Type*} [TopologicalSpace Value] [AddMonoid Value]
    [StarAddMonoid Value] [ContinuousStar Value]
    {n : ℕ} (w : CausalWord n)
    (f : ContinuousBoundaryFunction Value)
    (hw : IsClopen (prefixCylinder w)) :
    restrictToCylinderContinuous w (star f) hw =
      star (restrictToCylinderContinuous w f hw) := by
  ext ξ
  classical
  by_cases hξ : ξ ∈ prefixCylinder w
  · simp [restrictToCylinderContinuous, restrictToCylinder, hξ]
  · simp [restrictToCylinderContinuous, restrictToCylinder, hξ]

@[simp] theorem prefixPullbackContinuous_star
    {Value : Type*} [TopologicalSpace Value] [Star Value]
    [ContinuousStar Value] (a : CausalArrow)
    (f : ContinuousBoundaryFunction Value) :
    prefixPullbackContinuous a (star f) =
      star (prefixPullbackContinuous a f) := by
  ext ξ
  rfl

@[simp] theorem tailPullbackContinuous_star
    {Value : Type*} [TopologicalSpace Value] [Star Value]
    [ContinuousStar Value] (f : ContinuousBoundaryFunction Value) :
    tailPullbackContinuous (star f) =
      star (tailPullbackContinuous f) := by
  ext ξ
  rfl

@[simp] theorem prefixWordPullbackContinuous_star
    {Value : Type*} [TopologicalSpace Value] [Star Value]
    [ContinuousStar Value] {n : ℕ} (w : CausalWord n)
    (f : ContinuousBoundaryFunction Value) :
    prefixWordPullbackContinuous w (star f) =
      star (prefixWordPullbackContinuous w f) := by
  ext ξ
  rfl

end InfoGeometry.Canonical.CantorCliffordFunctionModel
