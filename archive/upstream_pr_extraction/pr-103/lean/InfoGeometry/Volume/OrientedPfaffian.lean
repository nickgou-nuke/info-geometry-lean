import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Volume.OrientedPfaffian

open scoped BigOperators

structure PerfectMatching (m : ℕ) where
  partner : Fin (2 * m) → Fin (2 * m)
  involutive : Function.Involutive partner
  fixed_free : ∀ i, partner i ≠ i

noncomputable instance perfectMatchingFintype (m : ℕ) : Fintype (PerfectMatching m) :=
  Fintype.ofInjective (fun M : PerfectMatching m => M.partner) (by
    intro M N h
    cases M with
    | mk f hf hff =>
      cases N with
      | mk g hg hgf => simp_all)

namespace PerfectMatching

variable {m : ℕ}

@[simp] theorem partner_partner (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partner (M.partner i) = i := M.involutive i

@[simp] theorem partner_ne_self (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partner i ≠ i := M.fixed_free i

theorem partner_injective (M : PerfectMatching m) : Function.Injective M.partner :=
  M.involutive.injective

theorem partner_surjective (M : PerfectMatching m) : Function.Surjective M.partner :=
  M.involutive.surjective

/-- The partner involution as the canonical permutation carried by a matching. -/
noncomputable def partnerEquiv (M : PerfectMatching m) : Equiv.Perm (Fin (2 * m)) :=
  Equiv.ofBijective M.partner ⟨M.partner_injective, M.partner_surjective⟩

@[simp] theorem partnerEquiv_apply (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partnerEquiv i = M.partner i :=
  rfl

@[simp] theorem partnerEquiv_sq (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partnerEquiv (M.partnerEquiv i) = i :=
  M.involutive i

theorem partnerEquiv_ne_self (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partnerEquiv i ≠ i :=
  M.fixed_free i

private def pairIndexEquiv (m : ℕ) : Fin 2 × Fin m ≃ Fin (2 * m) :=
  finProdFinEquiv

private def flipPair (m : ℕ) : Fin 2 × Fin m ≃ Fin 2 × Fin m :=
  Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl (Fin m))

private theorem flipPair_involutive (m : ℕ) (p : Fin 2 × Fin m) :
    flipPair m (flipPair m p) = p := by
  rcases p with ⟨slot, k⟩
  fin_cases slot <;> simp [flipPair]

/-- The standard matching pairing the two slots over each `Fin m` index. -/
noncomputable def standardMatching (m : ℕ) : PerfectMatching m where
  partner := (pairIndexEquiv m).conj (flipPair m)
  involutive := by
    intro i
    simp [Equiv.conj_apply, flipPair_involutive]
  fixed_free := by
    intro i h
    have hp : flipPair m ((pairIndexEquiv m).symm i) =
        (pairIndexEquiv m).symm i := by
      apply (pairIndexEquiv m).injective
      simpa using h
    have hs := congrArg Prod.fst hp
    generalize hp : (pairIndexEquiv m).symm i = p at hs
    rcases p with ⟨slot, k⟩
    fin_cases slot <;> simp [flipPair] at hs

@[simp] theorem standardMatching_partner (m : ℕ) (i : Fin (2 * m)) :
    (standardMatching m).partner i =
      pairIndexEquiv m (flipPair m ((pairIndexEquiv m).symm i)) :=
  rfl

/-- Pair-slot symmetries consist of a permutation of the pairs and an
independent flip choice for each pair. -/
abbrev PairSlotSymmetry (m : ℕ) :=
  Equiv.Perm (Fin m) × (Fin m → Fin 2)

theorem pairSlotSymmetry_card (m : ℕ) :
    Fintype.card (PairSlotSymmetry m) = Nat.factorial m * 2 ^ m := by
  simp [PairSlotSymmetry, Fintype.card_perm]

private def pairSlotFlip (e : Fin 2) (i : Fin 2) : Fin 2 :=
  if e = 0 then i else (Equiv.swap 0 1) i

private theorem pairSlotFlip_involutive (e : Fin 2) (i : Fin 2) :
    pairSlotFlip e (pairSlotFlip e i) = i := by
  fin_cases e <;> simp [pairSlotFlip]

/-- The wreath-product action on the ordered pair-slot carrier. -/
noncomputable def pairSlotSymmetryEquiv (g : PairSlotSymmetry m) :
    (Fin 2 × Fin m) ≃ (Fin 2 × Fin m) where
  toFun := fun p => (pairSlotFlip (g.2 p.2) p.1, g.1 p.2)
  invFun := fun p =>
    (pairSlotFlip (g.2 (g.1.symm p.2)) p.1, g.1.symm p.2)
  left_inv := by
    rintro ⟨i, k⟩
    simp only
    rw [Equiv.symm_apply_apply]
    simp [pairSlotFlip_involutive]
  right_inv := by
    rintro ⟨i, k⟩
    simp only
    rw [Equiv.apply_symm_apply]
    simp [pairSlotFlip_involutive]

@[simp] theorem pairSlotSymmetryEquiv_apply
    (g : PairSlotSymmetry m) (p : Fin 2 × Fin m) :
    pairSlotSymmetryEquiv g p =
      (pairSlotFlip (g.2 p.2) p.1, g.1 p.2) :=
  rfl

@[simp] theorem pairSlotSymmetryEquiv_symm_apply
    (g : PairSlotSymmetry m) (p : Fin 2 × Fin m) :
    (pairSlotSymmetryEquiv g).symm p =
      (pairSlotFlip (g.2 (g.1.symm p.2)) p.1, g.1.symm p.2) :=
  rfl

theorem pairSlotSymmetryEquiv_commutes_flipPair
    (g : PairSlotSymmetry m) (p : Fin 2 × Fin m) :
    pairSlotSymmetryEquiv g (flipPair m p) =
      flipPair m (pairSlotSymmetryEquiv g p) := by
  rcases p with ⟨slot, k⟩
  simp only [flipPair, Equiv.prodCongr_apply,
    pairSlotSymmetryEquiv_apply]
  fin_cases slot <;>
    generalize he : g.2 k = e <;>
    fin_cases e <;>
    simp [pairSlotFlip, he]

theorem pairSlotSymmetryEquiv_symm_commutes_flipPair
    (g : PairSlotSymmetry m) (p : Fin 2 × Fin m) :
    (pairSlotSymmetryEquiv g).symm (flipPair m p) =
      flipPair m ((pairSlotSymmetryEquiv g).symm p) := by
  apply (pairSlotSymmetryEquiv g).injective
  rw [Equiv.apply_symm_apply, pairSlotSymmetryEquiv_commutes_flipPair]
  simp [pairSlotFlip_involutive]

def pairBlock (m : ℕ) (p : Fin 2 × Fin m) :
    Finset (Fin 2 × Fin m) := {p, flipPair m p}

theorem flipPair_ne_self (m : ℕ) (p : Fin 2 × Fin m) :
    flipPair m p ≠ p := by
  rcases p with ⟨slot, k⟩
  fin_cases slot <;> simp [flipPair]

@[simp] theorem pairBlock_card (m : ℕ) (p : Fin 2 × Fin m) :
    (pairBlock m p).card = 2 := by
  unfold pairBlock
  rw [Finset.card_insert_of_notMem]
  · simp
  · simpa using Ne.symm (flipPair_ne_self m p)

theorem mem_pairBlock_iff (m : ℕ) (p q : Fin 2 × Fin m) :
    q ∈ pairBlock m p ↔ q = p ∨ q = flipPair m p := by
  simp [pairBlock, eq_comm]

theorem pairSlotSymmetryEquiv_image_pairBlock
    (g : PairSlotSymmetry m) (p : Fin 2 × Fin m) :
    (pairBlock m p).image (pairSlotSymmetryEquiv g) =
      pairBlock m (pairSlotSymmetryEquiv g p) := by
  ext q
  simp only [pairBlock, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (pairSlotSymmetryEquiv_commutes_flipPair g p)
  · intro hq
    rcases hq with rfl | rfl
    · exact ⟨p, Or.inl rfl, rfl⟩
    · exact ⟨flipPair m p, Or.inr rfl,
        pairSlotSymmetryEquiv_commutes_flipPair g p⟩

theorem pairSlotSymmetryEquiv_image_pairBlock_card
    (g : PairSlotSymmetry m) (p : Fin 2 × Fin m) :
    ((pairBlock m p).image (pairSlotSymmetryEquiv g)).card = 2 := by
  rw [Finset.card_image_of_injective _ (pairSlotSymmetryEquiv g).injective]
  exact pairBlock_card m p

/-- Transport the pair-slot action to the canonical `Fin (2 * m)` carrier. -/
noncomputable def pairSlotSymmetryPerm (g : PairSlotSymmetry m) :
    Equiv.Perm (Fin (2 * m)) :=
  ((pairIndexEquiv m).symm.trans (pairSlotSymmetryEquiv g)).trans
    (pairIndexEquiv m)

@[simp] theorem pairSlotSymmetryPerm_apply (g : PairSlotSymmetry m)
    (i : Fin (2 * m)) :
    pairSlotSymmetryPerm g i =
      pairIndexEquiv m (pairSlotSymmetryEquiv g ((pairIndexEquiv m).symm i)) :=
  rfl

@[simp] theorem pairSlotSymmetryPerm_symm_apply (g : PairSlotSymmetry m)
    (i : Fin (2 * m)) :
    (pairSlotSymmetryPerm g).symm i =
      pairIndexEquiv m ((pairSlotSymmetryEquiv g).symm
        ((pairIndexEquiv m).symm i)) :=
  rfl

theorem pairSlotSymmetryPerm_injective :
    Function.Injective (pairSlotSymmetryPerm (m := m)) := by
  rintro ⟨p, e⟩ ⟨q, f⟩ h
  have heq : pairSlotSymmetryEquiv (p, e) =
      pairSlotSymmetryEquiv (q, f) := by
    apply Equiv.ext
    intro z
    have hz := congrArg (pairIndexEquiv m).symm
      (congrArg (fun σ => σ (pairIndexEquiv m z)) h)
    simpa [pairSlotSymmetryPerm] using hz
  have hpq : p = q := by
    apply Equiv.ext
    intro k
    have hz := congrArg Prod.snd (congrArg (fun e => e (0, k)) heq)
    simpa [pairSlotSymmetryEquiv_apply] using hz
  have hef : e = f := by
    funext k
    have hz := congrArg Prod.fst (congrArg (fun e => e (0, k)) heq)
    simp only [pairSlotSymmetryEquiv_apply] at hz
    have hek : e k = 0 ∨ e k = 1 := by omega
    have hfk : f k = 0 ∨ f k = 1 := by omega
    rcases hek with hek | hek <;> rcases hfk with hfk | hfk <;>
      simp [pairSlotFlip, hek, hfk] at hz ⊢
  cases hpq
  cases hef
  rfl

noncomputable def pairSlotSymmetryPermImage (m : ℕ) :
    Finset (Equiv.Perm (Fin (2 * m))) :=
  Finset.univ.image (pairSlotSymmetryPerm (m := m))

theorem pairSlotSymmetryPermImage_card (m : ℕ) :
    (pairSlotSymmetryPermImage m).card = 2 ^ m * Nat.factorial m := by
  rw [pairSlotSymmetryPermImage, Finset.card_image_of_injective _
    pairSlotSymmetryPerm_injective]
  simp [Fintype.card_perm, Nat.mul_comm]

/-- Transport a matching along a permutation of its index set. -/
noncomputable def map (M : PerfectMatching m)
    (σ : Equiv.Perm (Fin (2 * m))) : PerfectMatching m where
  partner := fun i => σ (M.partner (σ.symm i))
  involutive := by
    intro i
    simp [M.partner_partner]
  fixed_free := by
    intro i h
    have h' : M.partner (σ.symm i) = σ.symm i := by
      simpa using congrArg σ.symm h
    exact M.partner_ne_self _ h'

@[simp] theorem map_partner (M : PerfectMatching m)
    (σ : Equiv.Perm (Fin (2 * m))) (i : Fin (2 * m)) :
    (M.map σ).partner i = σ (M.partner (σ.symm i)) :=
  rfl

theorem matching_ext {M N : PerfectMatching m}
    (h : M.partner = N.partner) : M = N := by
  cases M
  cases N
  simp_all

@[simp] theorem map_partnerEquiv (M : PerfectMatching m)
    (σ : Equiv.Perm (Fin (2 * m))) :
    (M.map σ).partnerEquiv = σ * M.partnerEquiv * σ.symm := by
  ext i
  simp [Equiv.Perm.mul_apply]

theorem map_map_trans (M : PerfectMatching m)
    (σ τ : Equiv.Perm (Fin (2 * m))) :
    (M.map σ).map τ = M.map (σ.trans τ) := by
  apply matching_ext
  funext i
  simp [Equiv.trans_apply]

theorem pairSlotSymmetryPerm_preserves_standardMatching
    (g : PairSlotSymmetry m) :
    (standardMatching m).map (pairSlotSymmetryPerm g) =
      standardMatching m := by
  apply matching_ext
  funext i
  unfold PerfectMatching.map standardMatching pairSlotSymmetryPerm
  simp only [Equiv.trans_apply]
  have hcomm := pairSlotSymmetryEquiv_commutes_flipPair g
    ((pairSlotSymmetryEquiv g).symm ((pairIndexEquiv m).symm i))
  simpa [Equiv.conj, pairSlotSymmetryEquiv_symm_apply,
    pairSlotSymmetryPerm, pairSlotFlip_involutive] using
      congrArg (pairIndexEquiv m) hcomm

theorem pairSlotSymmetryPerm_stabilizes_partnerEquiv
    (g : PairSlotSymmetry m) :
    pairSlotSymmetryPerm g * (standardMatching m).partnerEquiv *
        (pairSlotSymmetryPerm g).symm =
      (standardMatching m).partnerEquiv := by
  have h := congrArg PerfectMatching.partnerEquiv
    (pairSlotSymmetryPerm_preserves_standardMatching g)
  simpa only [map_partnerEquiv] using h

/-- The matching represented by a pair-ordered permutation representative. -/
noncomputable def matchingOfPerm (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m))) : PerfectMatching m :=
  (standardMatching m).map σ

@[simp] theorem matchingOfPerm_one (m : ℕ) :
    matchingOfPerm m 1 = standardMatching m := by
  unfold matchingOfPerm
  apply matching_ext
  funext i
  simp

@[simp] theorem matchingOfPerm_partner (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m))) (i : Fin (2 * m)) :
    (matchingOfPerm m σ).partner i =
      σ ((standardMatching m).partner (σ.symm i)) :=
  rfl

theorem matchingOfPerm_pairSlotSymmetry_trans
    (g : PairSlotSymmetry m) (σ : Equiv.Perm (Fin (2 * m))) :
    matchingOfPerm m ((pairSlotSymmetryPerm g).trans σ) =
      matchingOfPerm m σ := by
  unfold matchingOfPerm
  rw [← map_map_trans, pairSlotSymmetryPerm_preserves_standardMatching]

def matchingOfPermFiber (m : ℕ) (M : PerfectMatching m) :
    Set (Equiv.Perm (Fin (2 * m))) :=
  {σ | matchingOfPerm m σ = M}

theorem pairSlotSymmetryPerm_trans_mem_matchingOfPermFiber
    (g : PairSlotSymmetry m) (σ : Equiv.Perm (Fin (2 * m))) :
    (pairSlotSymmetryPerm g).trans σ ∈
      matchingOfPermFiber m (matchingOfPerm m σ) := by
  exact matchingOfPerm_pairSlotSymmetry_trans g σ

noncomputable def pairSlotFiberEmbedding
    (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) :
    PairSlotSymmetry m ↪ matchingOfPermFiber m (matchingOfPerm m σ) where
  toFun g := ⟨(pairSlotSymmetryPerm g).trans σ,
    pairSlotSymmetryPerm_trans_mem_matchingOfPermFiber g σ⟩
  inj' := by
    intro g h
    intro hh
    apply pairSlotSymmetryPerm_injective
    have ht : (pairSlotSymmetryPerm g).trans σ =
        (pairSlotSymmetryPerm h).trans σ := congrArg Subtype.val hh
    have hc := congrArg (fun e => e.trans σ.symm) ht
    simpa [Equiv.trans_assoc] using hc

noncomputable instance matchingOfPermFiber.fintype (m : ℕ)
    (M : PerfectMatching m) : Fintype (matchingOfPermFiber m M) :=
  (Set.toFinite _).fintype

theorem matchingOfPermFiber_card_le
    (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) :
    Fintype.card (matchingOfPermFiber m (matchingOfPerm m σ)) ≥
      2 ^ m * Nat.factorial m := by
  classical
  have hc := Fintype.card_le_of_injective
    (pairSlotFiberEmbedding m σ)
    (pairSlotFiberEmbedding m σ).injective
  simpa [Fintype.card_perm, Nat.mul_comm] using hc

@[simp] theorem matchingOfPerm_partnerEquiv (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m))) :
    (matchingOfPerm m σ).partnerEquiv =
      σ * (standardMatching m).partnerEquiv * σ.symm := by
  exact (standardMatching m).map_partnerEquiv σ

theorem matchingOfPerm_eq_iff_partnerEquiv_eq
    (m : ℕ) (σ τ : Equiv.Perm (Fin (2 * m))) :
    matchingOfPerm m σ = matchingOfPerm m τ ↔
      σ * (standardMatching m).partnerEquiv * σ.symm =
        τ * (standardMatching m).partnerEquiv * τ.symm := by
  constructor
  · intro h
    simpa only [matchingOfPerm_partnerEquiv] using
      congrArg PerfectMatching.partnerEquiv h
  · intro h
    apply matching_ext
    have hp : (matchingOfPerm m σ).partnerEquiv =
        (matchingOfPerm m τ).partnerEquiv := by
      simpa only [matchingOfPerm_partnerEquiv] using h
    exact congrArg Equiv.toFun hp

theorem matchingOfPerm_eq_standard_iff_stabilizes
    (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) :
    matchingOfPerm m σ = standardMatching m ↔
      σ * (standardMatching m).partnerEquiv * σ.symm =
        (standardMatching m).partnerEquiv := by
  simpa only [matchingOfPerm_one] using
    (matchingOfPerm_eq_iff_partnerEquiv_eq m σ (1 : Equiv.Perm (Fin (2 * m))))

theorem stabilizingPerm_maps_partner
    (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (hσ : matchingOfPerm m σ = standardMatching m)
    (i : Fin (2 * m)) :
    σ ((standardMatching m).partner (σ.symm i)) =
      (standardMatching m).partner i := by
  have h := congrArg (fun M : PerfectMatching m => M.partner i) hσ
  simpa using h

def partnerBlock (M : PerfectMatching m) (i : Fin (2 * m)) :
    Finset (Fin (2 * m)) := {i, M.partner i}

@[simp] theorem partnerBlock_card (M : PerfectMatching m)
    (i : Fin (2 * m)) :
    (partnerBlock M i).card = 2 := by
  unfold partnerBlock
  rw [Finset.card_insert_of_notMem]
  · simp
  · simpa using Ne.symm (M.partner_ne_self i)

theorem stabilizingPerm_image_partnerBlock
    (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (hσ : matchingOfPerm m σ = standardMatching m)
    (i : Fin (2 * m)) :
    (partnerBlock (standardMatching m) (σ.symm i)).image σ =
      partnerBlock (standardMatching m) i := by
  ext j
  simp only [partnerBlock, Finset.mem_image, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨k, (rfl | rfl), rfl⟩
    · exact Or.inl (by simp)
    · exact Or.inr (stabilizingPerm_maps_partner m σ hσ i)
  · intro hj
    rcases hj with hj | hj
    · exact ⟨σ.symm i, Or.inl rfl, by simpa [hj]⟩
    · exact ⟨(standardMatching m).partner (σ.symm i), Or.inr rfl,
        by simpa [hj] using stabilizingPerm_maps_partner m σ hσ i⟩

def stabilizingPairIndexMap
    (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) : Fin m → Fin m :=
  fun k => ((pairIndexEquiv m).symm
    (σ (pairIndexEquiv m (0, k)))).2

@[simp] theorem stabilizingPairIndexMap_apply
    (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) (k : Fin m) :
    stabilizingPairIndexMap m σ k =
      ((pairIndexEquiv m).symm
        (σ (pairIndexEquiv m (0, k)))).2 :=
  rfl

theorem stabilizingPairIndexMap_pairSlotSymmetryPerm
    (g : PairSlotSymmetry m) (k : Fin m) :
    stabilizingPairIndexMap m (pairSlotSymmetryPerm g) k = g.1 k := by
  simp [stabilizingPairIndexMap, pairSlotSymmetryPerm,
    pairSlotSymmetryEquiv_apply]

def stabilizingPairFlipMap
    (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) : Fin m → Fin 2 :=
  fun k => ((pairIndexEquiv m).symm
    (σ (pairIndexEquiv m (0, k)))).1

theorem stabilizingPairFlipMap_pairSlotSymmetryPerm
    (g : PairSlotSymmetry m) (k : Fin m) :
    stabilizingPairFlipMap m (pairSlotSymmetryPerm g) k = g.2 k := by
  have h0 : g.2 k = 0 ∨ g.2 k = 1 := by omega
  rcases h0 with h0 | h0 <;>
    simp [stabilizingPairFlipMap, pairSlotSymmetryPerm,
      pairSlotSymmetryEquiv_apply, pairSlotFlip, h0]

def leftEndpoints (M : PerfectMatching m) : Finset (Fin (2 * m)) :=
  Finset.univ.filter fun i => i < M.partner i

def rightEndpoints (M : PerfectMatching m) : Finset (Fin (2 * m)) :=
  Finset.univ.filter fun i => M.partner i < i

@[simp] theorem mem_leftEndpoints (M : PerfectMatching m) (i : Fin (2 * m)) :
    i ∈ M.leftEndpoints ↔ i < M.partner i := by simp [leftEndpoints]

@[simp] theorem mem_rightEndpoints (M : PerfectMatching m) (i : Fin (2 * m)) :
    i ∈ M.rightEndpoints ↔ M.partner i < i := by simp [rightEndpoints]

theorem leftEndpoints_union_rightEndpoints (M : PerfectMatching m) :
    M.leftEndpoints ∪ M.rightEndpoints = Finset.univ := by
  ext i
  simp only [Finset.mem_union, mem_leftEndpoints, mem_rightEndpoints,
    Finset.mem_univ, iff_true]
  exact lt_or_gt_of_ne (Ne.symm (M.partner_ne_self i))

theorem leftEndpoints_disjoint_rightEndpoints (M : PerfectMatching m) :
    Disjoint M.leftEndpoints M.rightEndpoints := by
  refine Finset.disjoint_left.2 ?_
  intro i hi hj
  rw [M.mem_leftEndpoints] at hi
  rw [M.mem_rightEndpoints] at hj
  exact (lt_asymm hi hj)

theorem leftEndpoints_card_eq_rightEndpoints_card (M : PerfectMatching m) :
    M.leftEndpoints.card = M.rightEndpoints.card := by
  refine Finset.card_bij (fun i _ => M.partner i) ?_ ?_ ?_
  · intro i hi
    rw [M.mem_leftEndpoints] at hi
    rw [M.mem_rightEndpoints]
    simpa using hi
  · intro i₁ h₁ i₂ h₂ h
    exact M.partner_injective h
  · intro j hj
    refine ⟨M.partner j, ?_, M.partner_partner j⟩
    rw [M.mem_rightEndpoints] at hj
    rw [M.mem_leftEndpoints]
    simpa using hj

theorem leftEndpoints_card_add_rightEndpoints_card (M : PerfectMatching m) :
    M.leftEndpoints.card + M.rightEndpoints.card = 2 * m := by
  have h := Finset.card_union_of_disjoint (M.leftEndpoints_disjoint_rightEndpoints)
  rw [M.leftEndpoints_union_rightEndpoints] at h
  simpa using h.symm

theorem leftEndpoints_card (M : PerfectMatching m) : M.leftEndpoints.card = m := by
  have hsum := M.leftEndpoints_card_add_rightEndpoints_card
  have heq := M.leftEndpoints_card_eq_rightEndpoints_card
  omega

def matchingWeight
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (M : PerfectMatching m) : ℝ :=
  ∏ i ∈ M.leftEndpoints, A i (M.partner i)

def crossingPairs (M : PerfectMatching m) :
    Finset (Fin (2 * m) × Fin (2 * m)) :=
  (M.leftEndpoints.product M.leftEndpoints).filter fun p =>
    p.1 < p.2 ∧ p.2 < M.partner p.1 ∧ M.partner p.1 < M.partner p.2

def crossingNumber (M : PerfectMatching m) : ℕ := M.crossingPairs.card

def matchingSign (M : PerfectMatching m) : ℝ := (-1 : ℝ) ^ M.crossingNumber

@[simp] theorem matchingSign_sq (M : PerfectMatching m) :
    M.matchingSign ^ 2 = 1 := by
  simp [matchingSign, ← pow_mul]

end PerfectMatching

def orientedPfaffian (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : ℝ :=
  ∑ M : PerfectMatching m, M.matchingSign * M.matchingWeight A

/-- The empty matching gives the unit normalization of the signed expansion. -/
theorem orientedPfaffian_zero_dimension
    (A : Matrix (Fin 0) (Fin 0) ℝ) :
    orientedPfaffian 0 A = 1 := by
  classical
  let emptyMatching : PerfectMatching 0 :=
    { partner := fun i => Fin.elim0 i
      involutive := by intro i; exact Fin.elim0 i
      fixed_free := by intro i; exact Fin.elim0 i }
  have huniq : ∀ M : PerfectMatching 0, M = emptyMatching := by
    intro M
    cases M with
    | mk p hp hf =>
      congr
      funext i
      exact Fin.elim0 i
  letI : Unique (PerfectMatching 0) :=
    { default := emptyMatching
      uniq := huniq }
  rw [orientedPfaffian]
  rw [Fintype.sum_unique]
  change emptyMatching.matchingSign * emptyMatching.matchingWeight A = 1
  have hleft : emptyMatching.leftEndpoints = ∅ := by
    ext i
    exact Fin.elim0 i
  rw [show emptyMatching.matchingSign = 1 by
    simp [PerfectMatching.matchingSign, PerfectMatching.crossingNumber,
      PerfectMatching.crossingPairs, hleft]]
  simp [PerfectMatching.matchingWeight, hleft]

/-- The canonical two-point matching. -/
def twoPointMatching : PerfectMatching 1 where
  partner := ![1, 0]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

theorem twoPointMatching_unique (M : PerfectMatching 1) :
    M = twoPointMatching := by
  cases M with
  | mk p hp hfree =>
    congr
    funext i
    fin_cases i
    · have h := hfree 0
      apply Fin.ext
      change (p 0).val = 1
      have hval : (p 0).val ≠ 0 := by
        intro hz
        apply h
        exact Fin.ext hz
      omega
    · have h := hfree 1
      apply Fin.ext
      change (p 1).val = 0
      have hval : (p 1).val ≠ 1 := by
        intro hz
        apply h
        exact Fin.ext hz
      omega

theorem orientedPfaffian_fin_two (a : ℝ) :
    orientedPfaffian 1 (!![(0 : ℝ), a; -a, 0]) = a := by
  classical
  letI : Unique (PerfectMatching 1) :=
    { default := twoPointMatching
      uniq := twoPointMatching_unique }
  change (∑ M : PerfectMatching 1,
    M.matchingSign * M.matchingWeight (!![(0 : ℝ), a; -a, 0])) = a
  rw [Fintype.sum_unique]
  change twoPointMatching.matchingSign *
      twoPointMatching.matchingWeight (!![(0 : ℝ), a; -a, 0]) = a
  have hleft : twoPointMatching.leftEndpoints = ({0} : Finset (Fin 2)) := by
    ext i
    fin_cases i <;> simp [twoPointMatching, PerfectMatching.leftEndpoints]
  have hcross : twoPointMatching.crossingPairs = ∅ := by
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [twoPointMatching, PerfectMatching.crossingPairs,
        PerfectMatching.leftEndpoints]
  have hsign : twoPointMatching.matchingSign = 1 := by
    simp [PerfectMatching.matchingSign, PerfectMatching.crossingNumber, hcross]
  have hweight : twoPointMatching.matchingWeight
      (!![(0 : ℝ), a; -a, 0]) = a := by
    unfold PerfectMatching.matchingWeight
    rw [hleft]
    simp [twoPointMatching]
  rw [hsign, hweight]
  norm_num

@[simp] theorem orientedPfaffian_eq_matchingSum (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
    orientedPfaffian m A =
      ∑ M : PerfectMatching m, M.matchingSign * M.matchingWeight A := rfl

def IsSkew {m : ℕ}
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : Prop :=
  ∀ i j, A i j = -A j i

theorem IsSkew.diagonal_zero {m : ℕ}
    {A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    (hA : IsSkew A) (i : Fin (2 * m)) : A i i = 0 := by
  have h := hA i i
  linarith

end InfoGeometry.Volume.OrientedPfaffian
