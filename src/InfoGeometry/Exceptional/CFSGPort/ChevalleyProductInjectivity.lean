/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootGroupsTriangular
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootGroups

/-!
The first local operator lemmas for porting the ordered root-product
injectivity field from the external CFSG development.
-/

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

variable {τ : Tag} {R : Type*} [CommRing R]

private local instance instRingEndRootModule (τ : Tag) (R : Type*) [CommRing R] :
    Ring (Module.End R (RootModule τ R)) :=
  Module.End.instRing

/-- An endomorphism raises the grading `φ` by at least `n` when every
nonzero matrix coefficient moves a root-module basis vector by that amount. -/
@[expose] def RaisesBy (φ : (Fin τ.rank → ℤ) →+ ℤ) (n : ℤ)
    (A : Module.End R (RootModule τ R)) : Prop :=
  ∀ a b : Label τ, A (Finsupp.single b 1) a ≠ 0 →
    φ b.latticeWeight + n ≤ φ a.latticeWeight

namespace RaisesBy

variable {φ : (Fin τ.rank → ℤ) →+ ℤ} {m n : ℤ}
  {A B : Module.End R (RootModule τ R)}

theorem zero (n : ℤ) : RaisesBy (R := R) φ n 0 :=
  fun _ _ h => (h rfl).elim

theorem one : RaisesBy (R := R) φ 0 1 := by
  intro a b h
  rw [Module.End.one_apply, Finsupp.single_apply] at h
  split_ifs at h with hab
  · subst hab
    simp
  · exact (h rfl).elim

theorem mono (hA : RaisesBy φ m A) (hnm : n ≤ m) : RaisesBy φ n A := by
  intro a b hab
  have h := hA a b hab
  omega

/-- A coefficient at an exact lattice-weight shift vanishes when that shift
has grading below the operator's raising bound. -/
theorem apply_eq_zero_of_weightShift (hA : RaisesBy φ n A)
    {a b : Label τ} {δ : Fin τ.rank → ℤ}
    (hw : a.latticeWeight = b.latticeWeight + δ) (hδ : φ δ < n) :
    A (Finsupp.single b 1) a = 0 := by
  by_contra hne
  have hbound := hA a b hne
  have hgrade : φ a.latticeWeight = φ b.latticeWeight + φ δ := by
    rw [hw, map_add]
  omega

theorem add (hA : RaisesBy φ n A) (hB : RaisesBy φ n B) :
    RaisesBy φ n (A + B) := by
  intro a b hab
  rw [LinearMap.add_apply, Finsupp.add_apply] at hab
  by_cases h : A (Finsupp.single b 1) a = 0
  · rw [h, zero_add] at hab
    exact hB a b hab
  · exact hA a b h

theorem neg (hA : RaisesBy φ n A) : RaisesBy φ n (-A) := by
  intro a b hab
  apply hA a b
  simpa using hab

theorem sub (hA : RaisesBy φ n A) (hB : RaisesBy φ n B) :
    RaisesBy φ n (A - B) := by
  change ∀ a b : Label τ, (A - B) (Finsupp.single b 1) a ≠ 0 →
    φ b.latticeWeight + n ≤ φ a.latticeWeight
  intro a b hab
  rw [LinearMap.sub_apply, Finsupp.sub_apply] at hab
  by_cases h : A (Finsupp.single b 1) a = 0
  · have hB' : B (Finsupp.single b 1) a ≠ 0 := by
      intro hB'
      simp [h, hB'] at hab
    exact hB a b hB'
  · exact hA a b h

theorem mul (hA : RaisesBy φ m A) (hB : RaisesBy φ n B) :
    RaisesBy φ (m + n) (A * B) := by
  intro a b hab
  rw [Module.End.mul_apply, ← Finsupp.sum_single (B (Finsupp.single b 1)),
    Finsupp.sum, map_sum, Finsupp.finsetSum_apply] at hab
  obtain ⟨c, hc, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc'
  have h₁ := hA a c (right_ne_zero_of_mul hc')
  have h₂ := hB c b (Finsupp.mem_support_iff.mp hc)
  omega

end RaisesBy

/-- A coefficient at an exact lattice-weight shift vanishes when that shift
has grading below the operator's raising bound. -/
theorem apply_eq_zero_of_weightShift (hA : RaisesBy (R := R) φ n A)
    {a b : Label τ} {δ : Fin τ.rank → ℤ}
    (hw : a.latticeWeight = b.latticeWeight + δ) (hδ : φ δ < n) :
    A (Finsupp.single b 1) a = 0 := by
  by_contra hne
  have hbound := hA a b hne
  have hgrade : φ a.latticeWeight = φ b.latticeWeight + φ δ := by
    rw [hw, map_add]
  omega

/-- A positive root operator raises every additive root grading by at least
the grading of its root. This is the local pinned-operator input for the
height-layer parameter-isolation proof. -/
theorem raisesBy_pinnedX_sub_one (φ : (Fin τ.rank → ℤ) →+ ℤ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hφα : 0 < φ α) (c : R) :
    RaisesBy (R := R) φ (φ α)
      ((pinnedX τ R α c : Module.End R (RootModule τ R)) - 1) := by
  intro a b hab
  rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply, sub_ne_zero] at hab
  obtain ⟨k, hk, hw⟩ := pinnedX_weight_shift hα c a b hab
  have hshift : φ a.latticeWeight = φ b.latticeWeight + (k : ℤ) * φ α := by
    rw [hw, map_add, map_nsmul, nsmul_eq_mul]
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hscale : φ α ≤ (k : ℤ) * φ α := by nlinarith
  omega

/-- The weaker nonnegative-degree form needed to control the undifferenced
factors in an ordered product. -/
theorem raisesBy_pinnedX_sub_one_of_nonneg (φ : (Fin τ.rank → ℤ) →+ ℤ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hφα : 0 ≤ φ α) (c : R) :
    RaisesBy (R := R) φ 0
      ((pinnedX τ R α c : Module.End R (RootModule τ R)) - 1) := by
  intro a b hab
  rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply, sub_ne_zero] at hab
  obtain ⟨k, hk, hw⟩ := pinnedX_weight_shift hα c a b hab
  have hshift : φ a.latticeWeight = φ b.latticeWeight + (k : ℤ) * φ α := by
    rw [hw, map_add, map_nsmul, nsmul_eq_mul]
  have hk' : (0 : ℤ) ≤ (k : ℤ) := by omega
  have hscale : 0 ≤ (k : ℤ) * φ α := mul_nonneg hk' hφα
  omega

/-- Every pinned root operator with nonnegative grading has grading degree
zero as an endomorphism; its deviation from identity raises by that root's
grading. -/
theorem raisesBy_pinnedX_of_nonneg (φ : (Fin τ.rank → ℤ) →+ ℤ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hφα : 0 ≤ φ α) (c : R) :
    RaisesBy (R := R) φ 0 (pinnedX τ R α c : Module.End R (RootModule τ R)) := by
  have hdiff := raisesBy_pinnedX_sub_one_of_nonneg (R := R) φ hα hφα c
  have hone := RaisesBy.one (R := R) (φ := φ)
  have hsum := hdiff.add hone
  rw [sub_add_cancel] at hsum
  exact hsum

@[expose] def pinnedXEndProduct (L : List (Fin τ.rank → ℤ))
    (c : (Fin τ.rank → ℤ) → R) : Module.End R (RootModule τ R) :=
  (L.map fun α => (pinnedX τ R α (c α) : Module.End R (RootModule τ R))).prod

/-- The usual root height, packaged as an additive grading for the operator
filtration. -/
@[expose] def heightAddMonoidHom (τ : Tag) : (Fin τ.rank → ℤ) →+ ℤ where
  toFun := height
  map_zero' := by simp [height]
  map_add' := by
    intro v w
    simp [height, Finset.sum_add_distrib]

/-- Ordered products of pinned root operators whose roots have nonnegative
grading raise the grading by zero. -/
theorem raisesBy_pinnedXEndProduct (φ : (Fin τ.rank → ℤ) →+ ℤ)
    (L : List (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → R)
    (hL : ∀ α ∈ L, IsRoot τ α ∧ 0 ≤ φ α) :
    RaisesBy (R := R) φ 0 (pinnedXEndProduct (τ := τ) (R := R) L c) := by
  induction L with
  | nil => simpa [pinnedXEndProduct] using RaisesBy.one (R := R) (φ := φ)
  | cons α L ih =>
    have hα := hL α List.mem_cons_self
    have htail : ∀ β ∈ L, IsRoot τ β ∧ 0 ≤ φ β :=
      fun β hβ => hL β (List.mem_cons_of_mem _ hβ)
    simpa [pinnedXEndProduct] using
      (raisesBy_pinnedX_of_nonneg (R := R) φ hα.1 hα.2 (c α)).mul
        (ih htail)

private theorem mul_sub_one_eq (X P : Module.End R (RootModule τ R)) :
    X * P - 1 = (X - 1) * P + (P - 1) := by
  noncomm_ring

/-- A positive-root product differs from identity only at shifts whose
grading is at least the least root grading in its list. -/
theorem raisesBy_pinnedXEndProduct_sub_one
    (φ : (Fin τ.rank → ℤ) →+ ℤ) (L : List (Fin τ.rank → ℤ))
    (c : (Fin τ.rank → ℤ) → R)
    (hL : ∀ α ∈ L, IsRoot τ α ∧ 1 ≤ φ α) :
    RaisesBy (R := R) φ 1
      (pinnedXEndProduct (τ := τ) (R := R) L c - 1) := by
  induction L with
  | nil => simp [pinnedXEndProduct, RaisesBy.zero]
  | cons α L ih =>
    have hα := hL α List.mem_cons_self
    have htail : ∀ β ∈ L, IsRoot τ β ∧ 1 ≤ φ β :=
      fun β hβ => hL β (List.mem_cons_of_mem _ hβ)
    let X : Module.End R (RootModule τ R) := pinnedX τ R α (c α)
    let P : Module.End R (RootModule τ R) := pinnedXEndProduct (τ := τ) (R := R) L c
    have hX : RaisesBy (R := R) φ 1 (X - 1) := by
      have h := raisesBy_pinnedX_sub_one (R := R) φ hα.1 (by omega) (c α)
      simpa [X] using h.mono (by omega)
    have hP : RaisesBy (R := R) φ 0 P := by
      simpa [P] using raisesBy_pinnedXEndProduct (R := R) φ L c
        (fun β hβ => ⟨(htail β hβ).1, by have hp := (htail β hβ).2; omega⟩)
    change RaisesBy (R := R) φ 1 (X * P - 1)
    rw [mul_sub_one_eq]
    exact hX.mul hP |>.add (ih htail)

private theorem mul_sub_mul_eq (X X' P P' : Module.End R (RootModule τ R)) :
    X * P - X' * P' = X * (P - P') + (X - X') * P' := by
  noncomm_ring

/-- If two parameterized positive-root products agree in every grading below
`s`, then their difference raises the grading by at least `s`. This is the
operator filtration step used by the external ordered-product uniqueness
proof. -/
theorem raisesBy_pinnedXEndProduct_sub
    (φ : (Fin τ.rank → ℤ) →+ ℤ) (s : ℤ)
    (hs : 0 < s)
    (L : List (Fin τ.rank → ℤ)) (c c' : (Fin τ.rank → ℤ) → R)
    (hL : ∀ α ∈ L, IsRoot τ α ∧ 0 ≤ φ α)
    (hmatch : ∀ α ∈ L, φ α < s → c α = c' α) :
    RaisesBy (R := R) φ s
      (pinnedXEndProduct (τ := τ) (R := R) L c -
        pinnedXEndProduct (τ := τ) (R := R) L c') := by
  induction L with
  | nil =>
    simpa [pinnedXEndProduct] using RaisesBy.zero (R := R) (φ := φ) s
  | cons α L ih =>
    have hα := hL α List.mem_cons_self
    have htail : ∀ β ∈ L, IsRoot τ β ∧ 0 ≤ φ β :=
      fun β hβ => hL β (List.mem_cons_of_mem _ hβ)
    have hmatchTail : ∀ β ∈ L, φ β < s → c β = c' β :=
      fun β hβ hβs => hmatch β (List.mem_cons_of_mem _ hβ) hβs
    have htailDiff := ih htail hmatchTail
    have htailZero := raisesBy_pinnedXEndProduct (R := R) φ L c' htail
    let X : Module.End R (RootModule τ R) := pinnedX τ R α (c α)
    let X' : Module.End R (RootModule τ R) := pinnedX τ R α (c' α)
    let P : Module.End R (RootModule τ R) := pinnedXEndProduct (τ := τ) (R := R) L c
    let P' : Module.End R (RootModule τ R) := pinnedXEndProduct (τ := τ) (R := R) L c'
    have hleft : RaisesBy (R := R) φ s (X * (P - P')) := by
      have hX := raisesBy_pinnedX_of_nonneg (R := R) φ hα.1 hα.2 (c α)
      simpa [X, P, P'] using hX.mul htailDiff
    have hright : RaisesBy (R := R) φ s ((X - X') * P') := by
      by_cases hsmall : φ α < s
      · have hparam := hmatch α List.mem_cons_self hsmall
        have hXX : X = X' := by simp [X, X', hparam]
        rw [hXX, sub_self, zero_mul]
        exact RaisesBy.zero (R := R) (φ := φ) s
      · have hsα : s ≤ φ α := le_of_not_gt hsmall
        have hαpos : 0 < φ α := lt_of_lt_of_le hs hsα
        have hXdiff : RaisesBy (R := R) φ (φ α) (X - X') := by
          have h₁ := (raisesBy_pinnedX_sub_one (R := R) φ hα.1 hαpos (c α)).sub
            (raisesBy_pinnedX_sub_one (R := R) φ hα.1 hαpos (c' α))
          simpa [X, X', sub_sub_sub_cancel_right] using h₁
        have hXdiff' := hXdiff.mono hsα
        simpa [P'] using hXdiff'.mul htailZero
    change RaisesBy (R := R) φ s (X * P - X' * P')
    rw [mul_sub_mul_eq]
    exact hleft.add hright

private theorem pinnedCoeff_apply_eq_zero_of_weightShift
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {a b : Label τ}
    (hw : a.latticeWeight = b.latticeWeight + α) {k : ℕ} (hk : k ≠ 1) :
    pinnedCoeff τ R α k (Finsupp.single b 1) a = 0 := by
  by_cases hk0 : k = 0
  · subst k
    have hab : a ≠ b := by
      intro hab
      subst a
      have hcancel : b.latticeWeight + α = b.latticeWeight + 0 := by
        simpa using hw.symm
      have hz : α = 0 := add_left_cancel hcancel
      exact hα.ne_zero hz
    rw [pinnedCoeff_zero]
    simp [Module.End.one_apply, Finsupp.single_apply, hab]
  · have hk2 : 1 ≤ k := by omega
    have hweight := mapsWeights_pinnedCoeff (R := R) hα hk2 a b
    by_contra hne
    have hshift := hweight hne
    have hka : (k : ℤ) • α = α := add_left_cancel (hshift.symm.trans hw)
    have hnot : ¬ ∀ j, α j = 0 := by
      intro h
      apply hα.ne_zero
      ext j
      exact h j
    obtain ⟨j, hj⟩ := not_forall.mp hnot
    have hcoord := congrFun hka j
    simp only [Pi.smul_apply, zsmul_eq_mul] at hcoord
    norm_cast at hcoord
    have hk' : 2 ≤ k := by omega
    have hk'' : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk'
    have hdiff : ((k : ℤ) - 1) * α j = 0 := by nlinarith [hcoord]
    have hfactor : 0 < (k : ℤ) - 1 := by omega
    rcases lt_or_gt_of_ne hj with hjneg | hjpos
    · have hprod := mul_neg_of_pos_of_neg hfactor hjneg
      nlinarith
    · have hprod := mul_pos hfactor hjpos
      nlinarith

/-- At a matrix coefficient with exact root-weight shift `α`, the difference
of two pinned root operators is precisely `(c-c')` times the local root
derivation. Higher divided-power terms cannot contribute to that shift. -/
theorem pinnedX_sub_apply_of_weightShift
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {a b : Label τ}
    (hw : a.latticeWeight = b.latticeWeight + α) (c d : R) :
    ((pinnedX τ R α c : Module.End R (RootModule τ R)) -
        (pinnedX τ R α d : Module.End R (RootModule τ R))) (Finsupp.single b 1) a =
      ((c - d) • pinnedE τ R α) (Finsupp.single b 1) a := by
  simp only [LinearMap.sub_apply, Finsupp.sub_apply, pinnedX_eq_sum,
    LinearMap.sum_apply, Finsupp.finsetSum_apply, LinearMap.smul_apply,
    Finsupp.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  have hterm (k : ℕ) (hk : k ∈ Finset.range 4) (hk1 : k ≠ 1) :
      c ^ k * pinnedCoeff τ R α k (Finsupp.single b 1) a -
        d ^ k * pinnedCoeff τ R α k (Finsupp.single b 1) a = 0 := by
    rw [pinnedCoeff_apply_eq_zero_of_weightShift hα hw hk1]
    simp
  rw [Finset.sum_eq_single 1]
  · rw [pinnedCoeff_one]
    simp only [pow_one, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
    ring
  · intro k hk hk1
    exact hterm k hk hk1
  · simp

/-- A pinned root factor of strictly different root label cannot contribute
to a matrix coefficient at a shift of no greater positive grading. -/
theorem pinnedX_sub_apply_eq_zero_of_weightShift_ne
    {α δ : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (φ : (Fin τ.rank → ℤ) →+ ℤ) (hδ : 0 < φ δ) (hδα : φ δ ≤ φ α)
    (hneq : α ≠ δ) {a b : Label τ}
    (hw : a.latticeWeight = b.latticeWeight + δ) (c d : R) :
    ((pinnedX τ R α c : Module.End R (RootModule τ R)) -
        (pinnedX τ R α d : Module.End R (RootModule τ R)))
        (Finsupp.single b 1) a = 0 := by
  let x := ((pinnedX τ R α c : Module.End R (RootModule τ R)) - 1)
    (Finsupp.single b 1) a
  let y := ((pinnedX τ R α d : Module.End R (RootModule τ R)) - 1)
    (Finsupp.single b 1) a
  have hcoeff : x - y =
      ((pinnedX τ R α c : Module.End R (RootModule τ R)) -
        (pinnedX τ R α d : Module.End R (RootModule τ R)))
        (Finsupp.single b 1) a := by
    simp [x, y, LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply]
  by_contra hne
  have hxy : x - y ≠ 0 := by rw [hcoeff]; exact hne
  have hαpos : 0 < φ α := lt_of_lt_of_le hδ hδα
  have extract (t : R) (ht :
      ((pinnedX τ R α t : Module.End R (RootModule τ R)) - 1)
        (Finsupp.single b 1) a ≠ 0) : α = δ := by
    have ht' : (pinnedX τ R α t : Module.End R (RootModule τ R))
        (Finsupp.single b 1) a ≠ (Finsupp.single b 1 : RootModule τ R) a := by
      apply sub_ne_zero.mp
      simpa only [LinearMap.sub_apply, Module.End.one_apply,
        Finsupp.sub_apply] using ht
    obtain ⟨k, hk, hwk⟩ := pinnedX_weight_shift hα t a b ht'
    have hshift : δ = (k : ℤ) • α :=
      add_left_cancel (hw.symm.trans hwk)
    have hgrade : φ δ = (k : ℤ) * φ α := by
      rw [hshift, map_zsmul, zsmul_eq_mul]
      rfl
    have hkOne : k = 1 := by
      have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
      have hkLe : k ≤ 1 := by nlinarith
      omega
    simpa [hkOne] using hshift.symm
  have hxzero : x = 0 := by
    by_contra hx
    exact hneq (extract c (by simpa [x] using hx))
  have hyzero : y = 0 := by
    by_contra hy
    exact hneq (extract d (by simpa [y] using hy))
  exact hxy (by rw [hxzero, hyzero, sub_self])

/-- The exact-shift coefficient of an ordered pinned-root product difference
is the sum of the matching root-parameter contributions. Distinct roots of
the same or greater grading cannot contribute to that shift. -/
theorem pinnedXEndProduct_sub_apply_of_weightShift
    (φ : (Fin τ.rank → ℤ) →+ ℤ) {δ : Fin τ.rank → ℤ}
    (hδ : IsRoot τ δ) (hδφ : 0 < φ δ)
    (c c' : (Fin τ.rank → ℤ) → R) {a b : Label τ}
    (hw : a.latticeWeight = b.latticeWeight + δ) :
    ∀ L : List (Fin τ.rank → ℤ),
      (∀ α ∈ L, IsRoot τ α ∧ 1 ≤ φ α) →
      (∀ α ∈ L, φ α < φ δ → c α = c' α) →
      (pinnedXEndProduct (τ := τ) (R := R) L c -
          pinnedXEndProduct (τ := τ) (R := R) L c')
          (Finsupp.single b 1) a =
        (L.count δ : R) * (((c δ - c' δ) • pinnedE τ R δ)
          (Finsupp.single b 1) a)
  | [], _, _ => by simp [pinnedXEndProduct]
  | α :: L, hL, hmatch => by
      have hα := hL α List.mem_cons_self
      have htail : ∀ β ∈ L, IsRoot τ β ∧ 1 ≤ φ β :=
        fun β hβ => hL β (List.mem_cons_of_mem _ hβ)
      have hmatchTail : ∀ β ∈ L, φ β < φ δ → c β = c' β :=
        fun β hβ hβδ => hmatch β (List.mem_cons_of_mem _ hβ) hβδ
      have ih := pinnedXEndProduct_sub_apply_of_weightShift φ hδ hδφ c c' hw L
        htail hmatchTail
      let X : Module.End R (RootModule τ R) := pinnedX τ R α (c α)
      let X' : Module.End R (RootModule τ R) := pinnedX τ R α (c' α)
      let P : Module.End R (RootModule τ R) := pinnedXEndProduct (τ := τ) (R := R) L c
      let P' : Module.End R (RootModule τ R) := pinnedXEndProduct (τ := τ) (R := R) L c'
      have ih' : (P - P') (Finsupp.single b 1) a =
          (L.count δ : R) * (((c δ - c' δ) • pinnedE τ R δ)
            (Finsupp.single b 1) a) := by
        simpa [P, P'] using ih
      have hPdiff := raisesBy_pinnedXEndProduct_sub (R := R) φ (φ δ) hδφ L c c'
        (fun β hβ => ⟨(htail β hβ).1, by have hp := (htail β hβ).2; omega⟩) hmatchTail
      have hPprime : RaisesBy (R := R) φ 1 (P' - 1) := by
        simpa [P'] using raisesBy_pinnedXEndProduct_sub_one (R := R) φ L c' htail
      have hXminus : RaisesBy (R := R) φ (φ α) (X - 1) := by
        simpa [X] using raisesBy_pinnedX_sub_one (R := R) φ hα.1 (by omega) (c α)
      have hleft := hXminus.mul (by simpa [P, P'] using hPdiff)
      have hleftzero := hleft.apply_eq_zero_of_weightShift hw (by
        have hαgrade := hα.2
        omega)
      change (X * P - X' * P') (Finsupp.single b 1) a = _
      by_cases hsmall : φ α < φ δ
      · have hparam := hmatch α List.mem_cons_self hsmall
        have hXX : X = X' := by simp [X, X', hparam]
        have hrightzero : ((X - X') * (P' - 1))
            (Finsupp.single b 1) a = 0 := by simp [hXX]
        have hfactorzero : (X - X') (Finsupp.single b 1) a = 0 := by simp [hXX]
        rw [show X * P - X' * P' =
          (P - P') + (X - 1) * (P - P') +
            ((X - X') + (X - X') * (P' - 1)) by noncomm_ring]
        simp only [LinearMap.add_apply, Finsupp.add_apply]
        rw [hleftzero, hrightzero, hfactorzero]
        simp only [zero_add, add_zero]
        have hαδ : α ≠ δ := by
          intro h
          rw [h] at hsmall
          omega
        rw [ih']
        simp [List.count_cons_of_ne hαδ]
      · have hδα : φ δ ≤ φ α := le_of_not_gt hsmall
        have hXdiff : RaisesBy (R := R) φ (φ α) (X - X') := by
          have h₁ := (raisesBy_pinnedX_sub_one (R := R) φ hα.1 (by omega) (c α)).sub
            (raisesBy_pinnedX_sub_one (R := R) φ hα.1 (by omega) (c' α))
          simpa [X, X', sub_sub_sub_cancel_right] using h₁
        have hright := hXdiff.mul hPprime
        have hrightzero := hright.apply_eq_zero_of_weightShift hw (by omega)
        have hfactor : (X - X') (Finsupp.single b 1) a =
            if α = δ then ((c δ - c' δ) • pinnedE τ R δ)
              (Finsupp.single b 1) a else 0 := by
          by_cases hαδ : α = δ
          · subst α
            simp only [↓reduceIte, X, X']
            exact pinnedX_sub_apply_of_weightShift hδ hw (c δ) (c' δ)
          · have hzero := pinnedX_sub_apply_eq_zero_of_weightShift_ne hα.1 φ hδφ
              hδα hαδ hw (c α) (c' α)
            have hzero' : (X - X') (Finsupp.single b 1) a = 0 := by
              simpa [X, X'] using hzero
            have hcoeffzero : X (Finsupp.single b 1) a -
                X' (Finsupp.single b 1) a = 0 := by
              simpa only [LinearMap.sub_apply, Finsupp.sub_apply] using hzero'
            simp [hαδ, hcoeffzero]
        rw [show X * P - X' * P' =
          (P - P') + (X - 1) * (P - P') +
            ((X - X') + (X - X') * (P' - 1)) by noncomm_ring]
        simp only [LinearMap.add_apply, Finsupp.add_apply]
        rw [hleftzero, hrightzero, hfactor]
        simp only [zero_add, add_zero]
        rw [ih']
        by_cases hαδ : α = δ
        · simp [List.count_cons, hαδ]
          ring_nf
        · simp [List.count_cons_of_ne hαδ, hαδ]

/-- Every pinned root derivation has a nonzero matrix coefficient on the
root module over a nontrivial coefficient ring. -/
theorem exists_pinnedE_apply_ne_zero [Nontrivial R] (α : Fin τ.rank → ℤ) :
    ∃ a b : Label τ, pinnedE τ R α (Finsupp.single b 1) a ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hE : pinnedE τ R α = 0 :=
    Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => h a b)
  have h10 : (1 : R) = 0 := by
    exact (smul_pinnedE_injective (τ := τ) (R := R) α) (by simp [hE])
  exact one_ne_zero h10

/-- Parameter uniqueness for ordered pinned-root products on the actual
root-module endomorphism carrier. -/
theorem pinnedXEndProduct_params_injective [Nontrivial R] [NoZeroDivisors R]
    (φ : (Fin τ.rank → ℤ) →+ ℤ) (L : List (Fin τ.rank → ℤ))
    (hnd : L.Nodup)
    (hL : ∀ α ∈ L, IsRoot τ α ∧ 0 < φ α)
    (c c' : (Fin τ.rank → ℤ) → R)
    (heq : pinnedXEndProduct (τ := τ) (R := R) L c =
      pinnedXEndProduct (τ := τ) (R := R) L c') :
    ∀ α ∈ L, c α = c' α := by
  classical
  have hL' : ∀ α ∈ L, IsRoot τ α ∧ 1 ≤ φ α :=
    fun α hα => ⟨(hL α hα).1, by have hp := (hL α hα).2; omega⟩
  have key : ∀ n : ℕ, ∀ α ∈ L, φ α < n → c α = c' α := by
    intro n
    induction n with
    | zero =>
        intro α hα hn
        have := (hL α hα).2
        omega
    | succ n ih =>
        intro α hα hn
        by_cases hlt : φ α < n
        · exact ih α hα hlt
        · obtain ⟨a, b, hab⟩ := exists_pinnedE_apply_ne_zero (τ := τ) (R := R) α
          have hlow : ∀ β ∈ L, φ β < φ α → c β = c' β := by
            intro β hβ hβα
            have hβα' : φ β < n := by
              have hαn : φ α = n := by omega
              omega
            exact ih β hβ hβα'
          have hcoeff := pinnedXEndProduct_sub_apply_of_weightShift φ
            ((hL α hα).1) ((hL α hα).2) c c'
            (a := a) (b := b)
            (hw := by
              have hmaps := mapsWeights_pinnedCoeff (R := R) ((hL α hα).1)
                (show 1 ≤ 1 by omega)
              have hmapsE : MapsWeights (pinnedE τ R α) (· + α) := by
                simpa only [pinnedCoeff_one, one_nsmul] using hmaps
              exact hmapsE a b hab)
            L hL' hlow
          rw [heq, sub_self] at hcoeff
          rw [List.count_eq_one_of_mem hnd hα, Nat.cast_one, one_mul] at hcoeff
          have hmul : (c α - c' α) *
              pinnedE τ R α (Finsupp.single b 1) a = 0 := by
            have hcoeff' := hcoeff.symm
            simpa only [LinearMap.zero_apply, Finsupp.zero_apply, LinearMap.smul_apply,
              Finsupp.smul_apply, smul_eq_mul] using hcoeff'
          have hparam : c α - c' α = 0 := (mul_eq_zero.mp hmul).resolve_right hab
          exact sub_eq_zero.mp hparam
  intro α hα
  exact key ((φ α).toNat + 1) α hα (by
    have hself := Int.self_le_toNat (φ α)
    push_cast
    omega)

/-- Ordered products of elements from distinct pinned root subgroups have
unique root parameters when all listed roots raise one additive grading. -/
@[expose] def ProdInjectiveFor
    (X : (Fin τ.rank → ℤ) → Subgroup (Module.End R (RootModule τ R))ˣ)
    (L : List (Fin τ.rank → ℤ)) : Prop :=
  ∀ f g : (Fin τ.rank → ℤ) → (Module.End R (RootModule τ R))ˣ,
    (∀ α ∈ L, f α ∈ X α) → (∀ α ∈ L, g α ∈ X α) →
    (L.map f).prod = (L.map g).prod → ∀ α ∈ L, f α = g α

private theorem coe_map_prod_units {α : Type*}
    (l : List α) (f : α → (Module.End R (RootModule τ R))ˣ) :
    (((l.map f).prod : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)) =
      (l.map fun a => (f a : Module.End R (RootModule τ R))).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul, ih]

/-- The external CFSG `ProdInjectiveFor` field, ported to the local
endomorphism-unit root subgroups. The local height filtration proves the
parameter uniqueness without requiring the roots to be pre-sorted. -/
theorem rootSubgroup_prodInjectiveFor [Nontrivial R] [NoZeroDivisors R]
    (φ : (Fin τ.rank → ℤ) →+ ℤ) (L : List (Fin τ.rank → ℤ))
    (hnd : L.Nodup)
    (hL : ∀ α ∈ L, IsRoot τ α ∧ 0 < φ α) :
    ProdInjectiveFor (τ := τ) (R := R) (rootSubgroup τ R) L := by
  classical
  intro f g hf hg heq
  have hcf : ∀ α ∈ L, ∃ c : R, pinnedX τ R α c = f α := by
    intro α hα
    exact mem_rootSubgroup.mp (hf α hα)
  have hcg : ∀ α ∈ L, ∃ c : R, pinnedX τ R α c = g α := by
    intro α hα
    exact mem_rootSubgroup.mp (hg α hα)
  let c : (Fin τ.rank → ℤ) → R := fun α =>
    if hα : α ∈ L then Classical.choose (hcf α hα) else 0
  let c' : (Fin τ.rank → ℤ) → R := fun α =>
    if hα : α ∈ L then Classical.choose (hcg α hα) else 0
  have hfc : ∀ α ∈ L, f α = pinnedX τ R α (c α) := by
    intro α hα
    simp only [c, dif_pos hα]
    exact (Classical.choose_spec (hcf α hα)).symm
  have hgc : ∀ α ∈ L, g α = pinnedX τ R α (c' α) := by
    intro α hα
    simp only [c', dif_pos hα]
    exact (Classical.choose_spec (hcg α hα)).symm
  have heqEnd : pinnedXEndProduct (τ := τ) (R := R) L c =
      pinnedXEndProduct (τ := τ) (R := R) L c' := by
    have hval :
        (L.map fun α => (f α : Module.End R (RootModule τ R))).prod =
        (L.map fun α => (g α : Module.End R (RootModule τ R))).prod := by
      calc
        (L.map fun α => (f α : Module.End R (RootModule τ R))).prod =
            (((L.map f).prod : (Module.End R (RootModule τ R))ˣ) :
              Module.End R (RootModule τ R)) := (coe_map_prod_units L f).symm
        _ = (((L.map g).prod : (Module.End R (RootModule τ R))ˣ) :
              Module.End R (RootModule τ R)) := congrArg
                (fun u : (Module.End R (RootModule τ R))ˣ =>
                  (u : Module.End R (RootModule τ R))) heq
        _ = (L.map fun α => (g α : Module.End R (RootModule τ R))).prod :=
              coe_map_prod_units L g
    have hfmap : L.map (fun α => (f α : Module.End R (RootModule τ R))) =
        L.map fun α => (pinnedX τ R α (c α) : Module.End R (RootModule τ R)) := by
      apply List.map_congr_left
      intro α hα
      exact congrArg (fun u : (Module.End R (RootModule τ R))ˣ =>
        (u : Module.End R (RootModule τ R))) (hfc α hα)
    have hgmap : L.map (fun α => (g α : Module.End R (RootModule τ R))) =
        L.map fun α => (pinnedX τ R α (c' α) : Module.End R (RootModule τ R)) := by
      apply List.map_congr_left
      intro α hα
      exact congrArg (fun u : (Module.End R (RootModule τ R))ˣ =>
        (u : Module.End R (RootModule τ R))) (hgc α hα)
    rw [hfmap, hgmap] at hval
    simpa [pinnedXEndProduct] using hval
  have hparams := pinnedXEndProduct_params_injective (τ := τ) (R := R)
    φ L hnd hL c c' heqEnd
  intro α hα
  rw [hfc α hα, hgc α hα, hparams α hα]

/-- The negative-grade form of root-subgroup product injectivity. It is the
operator-carrier counterpart of the external `prodInjective_neg` field. -/
theorem rootSubgroup_prodInjectiveFor_neg [Nontrivial R] [NoZeroDivisors R]
    (φ : (Fin τ.rank → ℤ) →+ ℤ) (L : List (Fin τ.rank → ℤ))
    (hnd : L.Nodup)
    (hL : ∀ α ∈ L, IsRoot τ α ∧ φ α < 0) :
    ProdInjectiveFor (τ := τ) (R := R) (rootSubgroup τ R) L := by
  apply rootSubgroup_prodInjectiveFor (τ := τ) (R := R) (-φ) L hnd
  intro α hα
  exact ⟨(hL α hα).1, by simpa using neg_pos.mpr (hL α hα).2⟩

/-- Height-specialized positive-root product uniqueness, matching the
external `SteinbergExtras.prodInjective_pos` list condition. The local proof
needs no ordering hypothesis on `L`. -/
theorem rootSubgroup_prodInjective_height_pos [Nontrivial R] [NoZeroDivisors R]
    (L : List (Fin τ.rank → ℤ)) (hnd : L.Nodup)
    (hL : ∀ α, α ∈ L ↔ IsRoot τ α ∧ 0 < height α ∧
      ∀ δ, IsRoot τ δ → α ≠ 2 • δ) :
    ProdInjectiveFor (τ := τ) (R := R) (rootSubgroup τ R) L := by
  apply rootSubgroup_prodInjectiveFor (τ := τ) (R := R)
    (heightAddMonoidHom τ) L hnd
  intro α hα
  exact ⟨(hL α).mp hα |>.1, (hL α).mp hα |>.2.1⟩

/-- Height-specialized negative-root product uniqueness, matching the
external `SteinbergExtras.prodInjective_neg` list condition. -/
theorem rootSubgroup_prodInjective_height_neg [Nontrivial R] [NoZeroDivisors R]
    (L : List (Fin τ.rank → ℤ)) (hnd : L.Nodup)
    (hL : ∀ α, α ∈ L ↔ IsRoot τ α ∧ height α < 0 ∧
      ∀ δ, IsRoot τ δ → α ≠ 2 • δ) :
    ProdInjectiveFor (τ := τ) (R := R) (rootSubgroup τ R) L := by
  apply rootSubgroup_prodInjectiveFor_neg (τ := τ) (R := R)
    (heightAddMonoidHom τ) L hnd
  intro α hα
  exact ⟨(hL α).mp hα |>.1, (hL α).mp hα |>.2.1⟩

end InfoGeometry.Exceptional.CFSGPort.Chevalley

end
