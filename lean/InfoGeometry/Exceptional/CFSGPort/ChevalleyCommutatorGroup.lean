/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Lean 4.34.1 port of the group layer following
`CFSG.LieType.Chevalley.RootOps.Poly`. It reuses the existing pinned root
subgroups and the checked root-operator-family bridge.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyCommutatorFamily
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootGroups
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootHeightDescent

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

open Chevalley

variable {τ : Tag}

section Field

universe u

variable (K : Type u) [Field K]

@[expose] def familyEltUnit (α : RootCarrier τ) (c : K) :
    (Module.End K (RootModule τ K))ˣ :=
  pinnedX τ K α.1
    ((RootOperatorFamily.pinnedFamilySign (rootOperatorFamilyData.{u} τ) α.1 : K) * c)

theorem coe_familyEltUnit (α : RootCarrier τ) (c : K) :
    (familyEltUnit K α c : Module.End K (RootModule τ K)) =
      (rootOperatorFamilyData.{u} τ).elt K α c := by
  rw [familyEltUnit, pinnedX_eq_rootOperatorFamilyData]
  have hs := RootOperatorFamily.pinnedFamilySign_mul_self
    (rootOperatorFamilyData.{u} τ) K α.1
  change (rootOperatorFamilyData.{u} τ).elt K α
      ((RootOperatorFamily.pinnedFamilySign (rootOperatorFamilyData.{u} τ) α.1 : K) *
        ((RootOperatorFamily.pinnedFamilySign (rootOperatorFamilyData.{u} τ) α.1 : K) * c)) = _
  have harg :
      (RootOperatorFamily.pinnedFamilySign (rootOperatorFamilyData.{u} τ) α.1 : K) *
        ((RootOperatorFamily.pinnedFamilySign (rootOperatorFamilyData.{u} τ) α.1 : K) * c) = c := by
    rw [← mul_assoc, hs, one_mul]
  exact congrArg ((rootOperatorFamilyData.{u} τ).elt K α) harg

theorem familyEltUnit_mem_rootSubgroup (α : RootCarrier τ) (c : K) :
    familyEltUnit K α c ∈ rootSubgroup τ K α.1 := by
  apply mem_rootSubgroup.mpr
  exact ⟨(RootOperatorFamily.pinnedFamilySign (rootOperatorFamilyData.{u} τ) α.1 : K) * c,
    rfl⟩

theorem exists_familyEltUnit_eq (α : RootCarrier τ)
    {x : (Module.End K (RootModule τ K))ˣ} (hx : x ∈ rootSubgroup τ K α.1) :
    ∃ c, familyEltUnit K α c = x := by
  obtain ⟨c₀, hc₀⟩ := mem_rootSubgroup.mp hx
  let ε : K := RootOperatorFamily.pinnedFamilySign (rootOperatorFamilyData.{u} τ) α.1
  have hε : ε * ε = 1 := RootOperatorFamily.pinnedFamilySign_mul_self
    (rootOperatorFamilyData.{u} τ) K α.1
  refine ⟨ε * c₀, ?_⟩
  unfold familyEltUnit
  rw [← show ε =
    (RootOperatorFamily.pinnedFamilySign (rootOperatorFamilyData.{u} τ) α.1 : K) by rfl]
  rw [← mul_assoc, hε, one_mul, hc₀]

theorem weylElt_mul_elt_family (i : Fin τ.rank) (α : RootCarrier τ) (c : K) :
    (weylElt τ K i 1 : Module.End K (RootModule τ K)) *
        (rootOperatorFamilyData.{u} τ).elt K α c =
      (rootOperatorFamilyData.{u} τ).elt K
        ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩
        (((rootOperatorFamilyData.{u} τ).sign i α : K) * c) *
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) := by
  let F := rootOperatorFamilyData.{u} τ
  simp only [RootOperatorFamily.elt, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc
    (weylElt τ K i 1 : Module.End K (RootModule τ K)) *
        (c ^ k • F.D K α k) =
      c ^ k • ((weylElt τ K i 1 : Module.End K (RootModule τ K)) * F.D K α k) := by
        rw [mul_smul_comm]
    _ = c ^ k • (((F.sign i α ^ k : ℤ) : K) •
          (F.D K ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩ k *
            (weylElt τ K i 1 : Module.End K (RootModule τ K)))) := by
        rw [F.conj]
    _ = (c ^ k * ((F.sign i α ^ k : ℤ) : K)) •
          (F.D K ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩ k *
            (weylElt τ K i 1 : Module.End K (RootModule τ K))) := by
        rw [smul_smul]
    _ = (((F.sign i α : K) * c) ^ k •
          F.D K ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩ k) *
          (weylElt τ K i 1 : Module.End K (RootModule τ K)) := by
        rw [← smul_mul_assoc]
        congr 1
        push_cast
        ring_nf

theorem weylElt_mul_elt_mul_inv_family (i : Fin τ.rank) (α : RootCarrier τ) (c : K) :
    (weylElt τ K i 1 : Module.End K (RootModule τ K)) *
        (rootOperatorFamilyData.{u} τ).elt K α c *
        (((weylElt τ K i 1)⁻¹ : (Module.End K (RootModule τ K))ˣ) :
          Module.End K (RootModule τ K)) =
      (rootOperatorFamilyData.{u} τ).elt K
        ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩
        (((rootOperatorFamilyData.{u} τ).sign i α : K) * c) := by
  rw [weylElt_mul_elt_family, Units.mul_inv_cancel_right]

theorem weylElt_conj_familyEltUnit (i : Fin τ.rank) (α : RootCarrier τ) (c : K) :
    weylElt τ K i 1 * familyEltUnit K α c * (weylElt τ K i 1)⁻¹ =
      familyEltUnit K ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩
        (((rootOperatorFamilyData.{u} τ).sign i α : K) * c) := by
  apply Units.ext
  simpa only [Units.val_mul, Units.val_inv, coe_familyEltUnit] using
    weylElt_mul_elt_mul_inv_family (τ := τ) K i α c

theorem map_conj_weylElt_rootSubgroup (i : Fin τ.rank) (α : RootCarrier τ) :
    (rootSubgroup τ K α.1).map (MulAut.conj (weylElt τ K i 1)).toMonoidHom =
      rootSubgroup τ K (reflect τ i α.1) := by
  let F := rootOperatorFamilyData.{u} τ
  let β : RootCarrier τ := ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩
  let εα : K := (F.pinnedFamilySign α.1 : K)
  let εβ : K := (F.pinnedFamilySign β.1 : K)
  let σ : K := (F.sign i α : K)
  let scale : K := εβ * (σ * εα)
  let u : K → K := fun c => scale * c
  have hεα : εα * εα = 1 := F.pinnedFamilySign_mul_self K α.1
  have hεβ : εβ * εβ = 1 := F.pinnedFamilySign_mul_self K β.1
  have hσ : σ * σ = 1 := by
    rcases F.sign_eq i α with h | h <;> simp [σ, h]
  have hscale : scale * scale = 1 := by
    calc
      scale * scale = (εβ * εβ) * (σ * σ) * (εα * εα) := by dsimp [scale]; ring
      _ = 1 := by rw [hεβ, hσ, hεα]; ring
  have hu : Function.Surjective u := by
    intro c
    refine ⟨scale * c, ?_⟩
    dsimp [u]
    rw [← mul_assoc, hscale, one_mul]
  have hleft (c : K) : familyEltUnit K α (εα * c) = pinnedX τ K α.1 c := by
    unfold familyEltUnit
    apply congrArg
    rw [← mul_assoc, hεα, one_mul]
  have hconj (c : K) :
      weylElt τ K i 1 * pinnedX τ K α.1 c * (weylElt τ K i 1)⁻¹ =
        pinnedX τ K β.1 (u c) := by
    calc
      _ = weylElt τ K i 1 * familyEltUnit K α (εα * c) * (weylElt τ K i 1)⁻¹ := by
        rw [hleft c]
      _ = familyEltUnit K β (σ * (εα * c)) := weylElt_conj_familyEltUnit K i α (εα * c)
      _ = pinnedX τ K β.1 (u c) := by
        change pinnedX τ K β.1 (εβ * (σ * (εα * c))) = _
        congr 1
        dsimp [u, scale, εβ, σ, εα]
        ring
  exact Chevalley.map_conj_rootSubgroup (τ := τ) (R := K)
    (α := α.1) (β := β.1) (weylElt τ K i 1) hu hconj

theorem map_conj_weylElt_iSup (i : Fin τ.rank) (P : RootCarrier τ → Prop) :
    (⨆ (γ : RootCarrier τ) (_ : P γ), rootSubgroup τ K γ.1).map
        (MulAut.conj (weylElt τ K i 1)).toMonoidHom =
      ⨆ (γ : RootCarrier τ)
        (_ : P ⟨reflect τ i γ.1, IsRoot.reflect i γ.2⟩), rootSubgroup τ K γ.1 := by
  simp only [Subgroup.map_iSup, map_conj_weylElt_rootSubgroup]
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    have hγ' : P ⟨reflect τ i (reflect τ i γ.1),
        IsRoot.reflect i (IsRoot.reflect i γ.2)⟩ := by
      simpa only [reflect_reflect] using hγ
    exact le_iSup₂_of_le ⟨reflect τ i γ.1, IsRoot.reflect i γ.2⟩ hγ' le_rfl
  · refine iSup₂_le fun γ hγ => ?_
    have hle : rootSubgroup τ K γ.1 ≤
        rootSubgroup τ K (reflect τ i (reflect τ i γ.1)) := by
      rw [reflect_reflect]
    exact le_iSup₂_of_le ⟨reflect τ i γ.1, IsRoot.reflect i γ.2⟩ hγ hle

@[expose] noncomputable def factorsUnit (fs : List Factor) (c d : K) :
    (Module.End K (RootModule τ K))ˣ :=
  (fs.map fun f => if h : f.2.2.1 < τ.rootCertificate.roots.length then
    familyEltUnit K (rootAt τ f.2.2.1 h)
      ((f.2.2.2 : K) * c ^ f.1 * d ^ f.2.1) else 1).prod

theorem coe_factorsUnit (fs : List Factor) (c d : K) :
    (factorsUnit (τ := τ) K fs c d : Module.End K (RootModule τ K)) =
      factorsProd τ K fs c d := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      rw [factorsUnit, List.map_cons, List.prod_cons, ← factorsUnit,
        factorsProd_cons, Units.val_mul]
      split_ifs with h
      · rw [coe_familyEltUnit, ih]
      · simp [ih]

@[expose] def CommContained (α β : RootCarrier τ) : Prop :=
    ∀ x ∈ rootSubgroup τ K α.1, ∀ y ∈ rootSubgroup τ K β.1,
      x * y * x⁻¹ * y⁻¹ ∈
        ⨆ (γ : RootCarrier τ)
          (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
          rootSubgroup τ K γ.1

theorem CommContained.symm {α β : RootCarrier τ}
    (h : CommContained (K := K) α β) : CommContained (K := K) β α := by
  intro y hy x hx
  have hmem := inv_mem (h x hx y hy)
  rw [show (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ by group] at hmem
  have hle :
      (⨆ (γ : RootCarrier τ)
        (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
        rootSubgroup τ K γ.1) ≤
      ⨆ (γ : RootCarrier τ)
        (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • β.1 + b • α.1),
        rootSubgroup τ K γ.1 :=
    biSup_mono fun γ ⟨a, b, ha, hb, hγ⟩ => ⟨b, a, hb, ha, by rw [hγ, add_comm]⟩
  exact hle hmem

theorem commContained_iff {α β : RootCarrier τ} :
    CommContained (K := K) α β ↔ ∀ c d : K,
      familyEltUnit K α c * familyEltUnit K β d *
        (familyEltUnit K α c)⁻¹ * (familyEltUnit K β d)⁻¹ ∈
        ⨆ (γ : RootCarrier τ)
          (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
          rootSubgroup τ K γ.1 := by
  constructor
  · intro h c d
    exact h _ (familyEltUnit_mem_rootSubgroup K α c) _
      (familyEltUnit_mem_rootSubgroup K β d)
  · intro h x hx y hy
    obtain ⟨c, hc⟩ := exists_familyEltUnit_eq K α hx
    obtain ⟨d, hd⟩ := exists_familyEltUnit_eq K β hy
    rw [← hc, ← hd]
    exact h c d

theorem comm_transport (i : Fin τ.rank) {α β : RootCarrier τ}
    (h : CommContained (K := K) α β) :
    CommContained (K := K)
      ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩
      ⟨reflect τ i β.1, IsRoot.reflect i β.2⟩ := by
  intro x hx y hy
  rw [← map_conj_weylElt_rootSubgroup K i α] at hx
  rw [← map_conj_weylElt_rootSubgroup K i β] at hy
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
  let P : RootCarrier τ → Prop := fun γ =>
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj (weylElt τ K i 1)).toMonoidHom
    (h x₀ hx₀ y₀ hy₀)
  rw [map_conj_weylElt_iSup K i P, map_mul, map_mul, map_mul, map_inv, map_inv] at hmem
  have hle :
      (⨆ (γ : RootCarrier τ)
        (_ : P ⟨reflect τ i γ.1, IsRoot.reflect i γ.2⟩), rootSubgroup τ K γ.1) ≤
      ⨆ (γ : RootCarrier τ)
        (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
          γ.1 = a • reflect τ i α.1 + b • reflect τ i β.1), rootSubgroup τ K γ.1 := by
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨a, b, ha, hb, hγ⟩ := hγ
    have hγ' : γ.1 = a • reflect τ i α.1 + b • reflect τ i β.1 := by
      calc
        γ.1 = reflect τ i (reflect τ i γ.1) := (reflect_reflect τ i γ.1).symm
        _ = reflect τ i (a • α.1 + b • β.1) := congrArg (reflect τ i) hγ
        _ = a • reflect τ i α.1 + b • reflect τ i β.1 := by
          rw [← reflectHom_apply, map_add, map_nsmul, map_nsmul,
            reflectHom_apply, reflectHom_apply]
    exact le_iSup₂_of_le γ ⟨a, b, ha, hb, hγ'⟩ le_rfl
  exact hle hmem

@[expose] def walkCarrier (w : List (Fin τ.rank)) (α : RootCarrier τ) : RootCarrier τ :=
  w.foldr (fun i γ => ⟨reflect τ i γ.1, IsRoot.reflect i γ.2⟩) α

theorem walkCarrier_coe (w : List (Fin τ.rank)) (α : RootCarrier τ) :
    (walkCarrier (τ := τ) w α).1 = walkRoot τ w α.1 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [walkCarrier, List.foldr_cons, walkRoot, List.foldr_cons]
    exact congrArg (reflect τ i) ih

theorem comm_transport_list (w : List (Fin τ.rank)) {α β : RootCarrier τ}
    (h : CommContained (K := K) α β) :
    CommContained (K := K) (walkCarrier (τ := τ) w α) (walkCarrier (τ := τ) w β) := by
  induction w with
  | nil => simpa [walkCarrier] using h
  | cons i w ih =>
    simpa only [walkCarrier, List.foldr_cons] using comm_transport K i ih

theorem commContained_of_repCheck (hv : allValid τ = true) {a b : ℕ}
    {fs : List Factor} (h : repCheck τ a b fs = true)
    (α β : RootCarrier τ) (ha : rootPos α = a) (hb : rootPos β = b) :
    CommContained (K := K) α β := by
  have hcone : ∀ f ∈ fs, coneOk τ a b f = true := by
    simp only [repCheck, Bool.and_eq_true, List.all_eq_true] at h
    exact h.1.2
  rw [commContained_iff (K := K)]
  intro c d
  have hop := elt_mul_elt_of_repCheck (R := K) hv h α β ha hb c d
  have hgrp : familyEltUnit K α c * familyEltUnit K β d *
      (familyEltUnit K α c)⁻¹ * (familyEltUnit K β d)⁻¹ =
      factorsUnit (τ := τ) K fs c d := by
    have hmul : familyEltUnit K α c * familyEltUnit K β d =
        factorsUnit (τ := τ) K fs c d * familyEltUnit K β d * familyEltUnit K α c := by
      apply Units.ext
      simp only [Units.val_mul, coe_familyEltUnit, coe_factorsUnit]
      exact hop
    rw [hmul]
    group
  rw [hgrp]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
  have hc := hcone f hf
  simp only [coneOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
  obtain ⟨⟨⟨hg, hp⟩, hq⟩, hv'⟩ := hc
  simp only [hg, ↓reduceDIte]
  refine (le_iSup₂ (f := fun (γ : RootCarrier τ)
    (_ : ∃ a' b' : ℕ, 1 ≤ a' ∧ 1 ≤ b' ∧ γ.1 = a' • α.1 + b' • β.1) =>
      rootSubgroup τ K γ.1) (rootAt τ f.2.2.1 hg)
      ⟨f.1, f.2.1, hp, hq, ?_⟩) (familyEltUnit_mem_rootSubgroup K _ _)
  rw [Mirror.vecBEq_iff] at hv'
  rw [← root_rootPos α, ← root_rootPos β, ha, hb]
  exact hv'

theorem commContained_of_checks (hv : allValid τ = true) (htab : tabCheck τ = true)
    {rs : List (ℕ × ℕ × List Factor)} {cs : List ℕ}
    (hreps : repsCheck τ rs = true) (hcover : coverCheck τ rs cs = true)
    (i : Fin τ.rank) (β : RootCarrier τ) (hβ : 0 < height β.1)
    (hne : β ≠ (⟨Pi.single i 1, IsRoot.basis i⟩ : RootCarrier τ)) :
    CommContained (K := K) ⟨Pi.single i 1, IsRoot.basis i⟩ β := by
  simp only [coverCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    Nat.blt_eq] at hcover
  obtain ⟨hpairs, hwalk⟩ := hcover
  have hmem := mem_neededPairs i β hβ hne
  rw [← hpairs, List.mem_map] at hmem
  obtain ⟨e, he, hpe⟩ := hmem
  obtain ⟨hr, hw⟩ := hwalk e he
  set x := rs.getD (coverRep e) (0, 0, []) with hx
  have hxmem : x ∈ rs := by
    rw [hx, List.getD_eq_getElem _ _ hr]
    exact List.getElem_mem hr
  have hrep : repCheck τ x.1 x.2.1 x.2.2 = true := by
    simp only [repsCheck, List.all_eq_true] at hreps
    exact hreps x hxmem
  have hab : x.1 < τ.rootCertificate.roots.length ∧
      x.2.1 < τ.rootCertificate.roots.length := by
    simp only [repCheck, Bool.and_eq_true, Nat.blt_eq] at hrep
    exact ⟨hrep.1.1.1, hrep.1.1.2⟩
  have hcomm := commContained_of_repCheck K hv hrep (rootAt τ x.1 hab.1)
    (rootAt τ x.2.1 hab.2) (rootPos_rootAt _) (rootPos_rootAt _)
  set w := decodeWord τ 64 (coverWord e)
  have ht := comm_transport_list K w hcomm
  obtain ⟨-, -, h3, h4⟩ := walkPair_root_spec htab w hab.1 hab.2
  have hw' : walkPair τ w (x.1, x.2.1) = ((i : ℕ), rootPos β) := by
    rw [← hpe]
    exact hw
  rw [hw'] at h3 h4
  obtain ⟨-, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  have e1 : walkCarrier (τ := τ) w (rootAt τ x.1 hab.1) =
      (⟨Pi.single i 1, IsRoot.basis i⟩ : RootCarrier τ) := by
    apply Subtype.ext
    rw [walkCarrier_coe]
    exact h3.symm.trans (hb i)
  have e2 : walkCarrier (τ := τ) w (rootAt τ x.2.1 hab.2) = β := by
    apply Subtype.ext
    rw [walkCarrier_coe]
    exact h4.symm.trans (root_rootPos β)
  rwa [e1, e2] at ht

theorem commContained_simpleRoot (i : Fin τ.rank) (β : RootCarrier τ)
    (hβ : 0 < height β.1)
    (hne : β ≠ (⟨Pi.single i 1, IsRoot.basis i⟩ : RootCarrier τ)) :
    CommContained (K := K) ⟨Pi.single i 1, IsRoot.basis i⟩ β :=
  commContained_of_checks K (allValid_tag τ) (tabCheck_tag τ)
    (exceptional_repsCheck τ) (exceptional_coverCheck τ) i β hβ hne

/-- The height induction from `RootOps.CommAll`, specialized to the locally
checked exceptional root certificates and the existing pinned root groups. -/
theorem commContained_pos (α β : RootCarrier τ) (hα : 0 < height α.1)
    (hβ : 0 < height β.1) (hne : α ≠ β) :
    CommContained (K := K) α β := by
  induction h : (height α.1).toNat using Nat.strong_induction_on generalizing α β with
  | _ n ih =>
    by_cases hs : ∃ i, α = (⟨Pi.single i 1, IsRoot.basis i⟩ : RootCarrier τ)
    · obtain ⟨i, rfl⟩ := hs
      exact commContained_simpleRoot K i β hβ (Ne.symm hne)
    push Not at hs
    have hns : ∀ i, α.1 ≠ Pi.single i 1 := by
      intro i hi
      exact hs i (Subtype.ext hi)
    obtain ⟨i, hr, hrpos, hrlt⟩ :=
      exists_reflect_height_lt α.2 hα hns
    let α' : RootCarrier τ := ⟨reflect τ i α.1, hr⟩
    by_cases hb : β = (⟨Pi.single i 1, IsRoot.basis i⟩ : RootCarrier τ)
    · subst β
      exact (commContained_simpleRoot K i α hα hne).symm
    let β' : RootCarrier τ := ⟨reflect τ i β.1, IsRoot.reflect i β.2⟩
    have hβpos : 0 < height β'.1 :=
      height_reflect_pos β.2 hβ (by
        intro hroot
        exact hb (Subtype.ext hroot))
    have hne' : α' ≠ β' := by
      intro heq
      apply hne
      apply Subtype.ext
      have hroots := congrArg Subtype.val heq
      change reflect τ i α.1 = reflect τ i β.1 at hroots
      have hback := congrArg (reflect τ i) hroots
      simpa only [reflect_reflect] using hback
    have hrec := ih (height α'.1).toNat (by
      have hαlt : height α'.1 < height α.1 := by simpa [α'] using hrlt
      omega) α' β' hrpos hβpos hne' rfl
    simpa only [α', β', reflect_reflect] using comm_transport K i hrec

/-- The subgroup commutator of two positive-root groups lies in the sum-root
cone. This is the subgroup-level form of the external `CommAll` conclusion,
on the local pinned root-subgroup carrier. -/
theorem rootSubgroup_commutator_le_positiveCone (α β : RootCarrier τ)
    (hα : 0 < height α.1) (hβ : 0 < height β.1) (hne : α ≠ β) :
    ⁅rootSubgroup τ K α.1, rootSubgroup τ K β.1⁆ ≤
      ⨆ (γ : RootCarrier τ)
        (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
        rootSubgroup τ K γ.1 := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact commContained_pos K α β hα hβ hne x hx y hy

end Field

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

end
