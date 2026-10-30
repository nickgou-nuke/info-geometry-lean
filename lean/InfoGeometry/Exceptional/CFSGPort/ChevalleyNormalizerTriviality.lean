/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Local operator-carrier port of the opposite-root normalizer lemma used by
the external exceptional-family simplicity proofs.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyPinnedLemmas
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootGroups
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyWeyl

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

private theorem rootVec_eq_single_normalizer {τ : Tag} {K : Type*} [Field K]
    (β : Fin τ.rank → ℤ) (hβ : IsRoot τ β) :
    rootVec τ K β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 := by
  simp [rootVec, hβ]

private theorem xOp_hVec_normalizer {τ : Tag} {K : Type*} [Field K]
    (i j : Fin τ.rank) (c : K) :
    xOp τ K i c (hVec τ K j) =
      hVec τ K j + (((τ.cartan j i).natAbs : K) * c) • rootVec τ K (Pi.single i 1) := by
  change xOp τ K i c (Finsupp.single (Sum.inl j) 1) = _
  rw [xOp, Finsupp.linearCombination_single, one_smul]

private theorem yOp_hVec_normalizer {τ : Tag} {K : Type*} [Field K]
    (i j : Fin τ.rank) (c : K) :
    yOp τ K i c (hVec τ K j) =
      hVec τ K j + (((τ.cartan j i).natAbs : K) * c) • rootVec τ K (-Pi.single i 1) := by
  change yOp τ K i c (Finsupp.single (Sum.inl j) 1) = _
  rw [yOp, Finsupp.linearCombination_single, one_smul]

private theorem xOp_rootVec_neg_normalizer {τ : Tag} {K : Type*} [Field K]
    (i : Fin τ.rank) (c : K) :
    xOp τ K i c (rootVec τ K (-Pi.single i 1)) =
      rootVec τ K (-Pi.single i 1) + c • hVec τ K i + c ^ 2 • rootVec τ K (Pi.single i 1) := by
  rw [rootVec_eq_single_normalizer _ (isRoot_neg_single τ i), xOp,
    Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

private theorem yOp_rootVec_pos_normalizer {τ : Tag} {K : Type*} [Field K]
    (i : Fin τ.rank) (c : K) :
    yOp τ K i c (rootVec τ K (Pi.single i 1)) =
      rootVec τ K (Pi.single i 1) + c • hVec τ K i + c ^ 2 • rootVec τ K (-Pi.single i 1) := by
  rw [rootVec_eq_single_normalizer _ (isRoot_single τ i), yOp,
    Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single i)).trans (ite_eq_left rfl)

private theorem xOp_rootVec_pos_normalizer {τ : Tag} {K : Type*} [Field K]
    (i : Fin τ.rank) (c : K) :
    xOp τ K i c (rootVec τ K (Pi.single i 1)) = rootVec τ K (Pi.single i 1) := by
  rw [rootVec_eq_single_normalizer _ (isRoot_single τ i), xOp,
    Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

private theorem yOp_rootVec_neg_normalizer {τ : Tag} {K : Type*} [Field K]
    (i : Fin τ.rank) (c : K) :
    yOp τ K i c (rootVec τ K (-Pi.single i 1)) = rootVec τ K (-Pi.single i 1) := by
  rw [rootVec_eq_single_normalizer _ (isRoot_neg_single τ i), yOp,
    Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

private theorem xUnit_yUnit_xUnit_apply_negRoot {τ : Tag} {K : Type*} [Field K]
    (i : Fin τ.rank) (c : K) :
    ((xUnit τ K i c * yUnit τ K i 1 * xUnit τ K i (-c) :
      (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
        (rootVec τ K (-Pi.single i 1)) =
      c ^ 4 • rootVec τ K (Pi.single i 1) +
        (c ^ 3 - c ^ 2) • hVec τ K i + (1 - c) ^ 2 • rootVec τ K (-Pi.single i 1) := by
  simp only [Units.val_mul, Module.End.mul_apply, coe_xUnit, coe_yUnit,
    xOp_rootVec_neg_normalizer, map_add, map_smul,
    yOp_rootVec_neg_normalizer, yOp_hVec_normalizer, yOp_rootVec_pos_normalizer,
    xOp_rootVec_pos_normalizer, xOp_hVec_normalizer, τ.cartan_self]
  norm_num
  module

/-- A positive simple-root operator that normalizes the opposite root
subgroup is the identity. The carrier throughout is the unit group of
endomorphisms of the Chevalley root module. -/
theorem xUnit_eq_one_of_mem_normalizer_negSimpleRoot {τ : Tag} {K : Type*} [Field K]
    (i : Fin τ.rank) (c : K)
    (hn : xUnit τ K i c ∈ Subgroup.normalizer
      (rootSubgroup τ K (-Pi.single i 1) : Set (Module.End K (RootModule τ K))ˣ)) :
    c = 0 := by
  have hconj := (Subgroup.mem_set_normalizer_iff.mp hn (yUnit τ K i 1)).mp
    (mem_rootSubgroup.mpr ⟨1, by rw [pinnedX_neg_single]⟩)
  obtain ⟨d, hd⟩ := mem_rootSubgroup.mp hconj
  have hinv : (xUnit τ K i c)⁻¹ = xUnit τ K i (-c) := by
    apply Units.ext
    rfl
  rw [pinnedX_neg_single] at hd
  have heq : xUnit τ K i c * yUnit τ K i 1 * xUnit τ K i (-c) = yUnit τ K i d := by
    simpa [hinv] using hd.symm
  have happly := congrArg (fun T : Module.End K (RootModule τ K) =>
    T (rootVec τ K (-Pi.single i 1))) (congrArg Units.val heq)
  have hy : (yUnit τ K i d : Module.End K (RootModule τ K))
      (rootVec τ K (-Pi.single i 1)) = rootVec τ K (-Pi.single i 1) := by
    rw [coe_yUnit, yOp_rootVec_neg_normalizer]
  rw [xUnit_yUnit_xUnit_apply_negRoot, hy] at happly
  have hcoord := congrArg (fun v : RootModule τ K =>
    v (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩)) happly
  rw [rootVec_eq_single_normalizer _ (isRoot_single τ i),
    rootVec_eq_single_normalizer _ (isRoot_neg_single τ i), hVec] at hcoord
  have hroots : -Pi.single i 1 ≠ Pi.single i 1 := (single_ne_neg_single i).symm
  have hc4 : c ^ 4 = 0 := by
    simpa [hroots, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] using hcoord
  exact (pow_eq_zero_iff (a := c) (n := 4) (by norm_num)).1 hc4

/-- An element of a pinned simple-root subgroup that normalizes the opposite
simple-root subgroup is the identity. This is the local operator-unit form of
the normalizer input used by the external G₂ Curtis--Tits proof. -/
theorem eq_one_of_mem_normalizer_negSimpleRoot {τ : Tag} {K : Type*} [Field K]
    (i : Fin τ.rank) {u : (Module.End K (RootModule τ K))ˣ}
    (hu : u ∈ rootSubgroup τ K (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer
      (rootSubgroup τ K (-Pi.single i 1) : Set (Module.End K (RootModule τ K))ˣ)) :
    u = 1 := by
  obtain ⟨c, hc⟩ := mem_rootSubgroup.mp hu
  rw [pinnedX_single] at hc
  have hn' := hn
  rw [← hc] at hn'
  rw [← hc]
  have hc0 := xUnit_eq_one_of_mem_normalizer_negSimpleRoot i c hn'
  rw [hc0, xUnit_zero]

/-- The same normalizer criterion on the actual adjoint operator group. The
root subgroup is restricted to `adjointGroup`, matching the external
Curtis--Tits carrier; coercion to the ambient endomorphism-unit group reduces
the claim to the operator calculation above. -/
theorem adjointGroup_eq_one_of_mem_normalizer_negSimpleRoot {τ : Tag} {K : Type*} [Field K]
    (i : Fin τ.rank) {u : ↥(adjointGroup τ K)}
    (hu : u ∈ (rootSubgroup τ K (Pi.single i 1)).subgroupOf (adjointGroup τ K))
    (hn : u ∈ Subgroup.normalizer
      ((rootSubgroup τ K (-Pi.single i 1)).subgroupOf (adjointGroup τ K) :
        Set (adjointGroup τ K))) :
    u = 1 := by
  let S := rootSubgroup τ K (-Pi.single i 1)
  have hSle : S ≤ adjointGroup τ K := rootSubgroup_le_adjointGroup (-Pi.single i 1)
  have hnAmbient : (u : (Module.End K (RootModule τ K))ˣ) ∈
      Subgroup.normalizer (S : Set (Module.End K (RootModule τ K))ˣ) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro z
    constructor
    · intro hz
      let z' : adjointGroup τ K := ⟨z, hSle hz⟩
      have hz' : z' ∈ S.subgroupOf (adjointGroup τ K) :=
        Subgroup.mem_subgroupOf.mpr hz
      have hconj' := (Subgroup.mem_set_normalizer_iff.mp hn z').mp hz'
      have hconj : (u * z' * u⁻¹ : adjointGroup τ K) ∈
          S.subgroupOf (adjointGroup τ K) := hconj'
      simpa using (Subgroup.mem_subgroupOf.mp hconj)
    · intro hz
      let zConj : adjointGroup τ K := ⟨_, hSle hz⟩
      have hzConj : zConj ∈ S.subgroupOf (adjointGroup τ K) :=
        Subgroup.mem_subgroupOf.mpr hz
      have hzBack' : (u⁻¹ * zConj * u) ∈ S.subgroupOf (adjointGroup τ K) :=
        (Subgroup.mem_set_normalizer_iff''.mp hn zConj).mp hzConj
      have hzBack : ((u⁻¹ * zConj * u : adjointGroup τ K) :
          (Module.End K (RootModule τ K))ˣ) ∈ S :=
        Subgroup.mem_subgroupOf.mp hzBack'
      have hback_eq : ((u⁻¹ * zConj * u : adjointGroup τ K) :
          (Module.End K (RootModule τ K))ˣ) = z := by
        dsimp [zConj]
        group
      rw [hback_eq] at hzBack
      exact hzBack
  apply Subtype.ext
  exact eq_one_of_mem_normalizer_negSimpleRoot i (Subgroup.mem_subgroupOf.mp hu) hnAmbient

/-- Every exceptional Chevalley adjoint group on the root module contains a
noncommuting pair of actual endomorphism units. The witness is extracted from
the positive-root operator's failure to normalize the opposite root subgroup.
-/
theorem adjointGroup_exists_noncommuting_pair {τ : Tag} {K : Type*} [Field K]
    (i : Fin τ.rank) :
    ∃ g h : ↥(adjointGroup τ K), g * h ≠ h * g := by
  classical
  let x := xUnit τ K i 1
  let S := rootSubgroup τ K (-Pi.single i 1)
  have hxnot : x ∉ Subgroup.normalizer (S : Set (Module.End K (RootModule τ K))ˣ) := by
    intro hx
    have hzero := xUnit_eq_one_of_mem_normalizer_negSimpleRoot i 1 hx
    exact one_ne_zero hzero
  have hpair : ∃ y ∈ S, x * y ≠ y * x := by
    by_contra h
    have hcomm : ∀ y ∈ S, x * y = y * x := by
      intro y hy
      by_contra hxy
      exact h ⟨y, hy, hxy⟩
    apply hxnot
    apply Subgroup.mem_set_normalizer_iff.mpr
    intro y
    constructor
    · intro hy
      have hxy := hcomm y hy
      have heq : x * y * x⁻¹ = y := calc
        x * y * x⁻¹ = y * x * x⁻¹ := by rw [hxy]
        _ = y := by simp
      rw [heq]
      exact hy
    · intro hyconj
      have hxy := hcomm (x * y * x⁻¹) hyconj
      have hback : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
        calc
          x⁻¹ * (x * y * x⁻¹) * x = x⁻¹ * ((x * y * x⁻¹) * x) := by
            simp only [mul_assoc]
          _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [hxy.symm]
          _ = x * y * x⁻¹ := by group
      have hyEq : y = x * y * x⁻¹ := by
        calc
          y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = x * y * x⁻¹ := hback
      rw [hyEq]
      exact hyconj
  obtain ⟨y, hy, hxy⟩ := hpair
  refine ⟨⟨x, xUnit_mem_adjointGroup i 1⟩,
    ⟨y, rootSubgroup_le_adjointGroup (-Pi.single i 1) hy⟩, ?_⟩
  intro hcomm
  have hval := congrArg Subtype.val hcomm
  apply hxy
  simpa using hval

end InfoGeometry.Exceptional.CFSGPort.Chevalley
