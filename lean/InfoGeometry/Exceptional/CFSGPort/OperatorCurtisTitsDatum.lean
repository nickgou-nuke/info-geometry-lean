/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyCommutatorGroup
public import InfoGeometry.Exceptional.CFSGPort.CurtisTitsRankOne
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyBraidWalk

/-!
# Curtis--Tits datum on the pinned exceptional operator group

This is the local root-pinned carrier translation of the external
`CurtisTits.IsCTGroupDatum`. It packages the existing noncommutative
endomorphism-unit root groups, simple-root tori, and Weyl representatives;
it introduces no new group realization.
-/

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

open RootOps RootWalk

variable {τ : Tag} {K : Type*} [Field K]

abbrev adjointRootSubgroup (α : RootCarrier τ) :
    Subgroup (adjointGroup τ K) :=
  (rootSubgroup τ K α.1).subgroupOf (adjointGroup τ K)

abbrev adjointSimpleRootTorus (i : Fin τ.rank) :
    Subgroup (adjointGroup τ K) :=
  (simpleRootTorusSubgroup (τ := τ) (K := K) i).subgroupOf (adjointGroup τ K)

abbrev adjointRankOneSubgroup (i : Fin τ.rank) :
    Subgroup (adjointGroup τ K) :=
  adjointRootSubgroup (τ := τ) (K := K) ⟨Pi.single i 1, isRoot_single τ i⟩ ⊔
    adjointRootSubgroup (τ := τ) (K := K) ⟨-Pi.single i 1, isRoot_neg_single τ i⟩

@[expose] noncomputable def adjointSimpleWeyl (i : Fin τ.rank) : adjointGroup τ K :=
  ⟨weylElt τ K i 1, weylElt_mem_adjointGroup (τ := τ) (K := K) i 1⟩

@[simp] theorem coe_adjointSimpleWeyl (i : Fin τ.rank) :
    (adjointSimpleWeyl (τ := τ) (K := K) i : ModGL τ K) = weylElt τ K i 1 := rfl

@[simp] theorem adjointSimpleWeyl_subtype (i : Fin τ.rank) :
    (adjointGroup τ K).subtype (adjointSimpleWeyl (τ := τ) (K := K) i) =
      weylElt τ K i 1 := rfl

private theorem map_adjointSimpleWeyl_subtype (w : List (Fin τ.rank)) :
    (w.map (adjointSimpleWeyl (τ := τ) (K := K))).map
        (adjointGroup τ K).subtype =
      w.map (fun i => weylElt τ K i 1) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [ih, adjointSimpleWeyl_subtype]

/-- The external Curtis--Tits datum contract, specialized to the pinned
exceptional root-module operators and restricted to their generated adjoint
group. -/
structure IsOperatorCTGroupDatum : Prop where
  n_mem : ∀ i, adjointSimpleWeyl (τ := τ) (K := K) i ∈
    adjointRankOneSubgroup (τ := τ) (K := K) i
  conj_mem : ∀ i (α : RootCarrier τ) (x : adjointGroup τ K),
    x ∈ adjointRootSubgroup (τ := τ) (K := K) α →
      adjointSimpleWeyl (τ := τ) (K := K) i * x *
        (adjointSimpleWeyl (τ := τ) (K := K) i)⁻¹ ∈
          adjointRootSubgroup (τ := τ) (K := K)
            ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩
  braid : ∀ i j,
    ((CoxeterSystem.alternatingWord i j
      (braidLength (τ.cartan i j * τ.cartan j i))).map
        (adjointSimpleWeyl (τ := τ) (K := K))).prod =
      ((CoxeterSystem.alternatingWord j i
        (braidLength (τ.cartan i j * τ.cartan j i))).map
          (adjointSimpleWeyl (τ := τ) (K := K))).prod
  H_le : ∀ i, adjointSimpleRootTorus (τ := τ) (K := K) i ≤
    adjointRankOneSubgroup (τ := τ) (K := K) i
  sq_mem : ∀ i,
    (adjointSimpleWeyl (τ := τ) (K := K) i) ^ 2 ∈
      adjointSimpleRootTorus (τ := τ) (K := K) i
  H_conj_mem : ∀ i (α : RootCarrier τ)
      (h : adjointSimpleRootTorus (τ := τ) (K := K) i)
      (x : adjointGroup τ K),
      x ∈ adjointRootSubgroup (τ := τ) (K := K) α →
        h * x * h⁻¹ ∈ adjointRootSubgroup (τ := τ) (K := K) α
  conj_H_mem : ∀ i j (h : adjointSimpleRootTorus (τ := τ) (K := K) j),
    adjointSimpleWeyl (τ := τ) (K := K) i * h *
      (adjointSimpleWeyl (τ := τ) (K := K) i)⁻¹ ∈
        adjointSimpleRootTorus (τ := τ) (K := K) i ⊔
          adjointSimpleRootTorus (τ := τ) (K := K) j
  le_rankOne : ∀ i (α : RootCarrier τ),
    (∀ k, k ≠ i → α.1 k = 0) →
      adjointRootSubgroup (τ := τ) (K := K) α ≤
        adjointRankOneSubgroup (τ := τ) (K := K) i
  iSup_eq_top : (⨆ α : RootCarrier τ,
    adjointRootSubgroup (τ := τ) (K := K) α) = ⊤

/-- Field-by-field port of `Steinberg.Adjoint.adjDatum_isCTGroupDatum` from
the external CFSG development. The proof uses the local root-module carrier
and the already ported root, Weyl, torus, braid, and generation results. -/
theorem adjoint_isOperatorCTGroupDatum : IsOperatorCTGroupDatum (τ := τ) (K := K) where
  n_mem i := by
    rw [adjointRankOneSubgroup, ← Subgroup.subgroupOf_sup
      (rootSubgroup_le_adjointGroup (τ := τ) (K := K) _)
      (rootSubgroup_le_adjointGroup (τ := τ) (K := K) _)]
    apply Subgroup.mem_subgroupOf.mpr
    exact weylElt_mem_operatorRankOneSubgroup (τ := τ) (K := K) i 1
  conj_mem i α x hx := by
    change x.1 ∈ rootSubgroup τ K α.1 at hx
    change weylElt τ K i 1 * x.1 * (weylElt τ K i 1)⁻¹ ∈
      rootSubgroup τ K (reflect τ i α.1)
    rw [← RootOps.map_conj_weylElt_rootSubgroup (τ := τ) (K := K) i α]
    exact Subgroup.mem_map.mpr ⟨x.1, hx, rfl⟩
  braid i j := by
    apply Subtype.ext
    change (adjointGroup τ K).subtype
        ((CoxeterSystem.alternatingWord i j
          (braidLength (τ.cartan i j * τ.cartan j i))).map
            (adjointSimpleWeyl (τ := τ) (K := K))).prod =
      (adjointGroup τ K).subtype
        ((CoxeterSystem.alternatingWord j i
          (braidLength (τ.cartan i j * τ.cartan j i))).map
            (adjointSimpleWeyl (τ := τ) (K := K))).prod
    rw [map_list_prod, map_list_prod]
    rw [map_adjointSimpleWeyl_subtype, map_adjointSimpleWeyl_subtype]
    exact RootWalk.prod_alternatingWord_weylElt (τ := τ) (R := K) i j
  H_le i := by
    rw [adjointSimpleRootTorus, adjointRankOneSubgroup, adjointRootSubgroup,
      ← Subgroup.subgroupOf_sup
        (rootSubgroup_le_adjointGroup (τ := τ) (K := K) _)
        (rootSubgroup_le_adjointGroup (τ := τ) (K := K) _)]
    exact Subgroup.subgroupOf_mono _
      (simpleRootTorusSubgroup_le_operatorRankOneSubgroup (τ := τ) (K := K) i)
  sq_mem i := by
    apply Subgroup.mem_subgroupOf.mpr
    simpa [adjointSimpleWeyl] using
      (weylElt_one_sq_mem_simpleRootTorusSubgroup (τ := τ) (K := K) i)
  H_conj_mem i α h x hx := by
    have hh : (h.1 : adjointGroup τ K) ∈
        (simpleRootTorusSubgroup (τ := τ) (K := K) i).subgroupOf (adjointGroup τ K) := h.2
    have hroot : (x : adjointGroup τ K) ∈
        (rootSubgroup τ K α.1).subgroupOf (adjointGroup τ K) := hx
    apply Subgroup.mem_subgroupOf.mpr
    exact simpleRootTorusSubgroup_conj_mem_rootSubgroup (τ := τ) (K := K) i α.2
      (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hroot)
  conj_H_mem i j h := by
    rw [← Subgroup.subgroupOf_sup
      (simpleRootTorusSubgroup_le_adjointGroup (τ := τ) (K := K) i)
      (simpleRootTorusSubgroup_le_adjointGroup (τ := τ) (K := K) j)]
    apply Subgroup.mem_subgroupOf.mpr
    exact weylElt_one_conj_simpleRootTorusSubgroup_mem_sup (τ := τ) (K := K) i j
      (Subgroup.mem_subgroupOf.mp h.2)
  le_rankOne i α hsupport := by
    rw [adjointRankOneSubgroup, adjointRootSubgroup, ← Subgroup.subgroupOf_sup
      (rootSubgroup_le_adjointGroup (τ := τ) (K := K) _)
      (rootSubgroup_le_adjointGroup (τ := τ) (K := K) _)]
    exact Subgroup.subgroupOf_mono _
      (rootSubgroup_le_operatorRankOneSubgroup_of_support (τ := τ) (K := K) i
        α.2 hsupport)
  iSup_eq_top := by
    apply (Subgroup.map_subtype_inj (H := adjointGroup τ K)).mp
    rw [Subgroup.map_iSup]
    simp only [adjointRootSubgroup]
    simp_rw [Subgroup.map_subgroupOf_eq_of_le
      (rootSubgroup_le_adjointGroup (τ := τ) (K := K) _)]
    simp only [Subgroup.map_top, Subgroup.range_subtype]
    rw [adjointGroup_eq_rootSpan]
    simp [rootSpan, iSup_subtype, iSup_and]

end InfoGeometry.Exceptional.CFSGPort.Chevalley

end
