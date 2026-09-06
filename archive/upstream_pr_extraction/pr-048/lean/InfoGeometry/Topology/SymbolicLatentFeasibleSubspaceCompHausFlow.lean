import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceCompHaus

/-!
# Compact-Hausdorff flow on a feasible symbolic-latent subtype

For a symbolic latent flow, the native feasible-subspace homeomorphisms are
packaged directly as `CompHaus` isomorphisms.  The inverse and additive laws
are proved on the bundled maps, without passing through a separate `IsIso`
transport theorem.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [Fintype ι]

noncomputable def symbolicLatentFeasibleSubspaceCompHausFlowIso
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (t : ℝ) :
    symbolicLatentFeasibleSubspaceCompHaus S targets hclosed ≅
      symbolicLatentFeasibleSubspaceCompHaus S targets hclosed := by
  letI : CompactSpace (feasibleLatentSubspace S targets) :=
    (isClosed_finiteSymbolicLatentSystem_feasibleSet S targets hclosed
      ).isClosedEmbedding_subtypeVal.compactSpace
  change CompHaus.of (feasibleLatentSubspace S targets) ≅
    CompHaus.of (feasibleLatentSubspace S targets)
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := F.feasibleSubspaceMap t targets
          continuous_toFun := F.continuous_feasibleSubspaceMap t targets }⟩
      inv := ⟨TopCat.ofHom
        { toFun := F.feasibleSubspaceMap (-t) targets
          continuous_toFun := F.continuous_feasibleSubspaceMap (-t) targets }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        change F.act (-t) (F.act t (x : X)) = (x : X)
        rw [← F.add_apply (-t) t x]
        simp [F.zero_apply]
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        change F.act t (F.act (-t) (x : X)) = (x : X)
        rw [← F.add_apply t (-t) x]
        simp [F.zero_apply] }

@[simp] theorem symbolicLatentFeasibleSubspaceCompHausFlowIso_hom_apply
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (t : ℝ)
    (x : feasibleLatentSubspace S targets) :
    (symbolicLatentFeasibleSubspaceCompHausFlowIso
      F targets hclosed t).hom x =
      F.feasibleSubspaceMap t targets x := by
  rfl

theorem symbolicLatentFeasibleSubspaceCompHausFlowIso_zero
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    symbolicLatentFeasibleSubspaceCompHausFlowIso F targets hclosed 0 =
      Iso.refl (symbolicLatentFeasibleSubspaceCompHaus S targets hclosed) := by
  apply Iso.ext
  apply ConcreteCategory.hom_ext
  intro x
  change F.feasibleSubspaceMap 0 targets x = x
  exact F.feasibleSubspaceHomeomorph_zero_apply targets x

theorem symbolicLatentFeasibleSubspaceCompHausFlowIso_add
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (s t : ℝ) :
    (symbolicLatentFeasibleSubspaceCompHausFlowIso
      F targets hclosed (s + t)).hom =
      (symbolicLatentFeasibleSubspaceCompHausFlowIso
        F targets hclosed t).hom ≫
        (symbolicLatentFeasibleSubspaceCompHausFlowIso
          F targets hclosed s).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  change F.feasibleSubspaceMap (s + t) targets x =
    F.feasibleSubspaceMap s targets (F.feasibleSubspaceMap t targets x)
  simpa [F.feasibleSubspaceHomeomorph_apply] using
    F.feasibleSubspaceHomeomorph_add_apply s t targets x

theorem symbolicLatentFeasibleSubspaceCompHausFlowIso_inv_eq_neg_hom
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (t : ℝ) :
    (symbolicLatentFeasibleSubspaceCompHausFlowIso
      F targets hclosed t).inv =
      (symbolicLatentFeasibleSubspaceCompHausFlowIso
        F targets hclosed (-t)).hom := by
  rfl

end InfoGeometry.Topology

end
