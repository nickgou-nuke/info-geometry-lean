import InfoGeometry.Topology.SymbolicLatentQuotientOrbitClosureFlowHomeomorph
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of quotient orbit-closure flow

The quotient orbit-closure flow homeomorphism is promoted to a `CompHaus`
isomorphism when the quotient carrier is compact Hausdorff.  This is only
categorical packaging of the native homeomorphism; it adds no dynamical or
measure-theoretic assumptions.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

noncomputable def symbolicLatentQuotientOrbitClosureCompHaus
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    [CompactSpace Q] [T2Space Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) : CompHaus := by
  letI : CompactSpace (SymbolicLatentOrbitClosure K q) :=
    isCompact_iff_compactSpace.mp (isCompact_symbolicLatentOrbitClosure K q)
  exact CompHaus.of (SymbolicLatentOrbitClosure K q)

noncomputable def SymbolicLatentFlowQuotient.orbitClosureFlowCompHausIso
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    [CompactSpace Q] [T2Space Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (t : ℝ) :
    symbolicLatentQuotientOrbitClosureCompHaus K q ≅
      symbolicLatentQuotientOrbitClosureCompHaus K (K.act t q) := by
  dsimp [symbolicLatentQuotientOrbitClosureCompHaus]
  letI : CompactSpace (SymbolicLatentOrbitClosure K q) :=
    isCompact_iff_compactSpace.mp (isCompact_symbolicLatentOrbitClosure K q)
  letI : CompactSpace
      (SymbolicLatentOrbitClosure K (K.act t q)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentOrbitClosure K (K.act t q))
  let e := K.orbitClosureFlowHomeomorph q t
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e.symm (e y) = y
        exact e.symm_apply_apply y
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

theorem SymbolicLatentFlowQuotient.orbitClosureFlowCompHausIso_hom_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    [CompactSpace Q] [T2Space Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (t : ℝ)
    (y : SymbolicLatentOrbitClosure K q) :
    (K.orbitClosureFlowCompHausIso q t).hom y =
      K.orbitClosureFlowHomeomorph q t y :=
  rfl

@[simp] theorem SymbolicLatentFlowQuotient.orbitClosureFlowCompHausIso_inv_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    [CompactSpace Q] [T2Space Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (t : ℝ)
    (y : SymbolicLatentOrbitClosure K (K.act t q)) :
    (K.orbitClosureFlowCompHausIso q t).inv y =
      (K.orbitClosureFlowHomeomorph q t).symm y :=
  rfl

theorem SymbolicLatentFlowQuotient.orbitClosureFlowCompHausIso_comp_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    [CompactSpace Q] [T2Space Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (s t : ℝ)
    (y : SymbolicLatentOrbitClosure K q) :
    (((K.orbitClosureFlowCompHausIso q s).hom ≫
        (K.orbitClosureFlowCompHausIso (K.act s q) t).hom) y).1 =
      ((K.orbitClosureFlowCompHausIso q (t + s)).hom y).1 := by
  change K.act t (K.act s y.1) = K.act (t + s) y.1
  simpa [add_comm] using (K.act_add t s y.1).symm

end
end InfoGeometry.Topology
