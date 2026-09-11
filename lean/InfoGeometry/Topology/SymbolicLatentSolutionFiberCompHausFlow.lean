import InfoGeometry.Topology.SymbolicLatentSolutionFiberCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Compact-Hausdorff flow on exact symbolic-latent solution fibers

An observation-preserving symbolic flow restricts to every exact solution
fiber.  This owner packages those restrictions as genuine `CompHaus`
isomorphisms and proves their inverse and additive laws.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [Fintype ι]

def SymbolicLatentFlow.solutionFiberMap
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (t : ℝ)
    (values : ι → ℝ) :
    symbolicLatentSolutionFiber S values →
      symbolicLatentSolutionFiber S values :=
  fun x =>
    ⟨F.act t x, F.maps_solutionSet t values ⟨x, x.property, rfl⟩⟩

theorem SymbolicLatentFlow.continuous_solutionFiberMap
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (t : ℝ)
    (values : ι → ℝ) :
    Continuous (F.solutionFiberMap t values) := by
  exact (F.continuous_time t).comp continuous_subtype_val |>.subtype_mk
    (fun x => F.maps_solutionSet t values ⟨x, x.property, rfl⟩)

noncomputable def SymbolicLatentFlow.solutionFiberCompHausFlowIso
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (values : ι → ℝ)
    (t : ℝ) :
    symbolicLatentSolutionFiberCompHaus S values ≅
      symbolicLatentSolutionFiberCompHaus S values := by
  letI : CompactSpace (symbolicLatentSolutionFiber S values) :=
    (isClosed_finiteSymbolicLatentSystem_solutionSet S values
      ).isClosedEmbedding_subtypeVal.compactSpace
  change CompHaus.of (symbolicLatentSolutionFiber S values) ≅
    CompHaus.of (symbolicLatentSolutionFiber S values)
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := F.solutionFiberMap t values
          continuous_toFun := F.continuous_solutionFiberMap t values }⟩
      inv := ⟨TopCat.ofHom
        { toFun := F.solutionFiberMap (-t) values
          continuous_toFun := F.continuous_solutionFiberMap (-t) values }⟩
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

@[simp] theorem SymbolicLatentFlow.solutionFiberCompHausFlowIso_hom_apply
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (values : ι → ℝ)
    (t : ℝ)
    (x : symbolicLatentSolutionFiber S values) :
    (F.solutionFiberCompHausFlowIso values t).hom x =
      F.solutionFiberMap t values x :=
  rfl

theorem SymbolicLatentFlow.solutionFiberCompHausFlowIso_zero
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (values : ι → ℝ) :
    F.solutionFiberCompHausFlowIso values 0 =
      Iso.refl (symbolicLatentSolutionFiberCompHaus S values) := by
  apply Iso.ext
  dsimp [symbolicLatentSolutionFiberCompHaus]
  apply ConcreteCategory.hom_ext
  intro x
  change F.solutionFiberMap 0 values x = x
  apply Subtype.ext
  change F.act 0 (x : X) = (x : X)
  exact F.zero_apply (x : X)

theorem SymbolicLatentFlow.solutionFiberCompHausFlowIso_add
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (values : ι → ℝ)
    (s t : ℝ) :
    (F.solutionFiberCompHausFlowIso values (s + t)).hom =
      (F.solutionFiberCompHausFlowIso values t).hom ≫
        (F.solutionFiberCompHausFlowIso values s).hom := by
  dsimp [symbolicLatentSolutionFiberCompHaus]
  apply ConcreteCategory.hom_ext
  intro x
  change F.solutionFiberMap (s + t) values x =
    F.solutionFiberMap s values (F.solutionFiberMap t values x)
  apply Subtype.ext
  change F.act (s + t) (x : X) =
    F.act s (F.act t (x : X))
  exact F.add_apply s t (x : X)

theorem SymbolicLatentFlow.solutionFiberCompHausFlowIso_inv_eq_neg_hom
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (values : ι → ℝ)
    (t : ℝ) :
    (F.solutionFiberCompHausFlowIso values t).inv =
      (F.solutionFiberCompHausFlowIso values (-t)).hom :=
  rfl

end InfoGeometry.Topology
