import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularFeasibleHomeomorph

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# TopCat transport for feasible modular-flow slices

`feasibleHomeomorph` already proves that an observation-preserving modular
flow acts by a homeomorphism on each feasible subtype.  This owner exposes
that existing result as a native `TopCat` isomorphism; it does not assert any
additional recurrence, compactness, or analytic structure.
-/

def SymbolicLatentObservableModularFlow.feasibleHomeomorphTopCatHom
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (t : ℝ) :
    TopCat.of (S.feasibleSet targets) ⟶ TopCat.of (S.feasibleSet targets) :=
  TopCat.ofHom
    { toFun := Φ.feasibleHomeomorph targets t
      continuous_toFun := (Φ.feasibleHomeomorph targets t).continuous_toFun }

def SymbolicLatentObservableModularFlow.feasibleHomeomorphInverseTopCatHom
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (t : ℝ) :
    TopCat.of (S.feasibleSet targets) ⟶ TopCat.of (S.feasibleSet targets) :=
  TopCat.ofHom
    { toFun := (Φ.feasibleHomeomorph targets t).symm
      continuous_toFun := (Φ.feasibleHomeomorph targets t).symm.continuous_toFun }

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorphTopCatHom_isIso
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (t : ℝ) :
    IsIso (Φ.feasibleHomeomorphTopCatHom targets t) := by
  refine IsIso.mk ⟨Φ.feasibleHomeomorphInverseTopCatHom targets t, ?_, ?_⟩
  · apply TopCat.hom_ext
    ext x
    simpa [feasibleHomeomorphTopCatHom,
      feasibleHomeomorphInverseTopCatHom, TopCat.comp_app,
      TopCat.id_app, TopCat.ofHom] using
      (Φ.feasibleHomeomorph targets t).symm_apply_apply x
  · apply TopCat.hom_ext
    ext x
    simpa [feasibleHomeomorphTopCatHom,
      feasibleHomeomorphInverseTopCatHom, TopCat.comp_app,
      TopCat.id_app, TopCat.ofHom] using
      (Φ.feasibleHomeomorph targets t).apply_symm_apply x

@[simp] theorem SymbolicLatentObservableModularFlow.feasibleHomeomorphTopCatHom_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (t : ℝ) (x : S.feasibleSet targets) :
    Φ.feasibleHomeomorphTopCatHom targets t x =
      Φ.feasibleHomeomorph targets t x :=
  rfl

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorphTopCatHom_zero
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) :
    Φ.feasibleHomeomorphTopCatHom targets 0 =
      𝟙 (TopCat.of (S.feasibleSet targets)) := by
  apply TopCat.hom_ext
  ext x
  change (Φ.feasibleHomeomorph targets 0 x).1 = x.1
  exact congrArg Subtype.val (Φ.feasibleHomeomorph_zero_apply targets x)

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorphTopCatHom_add
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (s t : ℝ) :
    Φ.feasibleHomeomorphTopCatHom targets (s + t) =
      Φ.feasibleHomeomorphTopCatHom targets t ≫
        Φ.feasibleHomeomorphTopCatHom targets s := by
  apply TopCat.hom_ext
  ext x
  change (Φ.feasibleHomeomorph targets (s + t) x).1 =
    (Φ.feasibleHomeomorph targets s
      (Φ.feasibleHomeomorph targets t x)).1
  exact congrArg Subtype.val (Φ.feasibleHomeomorph_add_apply targets s t x)

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorphTopCatHom_comp
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (s t : ℝ) :
    Φ.feasibleHomeomorphTopCatHom targets s ≫
      Φ.feasibleHomeomorphTopCatHom targets t =
        Φ.feasibleHomeomorphTopCatHom targets (t + s) := by
  simpa [add_comm] using
    (Φ.feasibleHomeomorphTopCatHom_add targets t s).symm

@[simp] theorem SymbolicLatentObservableModularFlow.feasibleHomeomorphTopCatHom_comp_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (s t : ℝ) (x : S.feasibleSet targets) :
    (Φ.feasibleHomeomorphTopCatHom targets s ≫
      Φ.feasibleHomeomorphTopCatHom targets t) x =
        Φ.feasibleHomeomorphTopCatHom targets (t + s) x := by
  simpa [CategoryTheory.comp_apply] using
    congrArg (fun f => f x)
      (Φ.feasibleHomeomorphTopCatHom_comp targets s t)

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorphTopCatHom_comp_inv
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (t : ℝ) :
    Φ.feasibleHomeomorphTopCatHom targets t ≫
      Φ.feasibleHomeomorphInverseTopCatHom targets t =
        𝟙 (TopCat.of (S.feasibleSet targets)) := by
  apply TopCat.hom_ext
  ext x
  simpa [feasibleHomeomorphTopCatHom,
    feasibleHomeomorphInverseTopCatHom, TopCat.comp_app,
    TopCat.id_app, TopCat.ofHom] using
    (Φ.feasibleHomeomorph targets t).apply_symm_apply x

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorphTopCatHom_inv_comp
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (t : ℝ) :
    Φ.feasibleHomeomorphInverseTopCatHom targets t ≫
      Φ.feasibleHomeomorphTopCatHom targets t =
        𝟙 (TopCat.of (S.feasibleSet targets)) := by
  apply TopCat.hom_ext
  ext x
  simpa [feasibleHomeomorphTopCatHom,
    feasibleHomeomorphInverseTopCatHom, TopCat.comp_app,
    TopCat.id_app, TopCat.ofHom] using
    (Φ.feasibleHomeomorph targets t).symm_apply_apply x

end InfoGeometry.Topology
