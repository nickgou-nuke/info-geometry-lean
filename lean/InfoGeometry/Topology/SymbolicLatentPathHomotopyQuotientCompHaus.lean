import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Conditional `CompHaus` packaging of path-homotopy quotients

The quotient carrier is not automatically compact Hausdorff: compactness of
the base space does not by itself make the full compact-open path quotient
compact.  This owner therefore takes the required compact/Hausdorff instances
for the quotient carriers explicitly and transports the existing `TopCat`
functoriality without adding an analytic compactness claim.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X Y Z : Type}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable
  [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := X))]
  [T2Space (SymbolicLatentPathHomotopyQuotient (X := X))]
  [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := Y))]
  [T2Space (SymbolicLatentPathHomotopyQuotient (X := Y))]
  [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := Z))]
  [T2Space (SymbolicLatentPathHomotopyQuotient (X := Z))]

noncomputable def symbolicLatentPathHomotopyQuotientCompHausHom
    (f : C(X, Y)) :
    CompHaus.of (SymbolicLatentPathHomotopyQuotient (X := X)) ⟶
      CompHaus.of (SymbolicLatentPathHomotopyQuotient (X := Y)) := by
  exact ⟨symbolicLatentPathHomotopyQuotientTopCatHom f⟩

theorem symbolicLatentPathHomotopyQuotientCompHausHom_forget
    (f : C(X, Y)) :
    compHausToTop.map (symbolicLatentPathHomotopyQuotientCompHausHom f) =
      symbolicLatentPathHomotopyQuotientTopCatHom f := by
  rfl

@[simp] theorem symbolicLatentPathHomotopyQuotientCompHausHom_apply
    (f : C(X, Y))
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyQuotientCompHausHom f q =
      mapSymbolicLatentPathHomotopyQuotient f q := by
  rfl

theorem symbolicLatentPathHomotopyQuotientCompHausHom_id :
    symbolicLatentPathHomotopyQuotientCompHausHom (ContinuousMap.id X) =
      𝟙 (CompHaus.of (SymbolicLatentPathHomotopyQuotient (X := X))) := by
  apply ConcreteCategory.hom_ext
  intro q
  change symbolicLatentPathHomotopyQuotientTopCatHom
      (ContinuousMap.id X) q = q
  exact congrArg (fun h => h q)
    (symbolicLatentPathHomotopyQuotientTopCatHom_id (X := X))

theorem symbolicLatentPathHomotopyQuotientCompHausHom_comp
    (f : C(X, Y)) (g : C(Y, Z)) :
    symbolicLatentPathHomotopyQuotientCompHausHom (g.comp f) =
      symbolicLatentPathHomotopyQuotientCompHausHom f ≫
        symbolicLatentPathHomotopyQuotientCompHausHom g := by
  apply ConcreteCategory.hom_ext
  intro q
  change symbolicLatentPathHomotopyQuotientTopCatHom (g.comp f) q =
    (symbolicLatentPathHomotopyQuotientTopCatHom f ≫
      symbolicLatentPathHomotopyQuotientTopCatHom g) q
  exact congrArg (fun h => h q)
    (symbolicLatentPathHomotopyQuotientTopCatHom_comp f g)

@[simp] theorem symbolicLatentPathHomotopyQuotientCompHausHom_comp_apply
    (f : C(X, Y)) (g : C(Y, Z))
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyQuotientCompHausHom (g.comp f) q =
      (symbolicLatentPathHomotopyQuotientCompHausHom f ≫
        symbolicLatentPathHomotopyQuotientCompHausHom g) q := by
  exact congrArg (fun h => h q)
    (symbolicLatentPathHomotopyQuotientCompHausHom_comp f g)

noncomputable def symbolicLatentPathHomotopyEndpointCompHausHom
    {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X]
    [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := X))]
    [T2Space (SymbolicLatentPathHomotopyQuotient (X := X))] :
    CompHaus.of (SymbolicLatentPathHomotopyQuotient (X := X)) ⟶
      CompHaus.of (X × X) := by
  exact ⟨symbolicLatentPathHomotopyEndpointTopCatHom (X := X)⟩

noncomputable def symbolicLatentPathHomotopyEndpointMapCompHausHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (f : C(X, Y)) :
    CompHaus.of (X × X) ⟶ CompHaus.of (Y × Y) := by
  exact ⟨symbolicLatentPathHomotopyEndpointMapTopCatHom f⟩

theorem symbolicLatentPathHomotopyEndpointCompHausHom_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := X))]
    [T2Space (SymbolicLatentPathHomotopyQuotient (X := X))]
    [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := Y))]
    [T2Space (SymbolicLatentPathHomotopyQuotient (X := Y))]
    (f : C(X, Y)) :
    symbolicLatentPathHomotopyQuotientCompHausHom f ≫
        symbolicLatentPathHomotopyEndpointCompHausHom (X := Y) =
    symbolicLatentPathHomotopyEndpointCompHausHom (X := X) ≫
        symbolicLatentPathHomotopyEndpointMapCompHausHom f := by
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  simpa [Functor.map_comp,
    symbolicLatentPathHomotopyQuotientCompHausHom,
    symbolicLatentPathHomotopyEndpointCompHausHom,
    symbolicLatentPathHomotopyEndpointMapCompHausHom] using
    (symbolicLatentPathHomotopyEndpointTopCatHom_natural f)

@[simp] theorem symbolicLatentPathHomotopyEndpointCompHausHom_forget
    {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X]
    [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := X))]
    [T2Space (SymbolicLatentPathHomotopyQuotient (X := X))] :
    compHausToTop.map
        (symbolicLatentPathHomotopyEndpointCompHausHom (X := X)) =
      symbolicLatentPathHomotopyEndpointTopCatHom (X := X) := by
  rfl

@[simp] theorem symbolicLatentPathHomotopyEndpointCompHausHom_apply
    {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X]
    [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := X))]
    [T2Space (SymbolicLatentPathHomotopyQuotient (X := X))]
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyEndpointCompHausHom (X := X) q =
      symbolicLatentPathHomotopyEndpointMap q := by
  rfl

@[simp] theorem symbolicLatentPathHomotopyEndpointMapCompHausHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (f : C(X, Y)) (p : X × X) :
    symbolicLatentPathHomotopyEndpointMapCompHausHom f p =
      mapSymbolicLatentPathHomotopyEndpoint f p := by
  rfl

theorem symbolicLatentPathHomotopyEndpointCompHausHom_natural_comp
    {X Y Z : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
    [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := X))]
    [T2Space (SymbolicLatentPathHomotopyQuotient (X := X))]
    [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := Y))]
    [T2Space (SymbolicLatentPathHomotopyQuotient (X := Y))]
    [CompactSpace (SymbolicLatentPathHomotopyQuotient (X := Z))]
    [T2Space (SymbolicLatentPathHomotopyQuotient (X := Z))]
    (f : C(X, Y)) (g : C(Y, Z)) :
    symbolicLatentPathHomotopyQuotientCompHausHom (g.comp f) ≫
        symbolicLatentPathHomotopyEndpointCompHausHom (X := Z) =
      symbolicLatentPathHomotopyEndpointCompHausHom (X := X) ≫
        symbolicLatentPathHomotopyEndpointMapCompHausHom f ≫
          symbolicLatentPathHomotopyEndpointMapCompHausHom g := by
  rw [symbolicLatentPathHomotopyQuotientCompHausHom_comp f g]
  rw [Category.assoc]
  rw [symbolicLatentPathHomotopyEndpointCompHausHom_natural g]
  rw [← Category.assoc]
  rw [symbolicLatentPathHomotopyEndpointCompHausHom_natural f]
  rw [Category.assoc]

end InfoGeometry.Topology

