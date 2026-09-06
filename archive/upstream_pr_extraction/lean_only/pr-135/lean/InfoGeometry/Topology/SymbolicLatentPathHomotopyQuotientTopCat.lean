import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientFunctoriality

namespace InfoGeometry.Topology

open CategoryTheory

universe u

/-!
# Genuine `TopCat` structure on symbolic-latent path homotopy quotients

The compact-open topology on `ContinuousMap` supplies the path-space topology;
the quotient type then receives Mathlib's quotient topology.  This owner uses
that native topology rather than declaring an arbitrary one.
-/

theorem continuous_symbolicLatentPathHomotopyQuotientMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    Continuous (mapSymbolicLatentPathHomotopyQuotient f) := by
  have hq : Continuous (symbolicLatentPathHomotopyQuotientMap (X := Y)) :=
    @continuous_quotient_mk' (SymbolicLatentPath Y) _
      (symbolicLatentPathHomotopySetoid (X := Y))
  have hp : Continuous (f.comp : SymbolicLatentPath X → SymbolicLatentPath Y) :=
    ContinuousMap.continuous_postcomp f
  exact Continuous.quotient_lift (hq.comp hp) (by
    intro γ₀ γ₁ h
    exact @Quotient.sound (SymbolicLatentPath Y)
      (symbolicLatentPathHomotopySetoid (X := Y))
      (f.comp γ₀) (f.comp γ₁) (mapSymbolicLatentPathHomotopic f h))

def symbolicLatentPathHomotopyQuotientTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) ⟶
      TopCat.of (SymbolicLatentPathHomotopyQuotient (X := Y)) :=
  TopCat.ofHom
    { toFun := mapSymbolicLatentPathHomotopyQuotient f
      continuous_toFun := continuous_symbolicLatentPathHomotopyQuotientMap f }

theorem symbolicLatentPathHomotopyQuotientTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyQuotientTopCatHom f q =
      mapSymbolicLatentPathHomotopyQuotient f q :=
  rfl

theorem symbolicLatentPathHomotopyQuotientTopCatHom_id
    {X : Type} [TopologicalSpace X] :
    symbolicLatentPathHomotopyQuotientTopCatHom
        (ContinuousMap.id X) =
      𝟙 (TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X))) := by
  ext q
  exact congrFun
    (mapSymbolicLatentPathHomotopyQuotient_id (X := X)) q

theorem symbolicLatentPathHomotopyQuotientTopCatHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    symbolicLatentPathHomotopyQuotientTopCatHom (g.comp f) =
      symbolicLatentPathHomotopyQuotientTopCatHom f ≫
        symbolicLatentPathHomotopyQuotientTopCatHom g := by
  ext q
  exact congrFun
    (mapSymbolicLatentPathHomotopyQuotient_comp f g) q

@[simp] theorem symbolicLatentPathHomotopyQuotientTopCatHom_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    (symbolicLatentPathHomotopyQuotientTopCatHom (g.comp f) q) =
      (symbolicLatentPathHomotopyQuotientTopCatHom f ≫
        symbolicLatentPathHomotopyQuotientTopCatHom g) q := by
  simpa [CategoryTheory.comp_apply] using
    congrArg (fun h => h q) (symbolicLatentPathHomotopyQuotientTopCatHom_comp f g)

theorem continuous_symbolicLatentPathHomotopyEndpointMap
    {X : Type} [TopologicalSpace X] :
    Continuous (symbolicLatentPathHomotopyEndpointMap
      (X := X)) := by
  exact Continuous.quotient_lift
    ((continuous_eval_const (0 : SymbolicPathDomain) :
      Continuous (fun γ : SymbolicLatentPath X => γ 0)).prodMk
      (continuous_eval_const (1 : SymbolicPathDomain) :
        Continuous (fun γ : SymbolicLatentPath X => γ 1))) (by
    intro γ₀ γ₁ h
    exact h.same_endpoints)

def symbolicLatentPathHomotopyEndpointTopCatHom
    {X : Type} [TopologicalSpace X] :
    TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) ⟶
      TopCat.of (X × X) :=
  TopCat.ofHom
    { toFun := symbolicLatentPathHomotopyEndpointMap (X := X)
      continuous_toFun := continuous_symbolicLatentPathHomotopyEndpointMap (X := X) }

theorem symbolicLatentPathHomotopyEndpointTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyEndpointTopCatHom q =
      symbolicLatentPathHomotopyEndpointMap q :=
  rfl

def symbolicLatentPathHomotopyEndpointMapTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    TopCat.of (X × X) ⟶ TopCat.of (Y × Y) :=
  TopCat.ofHom
    { toFun := mapSymbolicLatentPathHomotopyEndpoint f
      continuous_toFun := f.continuous.prodMap f.continuous }

theorem symbolicLatentPathHomotopyEndpointTopCatHom_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    symbolicLatentPathHomotopyQuotientTopCatHom f ≫
        symbolicLatentPathHomotopyEndpointTopCatHom =
      symbolicLatentPathHomotopyEndpointTopCatHom ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom f := by
  ext q <;> refine Quotient.inductionOn q ?_ <;> intro γ <;>
    rfl

theorem symbolicLatentPathHomotopyEndpointTopCatHom_natural_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    symbolicLatentPathHomotopyQuotientTopCatHom (g.comp f) ≫
        symbolicLatentPathHomotopyEndpointTopCatHom =
      symbolicLatentPathHomotopyEndpointTopCatHom ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom f ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom g := by
  rw [symbolicLatentPathHomotopyQuotientTopCatHom_comp f g]
  rw [Category.assoc]
  rw [symbolicLatentPathHomotopyEndpointTopCatHom_natural g]
  rw [← Category.assoc]
  rw [symbolicLatentPathHomotopyEndpointTopCatHom_natural f]
  rw [Category.assoc]

theorem symbolicLatentPathHomotopyEndpointMapTopCatHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    symbolicLatentPathHomotopyEndpointMapTopCatHom (g.comp f) =
      symbolicLatentPathHomotopyEndpointMapTopCatHom f ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom g := by
  ext p <;> rfl

end InfoGeometry.Topology
