import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotient
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientFunctoriality
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` endpoint readout for symbolic-latent based-loop homotopy quotients

The based-loop quotient already sits as the endpoint fiber of the path
homotopy quotient.  This file exposes that fiber as a `TopCat` morphism and
records the constant endpoint readout at the chosen basepoint.
-/

def symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom
    {X : Type} [TopologicalSpace X] (x : X) :
    TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient x) ⟶
      TopCat.of (X × X) :=
  symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom x ≫
    symbolicLatentPathHomotopyEndpointTopCatHom

theorem symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_apply
    {X : Type} [TopologicalSpace X] (x : X)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x q =
      (x, x) := by
  change symbolicLatentPathHomotopyEndpointMap q.1 = (x, x)
  exact q.2

theorem symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_inclusion_natural
    {X : Type} [TopologicalSpace X] (x : X) :
    symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom x ≫
        symbolicLatentPathHomotopyEndpointTopCatHom =
      symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x := by
  rfl

theorem symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_unique
    {X : Type} [TopologicalSpace X] (x : X)
    {u : TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient x) ⟶
      TopCat.of (X × X)}
    (hu : symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom x ≫
        symbolicLatentPathHomotopyEndpointTopCatHom = u) :
    u = symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x := by
  simpa [symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom] using hu.symm

theorem symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_constant
    {X : Type} [TopologicalSpace X] (x : X) :
    symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x
        (symbolicLatentBasedLoopHomotopyQuotient_constant x) =
      (x, x) :=
  rfl

  theorem symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y) :
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom y =
      symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom x ≫
        symbolicLatentPathHomotopyQuotientTopCatHom f := by
  ext q
  rfl

theorem symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y) :
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom y =
      symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom f := by
  calc
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom y
      = symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
          (symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom y ≫
            symbolicLatentPathHomotopyEndpointTopCatHom) := by
          rfl
    _ = (symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
          symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom y) ≫
          symbolicLatentPathHomotopyEndpointTopCatHom := by
          rw [Category.assoc]
    _ = (symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom x ≫
          symbolicLatentPathHomotopyQuotientTopCatHom f) ≫
          symbolicLatentPathHomotopyEndpointTopCatHom := by
          rw [symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom_natural
            (f := f) (hxy := hxy)]
    _ = symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom x ≫
          (symbolicLatentPathHomotopyQuotientTopCatHom f ≫
            symbolicLatentPathHomotopyEndpointTopCatHom) := by
          rw [Category.assoc]
    _ = symbolicLatentBasedLoopHomotopyQuotientInclusionTopCatHom x ≫
          (symbolicLatentPathHomotopyEndpointTopCatHom ≫
            symbolicLatentPathHomotopyEndpointMapTopCatHom f) := by
          rw [symbolicLatentPathHomotopyEndpointTopCatHom_natural f]
    _ = symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x ≫
          symbolicLatentPathHomotopyEndpointMapTopCatHom f := by
          rfl

theorem symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_natural_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z) :
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz ≫
        symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom z =
      symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom f ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom g := by
  calc
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz ≫
        symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom z
      = symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
          (symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz ≫
            symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom z) := by
          simp
    _ = symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
          (symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom y ≫
            symbolicLatentPathHomotopyEndpointMapTopCatHom g) := by
          rw [symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_natural
            (f := g) (hxy := hyz)]
    _ = (symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
          symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom y) ≫
          symbolicLatentPathHomotopyEndpointMapTopCatHom g := by
          simp
    _ = (symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x ≫
          symbolicLatentPathHomotopyEndpointMapTopCatHom f) ≫
          symbolicLatentPathHomotopyEndpointMapTopCatHom g := by
          rw [symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_natural
            (f := f) (hxy := hxy)]
    _ = symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x ≫
          (symbolicLatentPathHomotopyEndpointMapTopCatHom f ≫
            symbolicLatentPathHomotopyEndpointMapTopCatHom g) := by
          simp
    _ = symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x ≫
          symbolicLatentPathHomotopyEndpointMapTopCatHom (g.comp f) := by
          rw [symbolicLatentPathHomotopyEndpointMapTopCatHom_comp f g]

theorem symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_natural_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    (symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz ≫
        symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom z) q =
      (symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom f ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom g) q := by
  simpa using
    congrArg (fun m => m q)
      (symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_natural_comp
        (f := f) (g := g) (hxy := hxy) (hyz := hyz))

end InfoGeometry.Topology
