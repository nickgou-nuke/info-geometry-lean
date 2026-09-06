import Mathlib
import InfoGeometry.Topology.SymbolicLatentBasedLoopPathFunctoriality
import InfoGeometry.Topology.SymbolicLatentBasedLoopPathHomotopyQuotientTopCat
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientFunctoriality

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Naturality of the based-loop path quotient map

The canonical map from based-loop paths to the endpoint fiber of the homotopy
quotient commutes with transport along a continuous map of ambient spaces.
This is a TopCat square, not a claim of quotient-level loop composition.
-/

theorem symbolicLatentBasedLoopPathHomotopyQuotientMap_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (γ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentBasedLoopPathHomotopyQuotientMap
        (mapSymbolicLatentBasedLoopPath f hxy γ) =
      mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
        (symbolicLatentBasedLoopPathHomotopyQuotientMap γ) := by
  apply Subtype.ext
  rfl

theorem symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y) :
    symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
        (X := X) (x := x) ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy =
      symbolicLatentBasedLoopPathTopCatHom f hxy ≫
        symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
          (X := Y) (x := y) := by
  ext γ
  simpa [symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom,
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom,
    symbolicLatentBasedLoopPathTopCatHom] using
    congrArg (fun q => q.1)
      (symbolicLatentBasedLoopPathHomotopyQuotientMap_natural f hxy γ).symm

theorem symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom_natural_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z) :
    symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
        (X := X) (x := x) ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz =
      symbolicLatentBasedLoopPathTopCatHom (g.comp f)
        ((congrArg g hxy).trans hyz) ≫
        symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
          (X := Z) (x := z) := by
  calc
    symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
        (X := X) (x := x) ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz
        =
      (symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
          (X := X) (x := x) ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy) ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz := by
          rw [← Category.assoc]
    _ =
      (symbolicLatentBasedLoopPathTopCatHom f hxy ≫
        symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
          (X := Y) (x := y)) ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz := by
          rw [symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom_natural f hxy]
    _ =
      symbolicLatentBasedLoopPathTopCatHom f hxy ≫
        (symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
          (X := Y) (x := y) ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz) := by
          rw [Category.assoc]
    _ =
      symbolicLatentBasedLoopPathTopCatHom f hxy ≫
        (symbolicLatentBasedLoopPathTopCatHom g hyz ≫
          symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
            (X := Z) (x := z)) := by
          rw [symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom_natural g hyz]
    _ =
      (symbolicLatentBasedLoopPathTopCatHom f hxy ≫
        symbolicLatentBasedLoopPathTopCatHom g hyz) ≫
        symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
          (X := Z) (x := z) := by
          rw [← Category.assoc]
    _ =
      symbolicLatentBasedLoopPathTopCatHom (g.comp f)
        ((congrArg g hxy).trans hyz) ≫
        symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
          (X := Z) (x := z) := by
          rw [symbolicLatentBasedLoopPathTopCatHom_comp f g hxy hyz]

theorem symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom_natural_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (γ : SymbolicLatentBasedLoopPath x) :
    (symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
        (X := X) (x := x) ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz) γ =
      (symbolicLatentBasedLoopPathTopCatHom (g.comp f)
        ((congrArg g hxy).trans hyz) ≫
        symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
          (X := Z) (x := z)) γ := by
  exact congrArg (fun m => m γ)
    (symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom_natural_comp
      (f := f) (g := g) (hxy := hxy) (hyz := hyz))

theorem symbolicLatentBasedLoopHomotopyQuotient_endpoint_transport
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentPathHomotopyEndpointMap
        (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q) =
      mapSymbolicLatentPathHomotopyEndpoint f
        (symbolicLatentPathHomotopyEndpointMap q) := by
  cases q with
  | mk q hq =>
      simpa [mapSymbolicLatentBasedLoopHomotopyQuotient] using
        mapSymbolicLatentPathHomotopyQuotient_endpoint f q

theorem symbolicLatentBasedLoopPathHomotopyQuotientMap_endpoint_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (γ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentPathHomotopyEndpointMap
        (mapSymbolicLatentBasedLoopHomotopyQuotient g hyz
          (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
            (symbolicLatentBasedLoopPathHomotopyQuotientMap γ))) =
      mapSymbolicLatentPathHomotopyEndpoint g
        (mapSymbolicLatentPathHomotopyEndpoint f
          (symbolicLatentPathHomotopyEndpointMap
            (symbolicLatentBasedLoopPathHomotopyQuotientMap γ))) := by
  rw [symbolicLatentBasedLoopHomotopyQuotient_endpoint_transport g hyz
      (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
        (symbolicLatentBasedLoopPathHomotopyQuotientMap γ))]
  rw [symbolicLatentBasedLoopHomotopyQuotient_endpoint_transport f hxy
      (symbolicLatentBasedLoopPathHomotopyQuotientMap γ)]

end InfoGeometry.Topology
