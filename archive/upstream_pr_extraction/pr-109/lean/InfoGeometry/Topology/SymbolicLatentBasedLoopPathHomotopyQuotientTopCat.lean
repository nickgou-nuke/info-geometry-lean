import Mathlib
import InfoGeometry.Topology.SymbolicLatentBasedLoopPath
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotient
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` bridge from based-loop paths to the based-loop homotopy quotient

This owner records the canonical quotient map from a based loop path to its
homotopy-quotient fiber over `(x, x)`, together with the induced topological
`TopCat` morphism.  It does not assert any new loop-group structure.
-/

def symbolicLatentBasedLoopPathHomotopyQuotientMap
    {X : Type} [TopologicalSpace X] {x : X} :
    SymbolicLatentBasedLoopPath x →
      SymbolicLatentBasedLoopHomotopyQuotient (X := X) x :=
  fun γ =>
    ⟨symbolicLatentPathHomotopyQuotientMap γ.1, by
      rw [symbolicLatentPathHomotopyEndpointMap_mk]
      rcases γ.2 with ⟨hstart, hfinish⟩
      simp [SymbolicLatentPath.endpoints, hstart, hfinish]⟩

theorem symbolicLatentBasedLoopPathHomotopyQuotientMap_apply
    {X : Type} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    (symbolicLatentBasedLoopPathHomotopyQuotientMap (X := X) (x := x) γ).1 =
      symbolicLatentPathHomotopyQuotientMap γ.1 :=
  rfl

theorem symbolicLatentBasedLoopPathHomotopyQuotientMap_endpoint
    {X : Type} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentPathHomotopyEndpointMap
        (symbolicLatentBasedLoopPathHomotopyQuotientMap (X := X) (x := x) γ) = (x, x) :=
  (symbolicLatentBasedLoopPathHomotopyQuotientMap (X := X) (x := x) γ).2

theorem continuous_symbolicLatentBasedLoopPathHomotopyQuotientMap
    {X : Type} [TopologicalSpace X] {x : X} :
    Continuous (symbolicLatentBasedLoopPathHomotopyQuotientMap (X := X) (x := x)) := by
  have hq : Continuous (symbolicLatentPathHomotopyQuotientMap (X := X)) :=
    @continuous_quotient_mk' (SymbolicLatentPath X) _
      (symbolicLatentPathHomotopySetoid (X := X))
  exact hq.comp continuous_subtype_val |>.subtype_mk
    (fun γ => by
      change symbolicLatentPathHomotopyEndpointMap
        (symbolicLatentPathHomotopyQuotientMap γ.1) = (x, x)
      rw [symbolicLatentPathHomotopyEndpointMap_mk]
      rcases γ.2 with ⟨hstart, hfinish⟩
      simp [SymbolicLatentPath.endpoints, hstart, hfinish])

def symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom
    {X : Type} [TopologicalSpace X] {x : X} :
    TopCat.of (SymbolicLatentBasedLoopPath x) ⟶
      TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient (X := X) x) :=
  TopCat.ofHom
    { toFun := symbolicLatentBasedLoopPathHomotopyQuotientMap (X := X) (x := x)
      continuous_toFun :=
        continuous_symbolicLatentBasedLoopPathHomotopyQuotientMap (X := X) (x := x) }

theorem symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom_apply
    {X : Type} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom (X := X) (x := x) γ =
      symbolicLatentBasedLoopPathHomotopyQuotientMap (X := X) (x := x) γ :=
  rfl

def symbolicLatentBasedLoopPathEndpointConstantTopCatHom
    {X : Type} [TopologicalSpace X] (x : X) :
    TopCat.of (SymbolicLatentBasedLoopPath x) ⟶
      TopCat.of (X × X) :=
  TopCat.ofHom
    { toFun := fun _ => (x, x)
      continuous_toFun := continuous_const }

theorem symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom_endpoint_factorization
    {X : Type} [TopologicalSpace X] {x : X} :
    symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom (X := X) (x := x) ≫
        symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom (X := X) x =
      symbolicLatentBasedLoopPathEndpointConstantTopCatHom x := by
  apply TopCat.hom_ext
  ext γ
  · simpa [symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom,
      symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom,
      symbolicLatentBasedLoopPathEndpointConstantTopCatHom] using
      congrArg Prod.fst (symbolicLatentBasedLoopPathHomotopyQuotientMap_endpoint γ)
  · simpa [symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom,
      symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom,
      symbolicLatentBasedLoopPathEndpointConstantTopCatHom] using
      congrArg Prod.snd (symbolicLatentBasedLoopPathHomotopyQuotientMap_endpoint γ)

theorem symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom_endpoint_factorization_unique
    {X : Type} [TopologicalSpace X] {x : X}
    {u : TopCat.of (SymbolicLatentBasedLoopPath x) ⟶ TopCat.of (X × X)}
    (hu : symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom (X := X) (x := x) ≫
        symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom (X := X) x = u) :
    u = symbolicLatentBasedLoopPathEndpointConstantTopCatHom x := by
  simpa [symbolicLatentBasedLoopPathHomotopyQuotientTopCatHom_endpoint_factorization]
    using hu.symm

end InfoGeometry.Topology
