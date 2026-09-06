import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientChartBridge
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` readout of the observed path-homotopy quotient

The observation map already transports paths and homotopies through the
generic quotient construction.  This owner exposes that transport as a
categorical morphism and records compatibility with endpoint evaluation.
-/

def symbolicObservationPathHomotopyQuotientTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) ⟶
      TopCat.of (SymbolicLatentPathHomotopyQuotient
        (X := SymbolicFeatureSpace ι)) :=
  symbolicLatentPathHomotopyQuotientTopCatHom
    (symbolicObservationContinuousMap S)

theorem symbolicObservationPathHomotopyQuotientTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicObservationPathHomotopyQuotientTopCatHom S q =
      mapSymbolicObservationPathHomotopyQuotient S q :=
  rfl

theorem symbolicObservationPathHomotopyQuotientTopCatHom_endpoint_natural
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    symbolicObservationPathHomotopyQuotientTopCatHom S ≫
        symbolicLatentPathHomotopyEndpointTopCatHom =
      symbolicLatentPathHomotopyEndpointTopCatHom ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom
          (symbolicObservationContinuousMap S) := by
  exact symbolicLatentPathHomotopyEndpointTopCatHom_natural
    (symbolicObservationContinuousMap S)

theorem symbolicObservationContinuousMap_comp
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    (symbolicObservationContinuousMap T).comp
        ({ toFun := F.toFun, continuous_toFun := F.continuous_toFun } : C(X, Y)) =
      symbolicObservationContinuousMap S := by
  ext x i
  exact F.intertwines i x

theorem symbolicObservationPathHomotopyQuotientTopCatHom_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    symbolicLatentPathHomotopyQuotientTopCatHom
        ({ toFun := F.toFun, continuous_toFun := F.continuous_toFun } : C(X, Y)) ≫
        symbolicObservationPathHomotopyQuotientTopCatHom T =
      symbolicObservationPathHomotopyQuotientTopCatHom S := by
  calc
    symbolicLatentPathHomotopyQuotientTopCatHom
        ({ toFun := F.toFun, continuous_toFun := F.continuous_toFun } : C(X, Y)) ≫
        symbolicObservationPathHomotopyQuotientTopCatHom T =
      symbolicLatentPathHomotopyQuotientTopCatHom
        ({ toFun := F.toFun, continuous_toFun := F.continuous_toFun } : C(X, Y)) ≫
        symbolicLatentPathHomotopyQuotientTopCatHom
          (symbolicObservationContinuousMap T) := by
      rfl
    _ = symbolicLatentPathHomotopyQuotientTopCatHom
        ((symbolicObservationContinuousMap T).comp
          ({ toFun := F.toFun, continuous_toFun := F.continuous_toFun } : C(X, Y))) := by
      symm
      exact symbolicLatentPathHomotopyQuotientTopCatHom_comp
        ({ toFun := F.toFun, continuous_toFun := F.continuous_toFun } : C(X, Y))
        (symbolicObservationContinuousMap T)
    _ = symbolicObservationPathHomotopyQuotientTopCatHom S := by
      simp [symbolicObservationPathHomotopyQuotientTopCatHom,
        symbolicObservationContinuousMap_comp F]

theorem symbolicObservationPathHomotopyQuotientTopCatHom_natural_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) :
    symbolicLatentPathHomotopyQuotientTopCatHom
        ({ toFun := (SymbolicLatentMorphism.comp g f).toFun,
           continuous_toFun := (SymbolicLatentMorphism.comp g f).continuous_toFun } :
          C(X, Z)) ≫
        symbolicObservationPathHomotopyQuotientTopCatHom U =
      symbolicObservationPathHomotopyQuotientTopCatHom S := by
  simpa [SymbolicLatentMorphism.comp] using
    symbolicObservationPathHomotopyQuotientTopCatHom_natural
      (SymbolicLatentMorphism.comp g f)

theorem symbolicObservationPathHomotopyQuotientTopCatHom_natural_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    (symbolicLatentPathHomotopyQuotientTopCatHom
        ({ toFun := (SymbolicLatentMorphism.comp g f).toFun,
           continuous_toFun := (SymbolicLatentMorphism.comp g f).continuous_toFun } :
          C(X, Z)) ≫
        symbolicObservationPathHomotopyQuotientTopCatHom U) q =
      symbolicObservationPathHomotopyQuotientTopCatHom S q := by
  have h :=
    congrArg (fun m => m q)
      (symbolicObservationPathHomotopyQuotientTopCatHom_natural_comp
        (g := g) (f := f))
  simp [SymbolicLatentMorphism.comp] at h ⊢
  exact h

end InfoGeometry.Topology
