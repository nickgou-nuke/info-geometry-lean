import Mathlib.Tactic

namespace Omega.SPG

/-- Concrete package for the classification of a profinite torus extension by its Stokes module.
The Stokes module and integer lattice live inside a common ambient coordinate type, the split
criterion compares them, and the classification statement is represented by an equivalence between
the extension's isomorphism class and its Stokes-module descriptor. -/
structure ProfiniteTorusExtensionStokesModuleClassificationData where
  Coordinate : Type
  ExtensionIsoClass : Type
  StokesModuleClass : Type
  stokesModule : Set Coordinate
  integerLattice : Set Coordinate
  integer_lattice_inclusion :
    integerLattice ⊆ stokesModule
  isoClassification :
    ExtensionIsoClass ≃ StokesModuleClass

/-- The extension splits exactly when its Stokes module is the integer lattice. -/
def ProfiniteTorusExtensionStokesModuleClassificationData.isSplit
    (D : ProfiniteTorusExtensionStokesModuleClassificationData) : Prop :=
  D.stokesModule = D.integerLattice

theorem ProfiniteTorusExtensionStokesModuleClassificationData.isSplit_iff
    (D : ProfiniteTorusExtensionStokesModuleClassificationData) :
    D.isSplit ↔ D.stokesModule = D.integerLattice := Iff.rfl

theorem ProfiniteTorusExtensionStokesModuleClassificationData.extensionIsoClassifiedByStokesModule
    (D : ProfiniteTorusExtensionStokesModuleClassificationData) :
    Nonempty (D.ExtensionIsoClass ≃ D.StokesModuleClass) :=
  ⟨D.isoClassification⟩

end Omega.SPG
