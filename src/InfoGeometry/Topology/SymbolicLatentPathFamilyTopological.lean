import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathFamily

/-!
# Topological boundary readout for symbolic latent path families

This owner packages the family of symbolic latent paths together with its
endpoint readout as a continuous map into the product of endpoint spaces.
It does not introduce any new algebraic structure on the latent carrier.
-/

namespace InfoGeometry.Topology

/-- The endpoint readout of a symbolic latent path family. -/
def symbolicLatentPathFamilyBoundaryMap
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) :
    C(P, X × X) :=
  ContinuousMap.prodMk F.startFamily F.finishFamily

@[simp] theorem symbolicLatentPathFamilyBoundaryMap_apply
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) (p : P) :
    symbolicLatentPathFamilyBoundaryMap F p =
      (F.startFamily p, F.finishFamily p) := by
  rfl

@[simp] theorem symbolicLatentPathFamilyBoundaryMap_fst
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) (p : P) :
    (symbolicLatentPathFamilyBoundaryMap F p).1 = F.startFamily p := by
  rfl

@[simp] theorem symbolicLatentPathFamilyBoundaryMap_snd
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) (p : P) :
    (symbolicLatentPathFamilyBoundaryMap F p).2 = F.finishFamily p := by
  rfl

/-- The boundary readout is continuous because it is a continuous map of
continuous maps. -/
theorem continuous_symbolicLatentPathFamilyBoundaryMap
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) :
    Continuous (symbolicLatentPathFamilyBoundaryMap F) :=
  (symbolicLatentPathFamilyBoundaryMap F).continuous

end InfoGeometry.Topology
