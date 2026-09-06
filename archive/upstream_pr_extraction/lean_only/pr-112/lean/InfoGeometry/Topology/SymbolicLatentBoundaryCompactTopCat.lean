import InfoGeometry.Topology.SymbolicLatentBoundaryReadoutInverseLimitTopCat

/-!
# Compact/Hausdorff transport for the symbolic-latent boundary limit

The inverse-limit owner identifies the sequence-space boundary with the native
`TopCat` limit.  This file transports the standard product-space separation and
compactness properties across that homeomorphism.  No extra point-set topology
is chosen for the limit object.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits
open NaryTreeBoundaryInverseLimit

universe u

variable {A : Type u} [TopologicalSpace A]

/- The sequence-space boundary inherits these properties from the alphabet. -/
instance boundaryCompactSpace [CompactSpace A] :
    CompactSpace (Boundary (A := A)) := Function.compactSpace

instance boundaryT2Space [T2Space A] :
    T2Space (Boundary (A := A)) := by
  letI : ∀ _ : ℕ, T2Space A := fun _ => inferInstance
  exact Pi.t2Space

/- Transport the properties to the actual categorical inverse-limit object. -/
instance prefixLimitCompactSpace [CompactSpace A] :
    CompactSpace ((CategoryTheory.Limits.limit (prefixDiagram (A := A)) : TopCat) : Type u) := by
  letI : CompactSpace (↑(prefixCone (A := A)).pt) := by
    change CompactSpace (Boundary (A := A))
    infer_instance
  exact (TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A))).compactSpace

instance prefixLimitT2Space [T2Space A] :
    T2Space ((CategoryTheory.Limits.limit (prefixDiagram (A := A)) : TopCat) : Type u) := by
  letI : T2Space (↑(prefixCone (A := A)).pt) := by
    change T2Space (Boundary (A := A))
    infer_instance
  exact (TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A))).t2Space

theorem prefixLimit_isCompact [CompactSpace A] :
    IsCompact (Set.univ : Set ((CategoryTheory.Limits.limit (prefixDiagram (A := A)) : TopCat) : Type u)) :=
  isCompact_univ

theorem prefixLimit_isClosed_univ [CompactSpace A] [T2Space A] :
    IsClosed (Set.univ : Set ((CategoryTheory.Limits.limit (prefixDiagram (A := A)) : TopCat) : Type u)) :=
  isClosed_univ

end InfoGeometry.Topology
