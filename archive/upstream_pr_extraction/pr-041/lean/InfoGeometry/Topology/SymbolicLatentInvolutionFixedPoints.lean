import Mathlib
import InfoGeometry.Topology.SymbolicLatentModularFlow

namespace InfoGeometry.Topology

/-!
Fixed-point geometry for continuous latent involutions.  The fixed set is an
equalizer, so it is closed in a Hausdorff latent space.
-/

def symbolicLatentInvolutionFixedPointSet
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) : Set X :=
  {x | J x = x}

theorem mem_symbolicLatentInvolutionFixedPointSet
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) (x : X) :
    x ∈ symbolicLatentInvolutionFixedPointSet J ↔ J x = x :=
  Iff.rfl

theorem isClosed_symbolicLatentInvolutionFixedPointSet
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (J : SymbolicLatentInvolution X) :
    IsClosed (symbolicLatentInvolutionFixedPointSet J) := by
  exact isClosed_eq J.continuous continuous_id

theorem fixedPointSet_invariant_under_involution
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet J) :
    J x ∈ symbolicLatentInvolutionFixedPointSet J := by
  rw [mem_symbolicLatentInvolutionFixedPointSet] at hx ⊢
  rw [J.involutive, hx]

end InfoGeometry.Topology
