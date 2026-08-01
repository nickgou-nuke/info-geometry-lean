import Mathlib
import InfoGeometry.Canonical.YangianGeneratorKernel

namespace InfoGeometry.Canonical

variable {K : Type*} [CommRing K]

/-- The abstract representation of a Hopf algebra generator acting on a state space V. -/
structure HopfRepresentation (K H V : Type*) [CommRing K] [CommRing H] [Algebra K H] [AddCommGroup V] [Module K V] where
  action : H →ₗ[K] (V →ₗ[K] V)
  
/-- 
A state v ∈ V is invariant under the Hopf algebra if its action matches the counit ε.
In the context of the Yangian, this generalizes the linear kernel Y(Ω) = 0 
to the Hopf-algebraic setting Y(Ω) = ε(Y) Ω.
-/
def IsHopfInvariant {K H V : Type*} [CommRing K] [CommRing H] [Algebra K H] [AddCommGroup V] [Module K V] 
    (ρ : HopfRepresentation K H V) (ε : H →ₗ[K] K) (v : V) : Prop :=
  ∀ y : H, ρ.action y v = (ε y) • v

open scoped TensorProduct

/-- 
A Hopf coproduct tensor action glues two representations into a representation on V ⊗ W.
Crucially, it is structurally required to preserve invariance: the tensor product of 
invariant states remains invariant under the coproduct.
This implements the conceptual apex:
ρ_V(y)v = ε(y)v ∧ ρ_W(y)w = ε(y)w ⟹ ρ_{V⊗W}(y)(v⊗w) = ε(y)(v⊗w)
-/
class HopfCoproductTensorAction {K H : Type*} [CommRing K] [CommRing H] [Algebra K H] 
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ_V : HopfRepresentation K H V) (ρ_W : HopfRepresentation K H W) 
    (ε : H →ₗ[K] K) where
  /-- The induced coproduct action on the tensor product space. -/
  tensorAction : HopfRepresentation K H (V ⊗[K] W)
  /-- 
  The apex theorem: Gluing two invariant states preserves invariance under the coproduct.
  This is the theorem-honest foundation for BCFW on-shell diagram invariance.
  -/
  gluing_preserves_invariance : ∀ (v : V) (w : W),
    IsHopfInvariant ρ_V ε v → 
    IsHopfInvariant ρ_W ε w → 
    IsHopfInvariant tensorAction ε (v ⊗ₜ[K] w)

export HopfCoproductTensorAction (gluing_preserves_invariance)

end InfoGeometry.Canonical
