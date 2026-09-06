import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import InfoGeometry.Canonical.YangianCoproductTensorAction

namespace InfoGeometry.Topology

open InfoGeometry.Canonical
open scoped TensorProduct

/-!
# Topological invariant loci for the Hopf-action owner

The canonical Hopf owner provides an abstract action and a counit-relative
invariance predicate.  Here we prove the independent topological fact that a
continuous family of such equations has a closed solution locus.  The
coproduct class field is not reinterpreted as a proved Yangian theorem.
-/

variable {K H V : Type*}
  [CommRing K] [CommRing H] [Algebra K H]
  [AddCommGroup V] [Module K V]

/-- The simultaneous counit-invariant locus of a Hopf representation. -/
def hopfInvariantLocus
    (ρ : HopfRepresentation K H V) (ε : H →ₗ[K] K) : Set V :=
  {v | IsHopfInvariant ρ ε v}

/-- Continuity makes the simultaneous Hopf-invariant locus closed. -/
theorem isClosed_hopfInvariantLocus
    [TopologicalSpace K] [TopologicalSpace V] [T2Space V]
    [ContinuousSMul K V]
    (ρ : HopfRepresentation K H V) (ε : H →ₗ[K] K)
    (hcont : ∀ y : H, Continuous (ρ.action y)) :
    IsClosed (hopfInvariantLocus ρ ε) := by
  rw [show hopfInvariantLocus ρ ε =
      ⋂ y : H, {v : V | ρ.action y v = (ε y) • v} by
    ext v
    simp [hopfInvariantLocus, IsHopfInvariant]]
  exact isClosed_iInter (fun y =>
    isClosed_eq (hcont y) (continuous_const.smul continuous_id))

/-- The tensor coproduct owner supplies pure invariant tensors in its locus. -/
def hopfTensorInvariantLocus
    {W : Type*} [AddCommGroup W] [Module K W]
    (ρV : HopfRepresentation K H V)
    (ρW : HopfRepresentation K H W)
    (ε : H →ₗ[K] K)
    [HopfCoproductTensorAction ρV ρW ε] : Set (V ⊗[K] W) :=
  {z | IsHopfInvariant (HopfCoproductTensorAction.tensorAction ρV ρW ε) ε z}

theorem pureTensor_mem_hopfTensorInvariantLocus
    {W : Type*} [AddCommGroup W] [Module K W]
    (ρV : HopfRepresentation K H V)
    (ρW : HopfRepresentation K H W)
    (ε : H →ₗ[K] K)
    [HopfCoproductTensorAction ρV ρW ε]
    (v : V) (w : W)
    (hV : IsHopfInvariant ρV ε v)
    (hW : IsHopfInvariant ρW ε w) :
    v ⊗ₜ[K] w ∈ hopfTensorInvariantLocus ρV ρW ε := by
  change IsHopfInvariant (HopfCoproductTensorAction.tensorAction ρV ρW ε)
    ε (v ⊗ₜ[K] w)
  exact gluing_preserves_invariance v w hV hW

end InfoGeometry.Topology
