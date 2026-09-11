import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathConcatenationImage
import InfoGeometry.Topology.SymbolicLatentPathConcatenationNaturality
import InfoGeometry.Topology.SymbolicLatentPath
import InfoGeometry.Topology.SymbolicLatentPathImage

namespace InfoGeometry.Topology

/-!
# Observation images of canonical concatenations

The generic image-coverage theorem descends through a continuous observation
map.  Thus an observed concatenation has exactly the union of the observed
images of its two latent halves.
-/

theorem observedSymbolicLatentPathImage_canonicalSymbolicConcatenation_range_eq_union
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    observedSymbolicLatentPathImage S
        (canonicalSymbolicConcatenation hend) =
      observedSymbolicLatentPathImage S γ₀ ∪
        observedSymbolicLatentPathImage S γ₁ := by
  let f : X → (ι → ℝ) := symbolicObservationMap S
  have hf : Continuous f := continuous_symbolicObservationMap S
  let γ₀' := mapSymbolicLatentPathContinuous f hf γ₀
  let γ₁' := mapSymbolicLatentPathContinuous f hf γ₁
  have hend' : γ₀'.finish = γ₁'.start := by
    change f γ₀.finish = f γ₁.start
    exact congrArg f hend
  have hmap := mapSymbolicLatentPathContinuous_canonicalSymbolicConcatenation
    f hf hend hend'
  change Set.range
      (mapSymbolicLatentPathContinuous f hf
        (canonicalSymbolicConcatenation hend)) =
    Set.range γ₀' ∪ Set.range γ₁'
  rw [hmap]
  exact canonicalSymbolicConcatenation_range_eq_union hend'

end InfoGeometry.Topology
