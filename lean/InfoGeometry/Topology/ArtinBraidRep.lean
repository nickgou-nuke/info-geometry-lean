
import Mathlib.Algebra.Module.LinearMap.Basic

namespace InfoGeometry.Topology.ArtinBraid

/-- 
Explicit architecture isolating the Artin Braid Representation over a module.
Certifies the infinite braid transpositions acting on vector spaces. 
-/
structure ArtinBraidRep (K V : Type*) [CommRing K] [AddCommGroup V] [Module K V] where
  sigma : ℕ → (V →ₗ[K] V)
  braid_adjacent :
    ∀ i, sigma i ∘ₗ sigma (i+1) ∘ₗ sigma i =
         sigma (i+1) ∘ₗ sigma i ∘ₗ sigma (i+1)
  braid_far :
    ∀ i j, i + 1 < j →
      sigma i ∘ₗ sigma j = sigma j ∘ₗ sigma i

end InfoGeometry.Topology.ArtinBraid
