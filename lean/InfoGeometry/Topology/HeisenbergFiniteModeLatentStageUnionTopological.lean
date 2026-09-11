import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological

/-!
# Clopen stage exhaustion of Heisenberg latent labels

Finite mode stages produce finite subsets of the cyclotomic latent quotient.
This owner turns them into a monotone system of clopen subsets and proves
that their union is exactly the range of all basis-index latent labels.  It
is the set-level shadow of the finite-mode colimit, with no completion claim.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeLatentStageUnionTopological

open InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicLatentQuotientTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The latent subset visible at a finite mode stage. -/
def heisenbergFiniteModeStageLatentSet
    (q : SixthRootParameter) (s : Finset (Option ℤ)) :
    Set LatentQuotient :=
  ↑(heisenbergFiniteModeStageLatentImage q s)

/-- Every finite-stage latent set is clopen in the discrete quotient chart. -/
theorem isClopen_heisenbergFiniteModeStageLatentSet
    (q : SixthRootParameter) (s : Finset (Option ℤ)) :
    IsClopen (heisenbergFiniteModeStageLatentSet q s) := by
  exact isClopen_discrete _

theorem heisenbergFiniteModeStageLatentSet_mono
    (q : SixthRootParameter) {s t : Finset (Option ℤ)} (hst : s ⊆ t) :
    heisenbergFiniteModeStageLatentSet q s ⊆
      heisenbergFiniteModeStageLatentSet q t := by
  intro z hz
  exact heisenbergFiniteModeStageLatentImage_mono q hst hz

/-- The union over all finite stages is the full range of basis-index labels. -/
theorem iUnion_heisenbergFiniteModeStageLatentSet
    (q : SixthRootParameter) :
    (⋃ s : Finset (Option ℤ), heisenbergFiniteModeStageLatentSet q s) =
      Set.range (fun i : Option ℤ =>
        heisenbergFiniteModeLatentReadout (q, i)) := by
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨s, hz⟩
    change z ∈ heisenbergFiniteModeStageLatentImage q s at hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, hzi⟩
    exact ⟨i, hzi⟩
  · intro hz
    rcases hz with ⟨i, rfl⟩
    refine Set.mem_iUnion.mpr ⟨{i}, ?_⟩
    change heisenbergFiniteModeLatentReadout (q, i) ∈
      heisenbergFiniteModeStageLatentImage q {i}
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

end
end InfoGeometry.Topology.HeisenbergFiniteModeLatentStageUnionTopological
