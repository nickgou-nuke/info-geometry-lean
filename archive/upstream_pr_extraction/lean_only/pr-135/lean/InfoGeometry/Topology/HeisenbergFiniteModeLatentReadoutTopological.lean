import Mathlib
import InfoGeometry.Topology.HeisenbergFiniteModeCyclotomicTopological
import InfoGeometry.Topology.CyclotomicLatentQuotientTopological

/-!
# Stage-wise latent readout for finite Heisenberg modes

This owner sends a finite Heisenberg basis index to the existing cyclotomic
latent quotient.  The root coordinate is supplied externally, while the
first Weyl residue records the order-three mode degree and the second residue
is fixed at zero.  The construction is a label map on basis indices, not a
claim that arbitrary Heisenberg linear combinations have a single latent
coordinate.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological

open InfoGeometry.Topology.HeisenbergFiniteModeCyclotomicTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicLatentQuotientTopological

noncomputable section

/-- Latent label of a Heisenberg basis index at a chosen sixth-root parameter. -/
def heisenbergFiniteModeLatentReadout
    (p : SixthRootParameter × Option ℤ) : LatentQuotient :=
  (effectiveCubeRootParameter p.1,
    (heisenbergBasisCyclotomicDegree p.2, 0))

@[simp] theorem heisenbergFiniteModeLatentReadout_root
    (p : SixthRootParameter × Option ℤ) :
    (heisenbergFiniteModeLatentReadout p).1 =
      effectiveCubeRootParameter p.1 := by
  rfl

@[simp] theorem heisenbergFiniteModeLatentReadout_degree
    (p : SixthRootParameter × Option ℤ) :
    (heisenbergFiniteModeLatentReadout p).2.1 =
      heisenbergBasisCyclotomicDegree p.2 := by
  rfl

@[simp] theorem heisenbergFiniteModeLatentReadout_zero_residue
    (p : SixthRootParameter × Option ℤ) :
    (heisenbergFiniteModeLatentReadout p).2.2 = 0 := by
  rfl

theorem continuous_heisenbergFiniteModeLatentReadout :
    Continuous heisenbergFiniteModeLatentReadout := by
  exact continuous_of_discreteTopology

theorem isLocallyConstant_heisenbergFiniteModeLatentReadout :
    IsLocallyConstant heisenbergFiniteModeLatentReadout := by
  exact IsLocallyConstant.of_discrete
    (f := heisenbergFiniteModeLatentReadout)

/-- Latent labels visible from a finite mode stage at a fixed root parameter. -/
def heisenbergFiniteModeStageLatentImage
    (q : SixthRootParameter) (s : Finset (Option ℤ)) :
    Finset LatentQuotient :=
  s.image (fun i => heisenbergFiniteModeLatentReadout (q, i))

theorem heisenbergFiniteModeStageLatentImage_mono
    (q : SixthRootParameter) {s t : Finset (Option ℤ)} (hst : s ⊆ t) :
    heisenbergFiniteModeStageLatentImage q s ⊆
      heisenbergFiniteModeStageLatentImage q t := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
  exact Finset.mem_image.mpr ⟨i, hst hi, rfl⟩

theorem heisenbergFiniteModeStageLatentImage_degree_mem
    (q : SixthRootParameter) (s : Finset (Option ℤ))
    (i : Option ℤ) (hi : i ∈ s) :
    (heisenbergFiniteModeLatentReadout (q, i)).2.1 ∈
      (heisenbergFiniteModeStageLatentImage q s).image (fun z => z.2.1) := by
  exact Finset.mem_image.mpr ⟨heisenbergFiniteModeLatentReadout (q, i),
    Finset.mem_image.mpr ⟨i, hi, rfl⟩, rfl⟩

end
end InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological
