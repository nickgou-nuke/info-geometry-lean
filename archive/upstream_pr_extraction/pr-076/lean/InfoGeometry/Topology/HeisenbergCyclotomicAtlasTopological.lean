import Mathlib
import InfoGeometry.Canonical.HeisenbergCyclotomicAtlas

/-!
# Topological readout for the Heisenberg cyclotomic atlas

The cyclotomic parameter is the subtype of sixth roots of unity.  We equip
this parameter set with its discrete topology and then read the two fields
of the canonical atlas as genuine functions of that parameter.  No topology
is asserted on a value that is not a function.
-/

namespace InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological

open InfoGeometry.Canonical

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The parameter set for the cyclotomic sixth-root lane. -/
def SixthRootParameter :=
  {p : ℂˣ // (p : ℂ) ^ 6 = 1}

instance sixthRootParameterTopologicalSpace :
    TopologicalSpace SixthRootParameter := ⊥

instance sixthRootParameterDiscreteTopology :
    DiscreteTopology SixthRootParameter := ⟨rfl⟩

instance heisenbergBoundaryAtlasTopologicalSpace (α : 𝕜) :
    TopologicalSpace
      (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α) := ⊥

/-- Heisenberg boundary field of the canonical atlas, as a parameter readout. -/
def heisenbergBoundaryAtlasReadout (α : 𝕜) (q : SixthRootParameter) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α :=
  (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
      (𝕜 := 𝕜) α q.1 q.2).heisenberg

/-- Cyclotomic root field of the canonical atlas, as a parameter readout. -/
def heisenbergCyclotomicRootReadout (α : 𝕜) (q : SixthRootParameter) : ℂˣ :=
  (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
      (𝕜 := 𝕜) α q.1 q.2).sixthRoot

@[simp] theorem heisenbergBoundaryAtlasReadout_apply
    (α : 𝕜) (q : SixthRootParameter) :
    heisenbergBoundaryAtlasReadout α q =
      (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
          (𝕜 := 𝕜) α q.1 q.2).heisenberg := by
  rfl

@[simp] theorem heisenbergCyclotomicRootReadout_apply
    (α : 𝕜) (q : SixthRootParameter) :
    heisenbergCyclotomicRootReadout α q =
      (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
          (𝕜 := 𝕜) α q.1 q.2).sixthRoot := by
  rfl

/-- The Heisenberg boundary readout is continuous on the discrete parameter set. -/
theorem continuous_heisenbergBoundaryAtlasReadout (α : 𝕜) :
    Continuous (heisenbergBoundaryAtlasReadout α) := by
  simpa [heisenbergBoundaryAtlasReadout] using
    (continuous_of_discreteTopology :
      Continuous (heisenbergBoundaryAtlasReadout α))

/-- The cyclotomic-root readout is continuous on the discrete parameter set. -/
theorem continuous_heisenbergCyclotomicRootReadout (α : 𝕜) :
    Continuous (heisenbergCyclotomicRootReadout α) := by
  simpa [heisenbergCyclotomicRootReadout] using
    (continuous_of_discreteTopology :
      Continuous (heisenbergCyclotomicRootReadout α))

/-- Both atlas readouts are locally constant. -/
theorem isLocallyConstant_heisenbergBoundaryAtlasReadout (α : 𝕜) :
    IsLocallyConstant (heisenbergBoundaryAtlasReadout α) := by
  simpa [heisenbergBoundaryAtlasReadout] using
    (IsLocallyConstant.of_discrete (f := heisenbergBoundaryAtlasReadout α))

theorem isLocallyConstant_heisenbergCyclotomicRootReadout (α : 𝕜) :
    IsLocallyConstant (heisenbergCyclotomicRootReadout α) := by
  simpa [heisenbergCyclotomicRootReadout] using
    (IsLocallyConstant.of_discrete (f := heisenbergCyclotomicRootReadout α))

end
end InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
