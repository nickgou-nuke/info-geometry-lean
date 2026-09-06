import Mathlib
import InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyBridge

/-!
# TopCat packaging for the Heisenberg sixth-root / cubic monodromy packet

This file packages the already verified sixth-root Heisenberg readout as a
discrete topological packet. The source is the parameter space
`𝕜 × SixthRootParameter`; the target is the combined boundary / cubic-root /
monodromy readout. No new algebraic identification is introduced.
-/

noncomputable section

namespace InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyTopCat

open CategoryTheory
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyBridge
open InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- A concrete packet storing the Heisenberg parameter and the induced
sixth-root / cubic-monodromy readout. -/
structure Packet where
  α : 𝕜
  q : SixthRootParameter
  heisenberg :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α
  cubicRoot : CubicRootParameter
  monodromy : ColourOperator

instance packetTopologicalSpace : TopologicalSpace (Packet (𝕜 := 𝕜)) := ⊥

instance packetDiscreteTopology : DiscreteTopology (Packet (𝕜 := 𝕜)) := ⟨rfl⟩

instance parameterTopologicalSpace :
    TopologicalSpace (𝕜 × SixthRootParameter) := ⊥

instance parameterDiscreteTopology :
    DiscreteTopology (𝕜 × SixthRootParameter) := ⟨rfl⟩

/-- The packet as a `TopCat` object. -/
def topCat : TopCat :=
  TopCat.of (Packet (𝕜 := 𝕜))

/-- The parameter space as a `TopCat` object. -/
def parameterTopCat : TopCat :=
  TopCat.of (𝕜 × SixthRootParameter)

/-- Projection from the packet back to its input parameter. -/
noncomputable def projection :
    topCat (𝕜 := 𝕜) ⟶ parameterTopCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  exact ⟨fun p : Packet (𝕜 := 𝕜) => (p.α, p.q),
    continuous_of_discreteTopology⟩

/-- Canonical section from parameters into the combined packet. -/
noncomputable def readout :
    parameterTopCat (𝕜 := 𝕜) ⟶ topCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  exact ⟨fun p : 𝕜 × SixthRootParameter =>
      ⟨p.1, p.2,
        heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) p.1 p.2 |>.1,
        heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) p.1 p.2 |>.2.1,
        heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) p.1 p.2 |>.2.2⟩,
      continuous_of_discreteTopology⟩

@[simp] theorem projection_readout :
    readout (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜) = 𝟙 _ := by
  apply TopCat.hom_ext
  ext p
  rfl

@[simp] theorem projection_readout_apply (p : 𝕜 × SixthRootParameter) :
    (readout (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜)) p = p := by
  rfl

end InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyTopCat
