import InfoGeometry.ErlangenLanglandsLane
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped BigOperators

noncomputable section

namespace InfoGeometry

/-- Canonical theorem-chain metadata for the noncommutative
Erlangen/Langlands lane. -/
structure RoadmapEdge where
  src : String
  dst : String
  theorem_name : String
  requires : List String

def erlangenLanglandsRoadmap : List RoadmapEdge := [
  { src := "InfoGeometry.Geometry.BilingualUpperHalfPlane",
    dst := "InfoGeometry.OperatorAlgebra.FiniteJonesOptics",
    theorem_name := "moebiusMap_K_positivity",
    requires := ["phase linearity", "K-compatibility"] },

  { src := "InfoGeometry.OperatorAlgebra.FiniteJonesOptics",
    dst := "InfoGeometry.OperatorAlgebra.FiniteJonesErlangerBridge",
    theorem_name := "brewsterCoreProjector_is_fixed_Erlanger_object",
    requires := ["det2_brewsterEvent_jones", "diagonal gauge data"] },

  { src := "InfoGeometry.OperatorAlgebra.FiniteJonesErlangerBridge",
    dst := "InfoGeometry.Automorphic.KreinBridge",
    theorem_name := "boundary/siegel-to-cuspidal transport (planned composition)",
    requires := ["Brewster projector invariance", "automorphic readout map"] },

  { src := "InfoGeometry.Automorphic.KreinBridge",
    dst := "InfoGeometry.Automorphic.LFunctionResonance",
    theorem_name := "cuspidalProjector_yields_PCuspidal",
    requires := ["cuspidality transport lemma"] },

  { src := "InfoGeometry.Automorphic.LFunctionResonance",
    dst := "InfoGeometry.Automorphic.ProjectedLFunction",
    theorem_name := "rawLFunction_eq_boundary_add_cuspidal",
    requires := ["projection data", "cuspidal projector compatibility"] },

  { src := "InfoGeometry.Automorphic.ProjectedLFunction",
    dst := "InfoGeometry.Automorphic.LanglandsSugawaraBridge",
    theorem_name := "euler_product_holds / completed_functional_equation_holds",
    requires := ["projected-euler witness", "completed functional-equation witness"] },

  { src := "InfoGeometry.Automorphic.LanglandsSugawaraBridge",
    dst := "InfoGeometry.Automorphic.LanglandsPrimeResonance",
    theorem_name := "central_zero_iff_L_zero",
    requires := ["central-readout bridge", "spectral zero calibration"] },

  { src := "InfoGeometry.Automorphic.LanglandsPrimeResonance",
    dst := "InfoGeometry.OperatorAlgebra.KapustinWittenDualitySocket",
    theorem_name := "bulk_central_zero_iff_prime_resonance",
    requires := ["bulk Siegel data", "central-zero stability"] },

  { src := "InfoGeometry.OperatorAlgebra.KapustinWittenDualitySocket",
    dst := "InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy",
    theorem_name := "wilsonEigen_transports_to_tHooftEigen",
    requires := ["S-duality witness", "operator readout compatibility"] },

  { src := "InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy",
    dst := "InfoGeometry.Canonical.KleinBottleOrientifold",
    theorem_name := "KMS/holonomy recovery payload",
    requires := ["dual-holonomy recovery", "memory-kernel witness"] }
]

/-!
Execution protocol:

1) Validate each source module's owner target.
2) Supply required witness instances at each W-edge.
3) Instantiate only S-edges in first pass; postpone W-edges until compatibility data are
   explicitly available.
-/

end InfoGeometry
