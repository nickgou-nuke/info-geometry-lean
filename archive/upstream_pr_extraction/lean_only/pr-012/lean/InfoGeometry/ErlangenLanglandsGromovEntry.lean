import InfoGeometry.ErlangenLanglandsLane
import InfoGeometry.ErlangenLanglandsGeometryLane
import InfoGeometry.GromovWittenProjectiveLane
import InfoGeometry.GromovWittenErlangen.Entry
import InfoGeometry.LanglandsGWBridge
import InfoGeometry.GromovHomologicalProbabilityRoadmap
import InfoGeometry.ModularVolumePotential

/-!
Entry point for the Erlangen–Langlands–Gromov correspondence layer.

Import this module when code needs the projective/GW/quantum-metric integration
lenses alongside the arithmetic and geometric lane constructors.
-/

namespace InfoGeometry

namespace ErlangenLanglandsGromovEntry

/-- Sentinel declaration confirming the integration entrypoint loaded. -/
theorem loaded : True := by
  trivial

end ErlangenLanglandsGromovEntry

end InfoGeometry
