import InfoGeometry.ErlangenLanglandsLane
import InfoGeometry.ErlangenLanglandsGeometryLane
import InfoGeometry.ErlangenLanglandsGromovEntry
import InfoGeometry.ErlangenLanglandsChecks
import InfoGeometry.ErlangenLanglandsRoadmap
import InfoGeometry.ErlangenLanglandsOwners

/-!
Single entrypoint for the Operator-Erlangen / Langlands lane.

Import this file when you want one stable module for:
* dependency spine (`ErlangenLanglandsLane`)
* geometry-augmented spine (`ErlangenLanglandsGeometryLane`)
* correspondence integration spine (`ErlangenLanglandsGromovEntry`)
* declaration availability checks (`ErlangenLanglandsChecks`)
* roadmap metadata (`ErlangenLanglandsRoadmap`)
* constructive owner pipeline (`ErlangenLanglandsOwners`)
-/

namespace InfoGeometry

namespace ErlangenLanglandsEntry

/-- Sentinel declaration confirming that the Erlangen–Langlands entrypoint loaded. -/
theorem loaded : True := by
  trivial

end ErlangenLanglandsEntry

end InfoGeometry
