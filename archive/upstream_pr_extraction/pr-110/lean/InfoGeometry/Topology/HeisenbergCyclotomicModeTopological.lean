import Mathlib
import InfoGeometry.Canonical.HeisenbergCyclotomicModeBridge

/-!
# Topological readout for the Heisenberg cyclotomic mode bridge

This file packages the existing integer-mode-to-`ZMod 3` degree readout as a
topological map.  The source and target already carry discrete topologies in
mathlib, so continuity and local constancy are bookkeeping consequences of the
algebraic mode-degree skeleton.
-/

namespace InfoGeometry.Topology.HeisenbergCyclotomicModeTopological

open InfoGeometry.Canonical

noncomputable section

/-- The cyclotomic degree of a Heisenberg mode, viewed as a topological map. -/
def topologicalHeisenbergModeDegree (k : ℤ) : ZMod 3 :=
  heisenbergModeDegree k

@[simp] theorem topologicalHeisenbergModeDegree_eq (k : ℤ) :
    topologicalHeisenbergModeDegree k = heisenbergModeDegree k := by
  rfl

/-- The cyclotomic degree readout is continuous on the discrete domain. -/
theorem continuous_topologicalHeisenbergModeDegree :
    Continuous topologicalHeisenbergModeDegree := by
  simpa [topologicalHeisenbergModeDegree] using
    (continuous_of_discreteTopology :
      Continuous topologicalHeisenbergModeDegree)

/-- The cyclotomic degree readout is locally constant on the discrete domain. -/
theorem isLocallyConstant_topologicalHeisenbergModeDegree :
    IsLocallyConstant topologicalHeisenbergModeDegree := by
  simpa [topologicalHeisenbergModeDegree] using
    (IsLocallyConstant.of_discrete (f := topologicalHeisenbergModeDegree))

end
end InfoGeometry.Topology.HeisenbergCyclotomicModeTopological
