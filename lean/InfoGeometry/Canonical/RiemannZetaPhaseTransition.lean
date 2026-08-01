import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace InfoGeometry.Canonical

/--
**Thermodynamic temperature split for the Bost-Connes readout**
This file records a simple threshold classifier at `β = 1`.
It does not assert a pole theorem or a global phase-transition classification.
-/
inductive ThermodynamicPhase
| Symmetric -- β < 1
| Broken    -- β ≥ 1

/--
The temperature classifier used by this file.
-/
noncomputable def determinePhase (β : ℝ) : ThermodynamicPhase :=
  if β < 1 then ThermodynamicPhase.Symmetric
  else ThermodynamicPhase.Broken

/--
The two cases `β < 1` and `β > 1` are disjoint.
-/
theorem strict_phase_separation (β : ℝ) (h_less : β < 1) (h_greater : β > 1) : False := by
  linarith

end InfoGeometry.Canonical
