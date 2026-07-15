/-
InfoGeometry/Compatibility/PSLDescentShadow.lean

Compatibility wrapper for the complex-backed projective descent file.

This is a shadow/readout layer only. The real substrate does not import it.
-/

import InfoGeometry.Canonical.PSLDescent

namespace InfoGeometry.Compatibility

abbrev PSLDescentContract := PSLDescent.PSLDescentContract

theorem pslDescentContract : PSLDescentContract :=
  PSLDescent.pslDescentContract

end InfoGeometry.Compatibility
