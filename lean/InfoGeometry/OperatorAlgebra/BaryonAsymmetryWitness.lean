/-
InfoGeometry/OperatorAlgebra/BaryonAsymmetryWitness.lean

Baryon-asymmetry accounting.

This module does not derive baryogenesis. It records an optional model in which
an asymmetry readout is related to a condensate-transfer readout.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.AndreevBoundary

noncomputable section

namespace BaryonAsymmetryWitness

open InfoGeometry.OperatorAlgebra.AndreevBoundary

/--
Baryon-asymmetry accounting datum.

This is not a baryogenesis theorem. The structure stores only the algebraic
readout equality used below.
-/
structure BaryonAsymmetryAccounting
    (V Charge : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Charge] where
  ledger :
    AndreevChargeLedger V Charge

  /-- Asymmetry readout. -/
  asymmetry :
    Charge

  /--
  Supplied law relating asymmetry to condensate transfer.

  This is model-specific.
  -/
  asymmetry_eq_condensateTransfer :
    asymmetry = ledger.condensateTransfer

namespace BaryonAsymmetryAccounting

variable
    {V Charge : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Charge]

variable (B : BaryonAsymmetryAccounting V Charge)

/-- The asymmetry equals the installed condensate-transfer readout. -/
theorem asymmetry_eq_transfer :
    B.asymmetry = B.ledger.condensateTransfer :=
  B.asymmetry_eq_condensateTransfer

end BaryonAsymmetryAccounting

end BaryonAsymmetryWitness
