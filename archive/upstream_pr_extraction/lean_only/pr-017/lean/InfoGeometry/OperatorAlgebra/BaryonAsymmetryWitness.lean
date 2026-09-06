/-
InfoGeometry/OperatorAlgebra/BaryonAsymmetryWitness.lean

Witness-gated baryon-asymmetry accounting.

This module does not derive baryogenesis. It records an optional model in which
an asymmetry readout is related to a condensate-transfer readout.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.AndreevBoundary

noncomputable section

namespace InfoGeometry.OperatorAlgebra.BaryonAsymmetryWitness

open InfoGeometry.OperatorAlgebra.AndreevBoundary

/--
Baryon-asymmetry accounting witness.

This is not a baryogenesis theorem. A physical baryogenesis model must also
supply the relevant violation/out-of-equilibrium witnesses.
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

  /-- Baryon-number violation witness. -/
  baryon_number_violation_law : Prop

  /-- C/CP violation witness. -/
  cp_violation_law : Prop

  /-- Out-of-equilibrium witness. -/
  out_of_equilibrium_law : Prop

  /-- Proof/certificate of baryon-number violation. -/
  baryon_number_violation_certificate :
    baryon_number_violation_law

  /-- Proof/certificate of CP violation. -/
  cp_violation_certificate :
    cp_violation_law

  /-- Proof/certificate of departure from equilibrium. -/
  out_of_equilibrium_certificate :
    out_of_equilibrium_law

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

/-- Baryon-number violation certificate is available. -/
theorem baryon_number_violation_valid :
    B.baryon_number_violation_law :=
  B.baryon_number_violation_certificate

/-- CP-violation certificate is available. -/
theorem cp_violation_valid :
    B.cp_violation_law :=
  B.cp_violation_certificate

/-- Out-of-equilibrium certificate is available. -/
theorem out_of_equilibrium_valid :
    B.out_of_equilibrium_law :=
  B.out_of_equilibrium_certificate

end BaryonAsymmetryAccounting

end InfoGeometry.OperatorAlgebra.BaryonAsymmetryWitness
