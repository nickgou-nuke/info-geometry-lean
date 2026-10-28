/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealDualTwistor
import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

/-!
# Genuine-dual incidence in the real split Clifford module

The existing ten-dimensional neutral carrier is definitionally
`V5 × Module.Dual ℝ V5`.  The new symmetric evaluation form is twice the
existing Clifford polarization.  Its zero-evaluation constraint is exactly
square-zero for the existing wedge-plus-contraction action on the full real
exterior spinor algebra.  This relates two actual operators on distinct
modules; it does not identify ordinary four-dimensional twistor space with
the higher-dimensional pure-spinor space.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealDualTwistorClifford

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Twistor.RealDualTwistor

/-- The normalization difference between the two existing evaluation forms. -/
theorem neutralForm_eq_two_mul_cliffordPairing (p q : NeutralSpace) :
    neutralForm p q = 2 * neutralPairing p q := by
  simp only [neutralForm_apply, neutralPairing]
  ring

/-- The exterior Clifford anticommutator is the symmetric evaluation form. -/
theorem neutralAction_anticommutator_eq_neutralForm (p q : NeutralSpace) :
    neutralAction p * neutralAction q + neutralAction q * neutralAction p =
      neutralForm p q • (1 : SpinorEnd) := by
  rw [neutralAction_anticommutator, neutralForm_eq_two_mul_cliffordPairing]

/-- No nonzero-factor assumptions are needed for the full Clifford action. -/
theorem incident_iff_clifford_sq_zero (p : NeutralSpace) :
    Incident p ↔ neutralAction p * neutralAction p = 0 := by
  rw [neutralAction_sq]
  simp [Incident, smul_eq_zero]

/-- For nonzero primal and dual factors, the dyad and the full exterior
Clifford action detect exactly the same zero-evaluation constraint. -/
theorem dyad_sq_zero_iff_clifford_sq_zero (p : NeutralSpace)
    (hv : p.1 ≠ 0) (hφ : p.2 ≠ 0) :
    dyad p * dyad p = 0 ↔ neutralAction p * neutralAction p = 0 :=
  (dyad_sq_zero_iff p hv hφ).trans (incident_iff_clifford_sq_zero p)

/-- Annihilators of nonzero exterior spinors remain totally null for the
genuine-dual form, with the normalization explicitly accounted for. -/
theorem neutralAnnihilator_isotropic {ψ : Spinor} (hψ : ψ ≠ 0)
    {p q : NeutralSpace} (hp : p ∈ neutralAnnihilator ψ)
    (hq : q ∈ neutralAnnihilator ψ) : neutralForm p q = 0 := by
  rw [neutralForm_eq_two_mul_cliffordPairing,
    neutralAnnihilator_totallyNull hψ p hp q hq, mul_zero]

end InfoGeometry.Twistor.RealDualTwistorClifford
