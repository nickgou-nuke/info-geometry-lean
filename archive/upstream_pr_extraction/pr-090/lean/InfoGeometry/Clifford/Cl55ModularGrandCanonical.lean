import InfoGeometry.Clifford.Cl55ModularDerivation
import InfoGeometry.Clifford.Cl55ChiralGrandCanonical

/-!
# Grand-canonical charge conservation as a modular-derivation statement

The grand-canonical owner supplies conservation of the chiral charge inside
the noncommutative `Cl55` algebra.  This file converts that equality into the
vanishing of the already-owned inner derivation.  No state, trace, topology,
or analytic modular flow is asserted here.
-/

namespace InfoGeometry.Clifford.Clifford55

theorem cl55GrandCanonical_modularDerivation_charge_zero
    (H : Cl55) (μplus μminus : ℝ)
    (hH : chiralChargeConserved55 H)
    (hPlus : chiralPlusNumber55 * chiralCharge55 =
      chiralCharge55 * chiralPlusNumber55)
    (hMinus : chiralMinusNumber55 * chiralCharge55 =
      chiralCharge55 * chiralMinusNumber55) :
    cl55ModularDerivation
        (chiralGrandCanonicalGenerator55 H μplus μminus)
        chiralCharge55 = 0 := by
  rw [cl55ModularDerivation_apply]
  have hcomm :
      chiralGrandCanonicalGenerator55 H μplus μminus * chiralCharge55 =
        chiralCharge55 * chiralGrandCanonicalGenerator55 H μplus μminus :=
    chiralGrandCanonicalGenerator55_commutes_charge
      H μplus μminus hH hPlus hMinus
  rw [hcomm]
  exact sub_self _

end InfoGeometry.Clifford.Clifford55
