/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55RightRegularMajoranaBridge
import InfoGeometry.Twistor.WeylZornMajoranaNambu

/-! The restricted Clifford null pair acts as Nambu sheet exchange through
the existing Fock and one-mode CAR equivalences. -/

noncomputable section

namespace InfoGeometry.Twistor.Cl55MajoranaNambuBridge

open InfoGeometry.Canonical.Cl55RightRegularMajoranaBridge
open InfoGeometry.Canonical.SplitOctonionCl55ZornActionBridge
open InfoGeometry.Canonical.SplitOctonionCl55CARRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.ZornLeftRightFockIntertwiner
open InfoGeometry.Canonical.ZornBdGPhaseFlowBridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.ExteriorZornCARIntertwiner
open InfoGeometry.Krein
open InfoGeometry.Twistor.WeylZornMajoranaNambu

theorem cl55_null_pair_nambu_swap (i : Fin 3)
    (ψ : InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3) :
    leftToRight (fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv (cl55VacuumIdealLeftAction
        (annihilation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ))))) +
    leftToRight (fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv (cl55VacuumIdealLeftAction
        (creation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ))))) =
      doubledZornEquiv i (modular_j
        ((doubledZornEquiv i).symm (leftToRight (fockToZorn ψ)))) := by
  rw [cl55_null_pair_majorana, ← majorana_intertwines_nambu_swap]
  rw [LinearEquiv.apply_symm_apply]

end InfoGeometry.Twistor.Cl55MajoranaNambuBridge

end
