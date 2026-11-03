/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55RightRegularFockBridge
import InfoGeometry.Canonical.SplitOctonionRightRegularBraid

/-! Transport of the sum of the restricted null actions to the existing
right-regular Majorana operator. -/

noncomputable section

namespace InfoGeometry.Canonical.Cl55RightRegularMajoranaBridge

open InfoGeometry.Canonical.Cl55RightRegularFockBridge
open InfoGeometry.Canonical.SplitOctonionCl55ZornActionBridge
open InfoGeometry.Canonical.SplitOctonionCl55CARRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.ZornLeftRightFockIntertwiner
open InfoGeometry.Canonical.SplitOctonionRightRegularBraid
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.ExteriorZornCARIntertwiner

theorem cl55_null_pair_majorana (i : Fin 3) (ψ : Exterior3) :
    leftToRight (fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv (cl55VacuumIdealLeftAction
        (annihilation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ))))) +
    leftToRight (fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv (cl55VacuumIdealLeftAction
        (creation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ))))) =
      majorana i (leftToRight (fockToZorn ψ)) := by
  rw [cl55_creation_right_regular, cl55_annihilation_right_regular]
  rfl

end InfoGeometry.Canonical.Cl55RightRegularMajoranaBridge

end
