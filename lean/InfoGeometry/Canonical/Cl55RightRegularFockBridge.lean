/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionCl55ZornActionBridge
import InfoGeometry.Canonical.ZornLeftRightFockIntertwiner

/-! The three-mode restriction of the Clifford action in right-regular
split-Zorn Fock coordinates. -/

noncomputable section

namespace InfoGeometry.Canonical.Cl55RightRegularFockBridge

open InfoGeometry.Canonical.SplitOctonionCl55ZornActionBridge
open InfoGeometry.Canonical.SplitOctonionCl55CARRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Canonical.ZornLeftRightFockIntertwiner
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.ExteriorZornCARIntertwiner
open InfoGeometry.Lie.SplitOctonionEllPolarization

theorem cl55_creation_right_regular (i : Fin 3) (ψ : Exterior3) :
    leftToRight (fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (annihilation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ))))) =
      rightRegular (rootPlus i) (leftToRight (fockToZorn ψ)) := by
  rw [cl55_color_creation_as_zorn]
  exact leftToRight_creation i ψ

theorem cl55_annihilation_right_regular (i : Fin 3) (ψ : Exterior3) :
    leftToRight (fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (creation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ))))) =
      rightRegular (rootMinus i) (leftToRight (fockToZorn ψ)) := by
  rw [cl55_color_annihilation_as_zorn]
  exact leftToRight_annihilation i ψ

end InfoGeometry.Canonical.Cl55RightRegularFockBridge

end
