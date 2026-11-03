/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionCl55CARRestrictionBridge
import InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge

/-!
# One three-mode CAR action in Clifford-spinor and split-Zorn coordinates

The Cl(5,5) vacuum-ideal restriction and the exterior-to-Zorn Fock
intertwiner have independent owners. This module composes them using the
exterior-algebra retraction onto the first three modes. It identifies the
restricted Clifford operators with the existing left-regular split-Zorn
creation and annihilation operators on every state of the three-mode carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCl55ZornActionBridge

open InfoGeometry.Canonical.SplitOctonionCl55CARRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge
open InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.ExteriorZornCARIntertwiner
open InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation

/-- Retract the five-mode exterior spinor to its first three coordinates. -/
def projectColorExterior :
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.Spinor →ₐ[ℝ] Exterior3 :=
  ExteriorAlgebra.map fiveVectorToColor

/-- The exterior-algebra projection is a left inverse to the color inclusion. -/
theorem projectColorExterior_includeColorExterior (ψ : Exterior3) :
    projectColorExterior (includeColorExterior ψ) = ψ := by
  change ((ExteriorAlgebra.map fiveVectorToColor).comp
    (ExteriorAlgebra.map colorVectorToFive)) ψ = ψ
  rw [ExteriorAlgebra.map_comp_map]
  have h := fiveVectorToColor_colorVectorToFive
  rw [h, ExteriorAlgebra.map_id]
  rfl

/-- The first three positive-null Clifford generators act in Zorn coordinates
as the existing split-octonion creation operators. -/
theorem cl55_color_creation_as_zorn
    (i : Fin 3) (ψ : Exterior3) :
    fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (annihilation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ)))) =
      creationMap (Pi.single i 1) (fockToZorn ψ) := by
  rw [cl55_annihilation55_restricts_to_color_creation,
    projectColorExterior_includeColorExterior, fockToZorn_wedge]
  have hbasis : basisVector3 i = Pi.single i (1 : ℝ) := by
    funext j
    by_cases h : j = i <;> simp [basisVector3, h]
  rw [hbasis]

/-- The first three negative-null Clifford generators act in Zorn coordinates
as the existing split-octonion annihilation operators. -/
theorem cl55_color_annihilation_as_zorn
    (i : Fin 3) (ψ : Exterior3) :
    fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (creation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ)))) =
      annihilate i (fockToZorn ψ) := by
  rw [cl55_creation55_restricts_to_color_annihilation,
    projectColorExterior_includeColorExterior, fockToZorn_contract]

end InfoGeometry.Canonical.SplitOctonionCl55ZornActionBridge

end
