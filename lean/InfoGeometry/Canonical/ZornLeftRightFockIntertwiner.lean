/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ExteriorZornCARIntertwiner
import InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner

/-! The left and right regular CAR representations are intertwined through
their independently constructed exterior-Fock equivalences. -/

noncomputable section

namespace InfoGeometry.Canonical.ZornLeftRightFockIntertwiner

open InfoGeometry.Clifford.ExteriorZornCARIntertwiner
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Lie.SplitOctonionEllPolarization

local notation "RightFock" => InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockBdGEquiv
local notation "CZ" => InfoGeometry.Canonical.ZornMatrix ℝ

/-- Change between the two native Zorn Fock representations. -/
def leftToRight : CZ ≃ₗ[ℝ] CZ :=
  exteriorZornCARLinearEquiv.symm.trans RightFock

theorem leftToRight_creation (i : Fin 3) (ψ : Exterior3) :
    leftToRight (creationMap (Pi.single i (1 : ℝ)) (fockToZorn ψ)) =
      rightRegular (rootPlus i) (leftToRight (fockToZorn ψ)) := by
  rw [← fockToZorn_wedge]
  simp only [leftToRight, LinearEquiv.trans_apply,
    show ∀ v, exteriorZornCARLinearEquiv.symm (fockToZorn v) = v from
      fun v => exteriorZornCARLinearEquiv.symm_apply_apply v]
  change RightFock (exteriorWedge3 (Pi.single i (1 : ℝ)) ψ) =
    rightRegular (rootPlus i) (RightFock ψ)
  simpa [InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift.modeVector] using
    (InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockToZorn_creation_mode i ψ)

theorem leftToRight_annihilation (i : Fin 3) (ψ : Exterior3) :
    leftToRight (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i (fockToZorn ψ)) =
      rightRegular (rootMinus i) (leftToRight (fockToZorn ψ)) := by
  rw [← fockToZorn_contract]
  simp only [leftToRight, LinearEquiv.trans_apply,
    show ∀ v, exteriorZornCARLinearEquiv.symm (fockToZorn v) = v from
      fun v => exteriorZornCARLinearEquiv.symm_apply_apply v]
  change RightFock (exteriorContract3 (LinearMap.proj i) ψ) =
    rightRegular (rootMinus i) (RightFock ψ)
  have hc : (Pi.basisFun ℝ (Fin 3)).coord i = LinearMap.proj i := by
    ext v
    rfl
  simpa only [InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift.modeCovector, hc,
    InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockBdGEquiv_apply] using
    (InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockToZorn_annihilation i ψ)

end InfoGeometry.Canonical.ZornLeftRightFockIntertwiner
