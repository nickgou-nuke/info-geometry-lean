import Mathlib.Tactic
import InfoGeometryCore.Basic

/-!
# Needham Fine-Structure Constant Packet

This file formalizes the explicit mathematics stated in SSRN 5404131:
- the golden-ratio definition `φ = (1 + √5) / 2`
- the proposed expression `α⁻¹ = 10 π φ e - log π`
- exact symbolic identities and positivity facts for that expression

It does not claim any physical derivation of the fine-structure constant.
-/

namespace InfoGeometry.Physics.NeedhamFineStructureConstant

open InfoGeometryCore

noncomputable abbrev phi : ℝ := phiR

noncomputable def needhamAlphaInv : ℝ :=
  10 * Real.pi * phi * Real.exp 1 - Real.log Real.pi

noncomputable def codata2018AlphaInv : ℝ :=
  137.035999084

noncomputable def needhamAbsError : ℝ :=
  |needhamAlphaInv - codata2018AlphaInv|

noncomputable def needhamRelError : ℝ :=
  needhamAbsError / codata2018AlphaInv

lemma phi_sq : phi ^ 2 = phi + 1 := by
  dsimp [phi, phiR]
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  field_simp
  nlinarith

lemma phi_pos : 0 < phi := by
  dsimp [phi, phiR]
  have hs : 0 < Real.sqrt 5 := by
    exact Real.sqrt_pos.mpr (by norm_num)
  nlinarith

lemma needhamAlphaInv_eq_closed_form :
    needhamAlphaInv = 5 * Real.pi * (1 + Real.sqrt 5) * Real.exp 1 - Real.log Real.pi := by
  dsimp [needhamAlphaInv, phi, phiR]
  ring

lemma codata2018AlphaInv_pos : 0 < codata2018AlphaInv := by
  norm_num [codata2018AlphaInv]

lemma needhamAbsError_nonneg : 0 ≤ needhamAbsError := by
  dsimp [needhamAbsError]
  exact abs_nonneg _

lemma needhamRelError_nonneg : 0 ≤ needhamRelError := by
  dsimp [needhamRelError]
  exact div_nonneg needhamAbsError_nonneg codata2018AlphaInv_pos.le

lemma needhamRelError_eq :
    needhamRelError = |needhamAlphaInv - codata2018AlphaInv| / codata2018AlphaInv := by
  rfl

end InfoGeometry.Physics.NeedhamFineStructureConstant
