/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CARCCRColimitSupercarrier
import InfoGeometry.Canonical.FureySplitOctonionColimitBridge
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationLinearityWave16

/-!
# Zorn CAR and polynomial CCR on the same algebraic Fock-colimit carrier

The finite split-octonion CAR state map into the Clifford Fock colimit is
tensored with the identity on polynomial wavefunctions. This gives explicit
intertwining theorems for the three-mode Majorana mass and the polynomial CCR
creation/annihilation operators. The polynomial and CAR operators remain
actions on distinct tensor factors.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCARCCRColimitBridge

open scoped TensorProduct
open InfoGeometry.Twistor.RealSupertwistor
open InfoGeometry.Twistor.RealPolynomialCCR
open InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge
open InfoGeometry.Canonical.FureySplitOctonionSuperchargeBridge
open InfoGeometry.Canonical.FureySplitOctonionColimitBridge

local notation "Zorn" => InfoGeometry.Canonical.ZornMatrix ℝ
local notation "Wave" => WavePolynomial (Fin 3)
local notation "ZornCarrier" => Wave ⊗[ℝ] Zorn
local notation "ColimitCarrier" => Wave ⊗[ℝ] FockInfinity
local notation "WaveFive" => WavePolynomial (Fin 5)
local notation "FiveModeCarrier" => WaveFive ⊗[ℝ] FockInfinity

/-- The first three polynomial modes are included in the existing
five-mode polynomial carrier by the canonical order-preserving embedding. -/
def colorPolynomialEmbedding : Wave →ₐ[ℝ] WaveFive :=
  MvPolynomial.rename (fun i : Fin 3 => Fin.castAdd 2 i)

/-- Polynomial differentiation is preserved by the same mode inclusion. -/
theorem colorPolynomialEmbedding_annihilate (i : Fin 3) (p : Wave) :
    colorPolynomialEmbedding (annihilate i p) =
      annihilate (Fin.castAdd 2 i) (colorPolynomialEmbedding p) := by
  rw [annihilate_apply, annihilate_apply]
  exact (MvPolynomial.pderiv_rename
    (fun a b h => Fin.castAdd_inj.mp h) i p).symm

/-- Tensor the polynomial-mode inclusion with the identity on the Zorn CAR
state carrier. -/
def zornThreeToFiveCarrier : ZornCarrier →ₗ[ℝ] WaveFive ⊗[ℝ] Zorn :=
  TensorProduct.map colorPolynomialEmbedding.toLinearMap
    (LinearMap.id : Zorn →ₗ[ℝ] Zorn)

/-- Tensor the same polynomial-mode inclusion with the identity on the
algebraic Fock colimit. -/
def colimitThreeToFiveCarrier : ColimitCarrier →ₗ[ℝ] FiveModeCarrier :=
  TensorProduct.map colorPolynomialEmbedding.toLinearMap
    (LinearMap.id : FockInfinity →ₗ[ℝ] FockInfinity)

/-- Linear packaging of the existing algebraic Fock-colimit action. -/
def splitCliffordFockActionLinear (a : SplitCliffordInfinity) :
    FockInfinity →ₗ[ℝ] FockInfinity where
  toFun := splitCliffordFockAction a
  map_add' := splitCliffordFockAction_add_right a
  map_smul' r ψ := splitCliffordFockAction_smul_right r a ψ

/-- Carry a polynomial–Zorn state into the polynomial–Fock-colimit carrier,
using the established three-mode Zorn-to-Fock state map. -/
def zornCarrierToFockColimit : ZornCarrier →ₗ[ℝ] ColimitCarrier :=
  TensorProduct.map (LinearMap.id : Wave →ₗ[ℝ] Wave) zornStateToFockColimit

/-- The finite three-mode split-Clifford mass acting on the Fock-colimit
factor of the polynomial–Fock carrier. -/
def zornMassOnFockColimit : Module.End ℝ ColimitCarrier :=
  (splitCliffordFockActionLinear
    (DirectLimit.Algebra.of SplitClNNAlg
      (fun m n h => splitCliffordMap m n h) 3 zornThreeModeMajoranaClifford)).lTensor Wave

/-- The same three-mode Clifford mass acting on the already-owned five-mode
polynomial–Fock colimit carrier. -/
def zornMassOnFiveModeColimit : Module.End ℝ FiveModeCarrier :=
  (splitCliffordFockActionLinear
    (DirectLimit.Algebra.of SplitClNNAlg
      (fun m n h => splitCliffordMap m n h) 3 zornThreeModeMajoranaClifford)).lTensor WaveFive

/-- The three-mode Zorn Majorana mass transports through the polynomial-mode
inclusion to its action on the established five-mode colimit carrier. -/
theorem zorn_mass_transports_to_five_mode_colimit (v : ColimitCarrier) :
    colimitThreeToFiveCarrier (zornMassOnFockColimit v) =
      zornMassOnFiveModeColimit (colimitThreeToFiveCarrier v) := by
  change (TensorProduct.map colorPolynomialEmbedding.toLinearMap
      (LinearMap.id : FockInfinity →ₗ[ℝ] FockInfinity))
      ((splitCliffordFockActionLinear
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 3
          zornThreeModeMajoranaClifford)).lTensor Wave v) =
    ((splitCliffordFockActionLinear
      (DirectLimit.Algebra.of SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) 3
        zornThreeModeMajoranaClifford)).lTensor WaveFive)
      ((TensorProduct.map colorPolynomialEmbedding.toLinearMap
        (LinearMap.id : FockInfinity →ₗ[ℝ] FockInfinity)) v)
  rw [LinearMap.map_lTensor, LinearMap.lTensor_map]
  simp


/-- The polynomial mode embedding transports each selected CCR creation
operator, tensored with the Zorn state carrier, into the five-mode carrier. -/
theorem zorn_creation_transports_to_five_mode (i : Fin 3) (v : ZornCarrier) :
    zornThreeToFiveCarrier ((create i).rTensor Zorn v) =
      (create (Fin.castAdd 2 i)).rTensor Zorn (zornThreeToFiveCarrier v) := by
  have hcreate : colorPolynomialEmbedding.toLinearMap.comp (create i) =
      (create (Fin.castAdd 2 i)).comp colorPolynomialEmbedding.toLinearMap := by
    apply LinearMap.ext
    intro p
    simp [colorPolynomialEmbedding, create_apply]
  change (TensorProduct.map colorPolynomialEmbedding.toLinearMap
      (LinearMap.id : Zorn →ₗ[ℝ] Zorn)) ((create i).rTensor Zorn v) =
    (create (Fin.castAdd 2 i)).rTensor Zorn
      ((TensorProduct.map colorPolynomialEmbedding.toLinearMap
        (LinearMap.id : Zorn →ₗ[ℝ] Zorn)) v)
  rw [LinearMap.map_rTensor, LinearMap.rTensor_map]
  rw [hcreate]

/-- The polynomial mode embedding transports each selected CCR annihilation
operator, tensored with the Zorn state carrier, into the five-mode carrier. -/
theorem zorn_annihilation_transports_to_five_mode (i : Fin 3) (v : ZornCarrier) :
    zornThreeToFiveCarrier ((annihilate i).rTensor Zorn v) =
      (annihilate (Fin.castAdd 2 i)).rTensor Zorn (zornThreeToFiveCarrier v) := by
  have hannihilate : colorPolynomialEmbedding.toLinearMap.comp (annihilate i) =
      (annihilate (Fin.castAdd 2 i)).comp colorPolynomialEmbedding.toLinearMap := by
    apply LinearMap.ext
    intro p
    exact colorPolynomialEmbedding_annihilate i p
  change (TensorProduct.map colorPolynomialEmbedding.toLinearMap
      (LinearMap.id : Zorn →ₗ[ℝ] Zorn)) ((annihilate i).rTensor Zorn v) =
    (annihilate (Fin.castAdd 2 i)).rTensor Zorn
      ((TensorProduct.map colorPolynomialEmbedding.toLinearMap
        (LinearMap.id : Zorn →ₗ[ℝ] Zorn)) v)
  rw [LinearMap.map_rTensor, LinearMap.rTensor_map]
  rw [hannihilate]

/-- On every polynomial–Zorn state, the three-mode Zorn mass action agrees
with the induced split-Clifford action in the algebraic Fock colimit. -/
theorem zorn_mass_action_intertwines_fock_colimit (v : ZornCarrier) :
    zornCarrierToFockColimit (zornThreeModeMajorana v) =
      zornMassOnFockColimit (zornCarrierToFockColimit v) := by
  have hMass : zornThreeModeMajorana = zornThreeModeMajoranaState.lTensor Wave := by
    have hid : (1 : Module.End ℝ ZornCarrier) =
        (1 : Module.End ℝ Wave).rTensor Zorn := by
      change (LinearMap.id : ZornCarrier →ₗ[ℝ] ZornCarrier) =
        (LinearMap.id : Wave →ₗ[ℝ] Wave).rTensor Zorn
      rw [LinearMap.rTensor_id]
    rw [← splitOctonionCARCCRRepresentation_majorana_mass,
      splitOctonionCARCCRRepresentation_tmul]
    rw [← hid, one_mul]
  have hState : zornStateToFockColimit.comp zornThreeModeMajoranaState =
      LinearMap.comp (splitCliffordFockActionLinear
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 3
          zornThreeModeMajoranaClifford)) zornStateToFockColimit := by
    ext z
    exact (zorn_mass_intertwines_fock_colimit z).symm
  rw [hMass]
  change (TensorProduct.map (LinearMap.id : Wave →ₗ[ℝ] Wave)
      zornStateToFockColimit) ((zornThreeModeMajoranaState.lTensor Wave) v) =
    ((splitCliffordFockActionLinear
      (DirectLimit.Algebra.of SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) 3
        zornThreeModeMajoranaClifford)).lTensor Wave)
      ((TensorProduct.map (LinearMap.id : Wave →ₗ[ℝ] Wave)
        zornStateToFockColimit) v)
  rw [LinearMap.map_lTensor, LinearMap.lTensor_map, hState]

/-- Polynomial CCR creation intertwines with the identical creation operator
on the polynomial factor after the Zorn state embedding. -/
theorem boson_creation_intertwines_zorn_fock_colimit (i : Fin 3)
    (v : ZornCarrier) :
    zornCarrierToFockColimit ((create i).rTensor Zorn v) =
      (create i).rTensor FockInfinity (zornCarrierToFockColimit v) := by
  change (TensorProduct.map (LinearMap.id : Wave →ₗ[ℝ] Wave)
      zornStateToFockColimit) ((create i).rTensor Zorn v) =
    (create i).rTensor FockInfinity
      ((TensorProduct.map (LinearMap.id : Wave →ₗ[ℝ] Wave)
        zornStateToFockColimit) v)
  rw [LinearMap.map_rTensor, LinearMap.rTensor_map]
  simp

/-- Polynomial CCR annihilation intertwines with the identical annihilation
operator on the polynomial factor after the Zorn state embedding. -/
theorem boson_annihilation_intertwines_zorn_fock_colimit (i : Fin 3)
    (v : ZornCarrier) :
    zornCarrierToFockColimit ((annihilate i).rTensor Zorn v) =
      (annihilate i).rTensor FockInfinity (zornCarrierToFockColimit v) := by
  change (TensorProduct.map (LinearMap.id : Wave →ₗ[ℝ] Wave)
      zornStateToFockColimit) ((annihilate i).rTensor Zorn v) =
    (annihilate i).rTensor FockInfinity
      ((TensorProduct.map (LinearMap.id : Wave →ₗ[ℝ] Wave)
        zornStateToFockColimit) v)
  rw [LinearMap.map_rTensor, LinearMap.rTensor_map]
  simp

/-- The polynomial CCR action commutes with the transported Zorn Majorana mass
on the polynomial–Fock-colimit carrier. This is the cross-factor relation on
the common target carrier, not merely an intertwining statement about states. -/
theorem polynomial_operator_commutes_with_zorn_mass_on_fock_colimit
    (b : Module.End ℝ Wave) :
    (b.rTensor FockInfinity) * zornMassOnFockColimit =
      zornMassOnFockColimit * (b.rTensor FockInfinity) := by
  change (b.rTensor FockInfinity).comp
      ((splitCliffordFockActionLinear
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 3
          zornThreeModeMajoranaClifford)).lTensor Wave) =
    ((splitCliffordFockActionLinear
      (DirectLimit.Algebra.of SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) 3
        zornThreeModeMajoranaClifford)).lTensor Wave).comp
      (b.rTensor FockInfinity)
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

end InfoGeometry.Canonical.ZornCARCCRColimitBridge

end
