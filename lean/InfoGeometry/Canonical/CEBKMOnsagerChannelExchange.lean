/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily
import InfoGeometry.Thermo.OnsagerOperatorClosure

noncomputable section

namespace InfoGeometry.Canonical.CEBKMOnsagerChannelExchange

open InfoGeometry.Canonical.BKMScalarGaugeQuotient
open InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration
open InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily
open InfoGeometry.Canonical.CEBKMOnsagerSystem
open InfoGeometry.Canonical.CEOneFormNOperatorBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem

variable {n : ℕ}

abbrev TwoChannelCarrier (n : ℕ) := FamilyCarrier 2 n

def exchangeChannels : (Fin 2 → Carrier n) →ₗ[ℝ] (Fin 2 → Carrier n) where
  toFun x := fun i => x (Equiv.swap 0 1 i)
  map_add' x y := by
    funext i
    simp
  map_smul' c x := by
    funext i
    simp

@[simp] theorem exchangeChannels_zero (x : TwoChannelCarrier n) :
    exchangeChannels x 0 = x 1 := by
  simp [exchangeChannels]

@[simp] theorem exchangeChannels_one (x : TwoChannelCarrier n) :
    exchangeChannels x 1 = x 0 := by
  simp [exchangeChannels]

theorem exchangeChannels_involutive (x : TwoChannelCarrier n) :
    exchangeChannels (exchangeChannels x) = x := by
  funext i
  fin_cases i <;> simp

def exchangeTimeReversal : TimeReversal (TwoChannelCarrier n) where
  op := exchangeChannels
  involutive := exchangeChannels_involutive

def antisymmetricChannelWeights : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 else -1

theorem weightedReadout_exchange_neg
    (a : GibbsOperator n) (x : TwoChannelCarrier n) :
    finiteGibbsCEFamilyNOperatorReadoutLinear (fun _ : Fin 2 => a)
      antisymmetricChannelWeights (exchangeChannels x) =
    -finiteGibbsCEFamilyNOperatorReadoutLinear (fun _ : Fin 2 => a)
      antisymmetricChannelWeights x := by
  rw [finiteGibbsCEFamilyNOperatorReadoutLinear_apply,
    finiteGibbsCEFamilyNOperatorReadoutLinear_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have h01 : ∀ v, finiteGibbsCEFamilyComponentForm (fun _ : Fin 2 => a) 0 v =
      finiteGibbsCEFamilyComponentForm (fun _ : Fin 2 => a) 1 v := fun _ => rfl
  simp only [antisymmetricChannelWeights, exchangeChannels_zero, exchangeChannels_one,
    Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, one_smul, h01]
  module

theorem channelDissipation_exchange_even
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : GibbsOperator n)
    (x y : TwoChannelCarrier n) :
    finiteCEFamilyNOperatorDissipativeForm D hpow (fun _ : Fin 2 => a)
      antisymmetricChannelWeights (exchangeChannels x) (exchangeChannels y) =
    finiteCEFamilyNOperatorDissipativeForm D hpow (fun _ : Fin 2 => a)
      antisymmetricChannelWeights x y := by
  rw [finiteCEFamilyNOperatorDissipativeForm_apply,
    finiteCEFamilyNOperatorDissipativeForm_apply,
    weightedReadout_exchange_neg, weightedReadout_exchange_neg]
  unfold centeredBKMRealCovariance
  rw [← centeringLinearMap_apply D hpow, ← centeringLinearMap_apply D hpow]
  simp only [map_neg, LinearMap.neg_apply, neg_neg, centeringLinearMap_apply]

theorem channelCurvature_exchange_odd
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a Q : GibbsOperator n)
    (x y : TwoChannelCarrier n) :
    finiteCEFamilyNOperatorCurvatureProbeForm D hpow
      (fun _ : Fin 2 => a) antisymmetricChannelWeights Q
      (exchangeChannels x) (exchangeChannels y) =
    -finiteCEFamilyNOperatorCurvatureProbeForm D hpow
      (fun _ : Fin 2 => a) antisymmetricChannelWeights Q x y := by
  rw [finiteCEFamilyNOperatorCurvatureProbeForm_apply,
    finiteCEFamilyNOperatorCurvatureProbeForm_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [antisymmetricChannelWeights, exchangeChannels_zero, exchangeChannels_one,
    Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
  ring

def twoChannelGibbsParityOnsagerSystem
    (H a Q : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    ParityOnsagerSystem (TwoChannelCarrier n) where
  toOnsagerCasimirSystem :=
    finiteGibbsCEFamilyNOperatorSystem H hH hZ
      (fun _ : Fin 2 => a) antisymmetricChannelWeights Q
  T := exchangeTimeReversal
  dissipative_T_even := by
    intro x y
    exact channelDissipation_exchange_even
      (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ) a x y
  reversible_T_odd := by
    intro x y
    exact channelCurvature_exchange_odd
      (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ) a Q x y

theorem twoChannelGibbsOnsager_casimir_reciprocity
    (H a Q : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) (x y : TwoChannelCarrier n) :
    (twoChannelGibbsParityOnsagerSystem H a Q hH hZ).totalGenerator
        (exchangeChannels x) (exchangeChannels y) =
      (twoChannelGibbsParityOnsagerSystem H a Q hH hZ).totalGenerator y x :=
  (twoChannelGibbsParityOnsagerSystem H a Q hH hZ).onsager_casimir_master_reciprocity x y

end InfoGeometry.Canonical.CEBKMOnsagerChannelExchange

end noncomputable section
