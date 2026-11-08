/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CEOneFormNOperatorBridge
import InfoGeometry.Canonical.BKMScalarGaugeQuotient
import InfoGeometry.Canonical.OperatorFrechetDerivationJet
import InfoGeometry.Thermo.OnsagerOperatorClosure

/-!
# Finite CE-derived BKM/Onsager system

The dissipative form is the pullback of the centered finite BKM covariance
along the CE degree-zero form. The reversible form is the fixed-probe BKM
readout of the native CE connection curvature. Both are constructed as
bilinear forms on the derivation lane; their Onsager properties are proved
from the finite BKM and CE owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.CEBKMOnsagerSystem

open InfoGeometry.Canonical.CEOneFormNOperatorBridge
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Algebra

variable {n : ℕ}

abbrev Carrier (n : ℕ) :=
  (realDerivationsLane (GibbsOperator n)).L

/-- Center the CE-derived finite operator one-form by the genuine finite-state
expectation map. -/
def centeredCEOneForm
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : GibbsOperator n) :
    Op1Form ℝ (Carrier n) (GibbsOperator n) :=
  (BKMScalarGaugeQuotient.centeringLinearMap D hpow).comp
    (finiteCEOperatorForm n a)

/-- The centered finite BKM covariance pulled back to CE derivation
directions. -/
def centeredCEBKMForm
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : GibbsOperator n) :
    LinearMap.BilinForm ℝ (Carrier n) :=
  (D.bkmRealBilinForm hpow).compl₁₂
    (centeredCEOneForm D hpow a) (centeredCEOneForm D hpow a)

@[simp] theorem centeredCEBKMForm_apply
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : GibbsOperator n) (x y : Carrier n) :
    centeredCEBKMForm D hpow a x y =
      centeredBKMRealCovariance D hpow
        (finiteCEOperatorForm n a x) (finiteCEOperatorForm n a y) := by
  simp only [centeredCEBKMForm, LinearMap.compl₁₂_apply,
    centeredCEOneForm, LinearMap.comp_apply,
    BKMScalarGaugeQuotient.centeringLinearMap_apply,
    centeredBKMRealCovariance]

theorem centeredCEBKMForm_symm
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : GibbsOperator n) (x y : Carrier n) :
    centeredCEBKMForm D hpow a x y = centeredCEBKMForm D hpow a y x := by
  rw [centeredCEBKMForm_apply, centeredCEBKMForm_apply]
  exact centeredBKMRealCovariance_symm D hpow _ _

theorem centeredCEBKMForm_nonneg
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : GibbsOperator n) (x : Carrier n) :
    0 ≤ centeredCEBKMForm D hpow a x x := by
  rw [centeredCEBKMForm_apply, centeredBKMRealCovariance_self]
  exact D.kuboMoriPairing_self_re_nonneg
    (centeredStatistic D (finiteCEOperatorForm n a x)) hpow

/-- Scalarize the CE curvature by fixing the second BKM probe. The curvature
cochain and the fixed-probe BKM linear map produce an actual real bilinear
form on the derivation carrier. -/
def ceCurvatureBKMProbeForm
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a Q : GibbsOperator n) :
    LinearMap.BilinForm ℝ (Carrier n) :=
  let K := realDerivationsLane (GibbsOperator n)
  let Γ := exteriorDerivativeZero K a
  LinearMap.mk₂ ℝ
    (fun x y => (D.bkmRealBilinForm hpow).flip Q
      (connectionCurvature K Γ x y))
    (by
      intro x y z
      let κ := connectionCurvature K Γ
      let ℓ := (D.bkmRealBilinForm hpow).flip Q
      change ℓ (κ (x + y) z) = ℓ (κ x z) + ℓ (κ y z)
      have hκ : κ (x + y) = κ x + κ y := map_add κ x y
      rw [show κ (x + y) z = (κ x + κ y) z from congrArg (fun f => f z) hκ,
        LinearMap.add_apply, map_add])
    (by
      intro r x y
      let κ := connectionCurvature K Γ
      let ℓ := (D.bkmRealBilinForm hpow).flip Q
      change ℓ (κ (r • x) y) = r • ℓ (κ x y)
      have hκ : κ (r • x) = r • κ x := map_smul κ r x
      rw [show κ (r • x) y = (r • κ x) y from congrArg (fun f => f y) hκ,
        LinearMap.smul_apply, map_smul])
    (by
      intro x y z
      let κ := connectionCurvature K Γ
      let ℓ := (D.bkmRealBilinForm hpow).flip Q
      change ℓ (κ x (y + z)) = ℓ (κ x y) + ℓ (κ x z)
      rw [map_add (κ x) y z, map_add])
    (by
      intro r x y
      let κ := connectionCurvature K Γ
      let ℓ := (D.bkmRealBilinForm hpow).flip Q
      change ℓ (κ x (r • y)) = r • ℓ (κ x y)
      rw [map_smul (κ x) r y, map_smul])

@[simp] theorem ceCurvatureBKMProbeForm_apply
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a Q : GibbsOperator n) (x y : Carrier n) :
    ceCurvatureBKMProbeForm D hpow a Q x y =
      D.bkmRealBilinForm hpow
        (connectionCurvature (realDerivationsLane (GibbsOperator n))
          (exteriorDerivativeZero (realDerivationsLane (GibbsOperator n)) a) x y)
        Q := by
  rfl

theorem ceCurvatureBKMProbeForm_skew
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a Q : GibbsOperator n) (x y : Carrier n) :
    ceCurvatureBKMProbeForm D hpow a Q x y =
      -ceCurvatureBKMProbeForm D hpow a Q y x := by
  rw [ceCurvatureBKMProbeForm_apply, ceCurvatureBKMProbeForm_apply]
  let κ := connectionCurvature (realDerivationsLane (GibbsOperator n))
    (exteriorDerivativeZero (realDerivationsLane (GibbsOperator n)) a)
  let ℓ := (D.bkmRealBilinForm hpow).flip Q
  change ℓ (κ x y) = -ℓ (κ y x)
  have h := LieModule.Cohomology.twoCochain_skew κ x y
  calc
    ℓ (κ x y) = -ℓ (-κ x y) := by simp
    _ = -ℓ (κ y x) := congrArg Neg.neg (congrArg ℓ h)

/-- The finite CE Onsager system with centered BKM dissipation and a
curvature-derived reversible term. No reversible-zero shortcut is used. -/
def finiteCEOnsagerSystem
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a Q : GibbsOperator n) :
    OnsagerCasimirSystem (Carrier n) where
  dissipative := centeredCEBKMForm D hpow a
  reversible := ceCurvatureBKMProbeForm D hpow a Q
  dissipative_symm := centeredCEBKMForm_symm D hpow a
  reversible_skew := ceCurvatureBKMProbeForm_skew D hpow a Q
  dissipative_nonneg := centeredCEBKMForm_nonneg D hpow a

theorem finiteCEOnsagerSystem_entropy
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a Q : GibbsOperator n) (x : Carrier n) :
    (finiteCEOnsagerSystem D hpow a Q).totalGenerator x x =
        centeredBKMRealCovariance D hpow
          (finiteCEOperatorForm n a x) (finiteCEOperatorForm n a x) ∧
      0 ≤ (finiteCEOnsagerSystem D hpow a Q).totalGenerator x x := by
  constructor
  · rw [(finiteCEOnsagerSystem D hpow a Q).entropy_production_eq]
    exact centeredCEBKMForm_apply D hpow a x x
  · exact (finiteCEOnsagerSystem D hpow a Q).entropy_production_nonneg x

end InfoGeometry.Canonical.CEBKMOnsagerSystem
