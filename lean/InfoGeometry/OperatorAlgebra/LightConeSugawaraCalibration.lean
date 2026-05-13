import InfoGeometry.OperatorAlgebra.KANLightConeAffineBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration

Sugawara binding for KAN-organized lightcone affine currents.

This module is intentionally a binding layer, not a new Sugawara theorem.  It
consumes:

* `KANLightConeAffineBridge`, which routes supplied lightcone directions through
  affine current/Virasoro owner data;
* `AffineVirasoroBridge.SugawaraModeConstructionDatum`, which supplies the
  normal-ordered mode-sum calibration.

The compatibility between those two sockets is an external predicate.  This
file does not prove Kac--Moody, normal ordering, Virasoro, or Sugawara from raw
projectors.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
open InfoGeometry.OperatorAlgebra.KANLightConeAffineBridge
open InfoGeometry.OperatorAlgebra.WeylWeightBalance

/--
Carrier binding a KAN/lightcone affine socket to a supplied Sugawara mode-sum
datum.

No compatibility law is bundled.  Use `UsesLightConeAffineBridge` when a theorem
needs to identify the Sugawara datum's affine bridge with the lightcone affine
bridge.
-/
@[rep_depth operator]
structure LightConeSugawaraCalibration
    (E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- KAN/Bogoliubov-shadowed lightcone affine-current socket. -/
  kanAffine :
    KANLightConeAffineBridge E Finite Alg Bog Korth Asplit Nshear CartanDiag

  /-- Supplied Sugawara normal-ordered mode-sum datum. -/
  sugawara :
    SugawaraModeConstructionDatum Finite Alg

namespace LightConeSugawaraCalibration

variable
    {E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (S :
  LightConeSugawaraCalibration E Finite Alg Bog Korth Asplit Nshear CartanDiag)

/--
External compatibility predicate: the supplied Sugawara datum is calibrated
against the same affine/Virasoro bridge used by the lightcone affine socket.
-/
@[rep_depth operator]
def UsesLightConeAffineBridge : Prop :=
  S.sugawara.bridge = S.kanAffine.affineLightCone.bridge

/-- Sugawara rescaling factor inherited from the supplied mode-sum datum. -/
@[rep_depth operator]
def sugawaraFactor : ℝ :=
  S.sugawara.sugawaraFactor

/-- Normal-ordered lightcone/affine mode sum used by the supplied Sugawara datum. -/
@[rep_depth operator]
def modeSum (n : ℤ) : Alg :=
  S.sugawara.modeSum n

/--
Sugawara owner readback: the Virasoro generator is the supplied mode sum
rescaled by the Sugawara factor.
-/
@[rep_depth operator]
theorem sugawara_virasoro_mode_eq_rescaled_sum
    (n : ℤ) :
    S.sugawara.bridge.virasoro.Lmode n =
      S.sugawaraFactor • S.modeSum n := by
  exact S.sugawara.virasoro_mode_eq_rescaled_sum n

/--
Lightcone-compatible Sugawara readback.  Under the external compatibility
predicate, the lightcone bridge's Virasoro mode is the supplied Sugawara
mode-sum readout.
-/
@[rep_depth operator]
theorem lightcone_virasoro_mode_eq_rescaled_sum
    (hUse : S.UsesLightConeAffineBridge)
    (n : ℤ) :
    S.kanAffine.affineLightCone.bridge.virasoro.Lmode n =
      S.sugawaraFactor • S.modeSum n := by
  rw [← hUse]
  exact S.sugawara_virasoro_mode_eq_rescaled_sum n

/-- Virasoro bracket in coefficient-normalized form, inherited from the owner datum. -/
@[rep_depth operator]
theorem virasoro_bracket_modes_normalized
    (m n : ℤ) :
    ⁅S.sugawara.bridge.virasoro.Lmode m, S.sugawara.bridge.virasoro.Lmode n⁆ =
      (m - n : ℝ) • S.sugawara.bridge.virasoro.Lmode (m + n) +
        (virasoroCentralCoefficient m n : ℝ) • S.sugawara.bridge.virasoro.central :=
  S.sugawara.bridge.virasoro.bracket_modes_normalized m n

/-- Sugawara central charge calibration inherited from the supplied affine/Virasoro datum. -/
@[rep_depth operator]
theorem sugawara_centralCharge_calibrated :
    S.sugawara.bridge.centralCharge =
      S.sugawara.bridge.level * S.sugawara.bridge.finiteDimension /
        (S.sugawara.bridge.level + S.sugawara.bridge.dualCoxeterNumber) :=
  S.sugawara.bridge.centralCharge_calibrated

/--
Lightcone central charge calibration inherited from the KAN/lightcone affine
socket.
-/
@[rep_depth operator]
theorem lightcone_centralCharge_calibrated :
    S.kanAffine.affineLightCone.bridge.centralCharge =
      S.kanAffine.affineLightCone.bridge.level *
        S.kanAffine.affineLightCone.bridge.finiteDimension /
          (S.kanAffine.affineLightCone.bridge.level +
            S.kanAffine.affineLightCone.bridge.dualCoxeterNumber) :=
  S.kanAffine.centralCharge_calibrated

/-- The Virasoro central coefficient is zero away from the balanced mode sector. -/
@[rep_depth operator]
theorem virasoroCentralCoefficient_eq_zero_of_not_modeBalanced
    {m n : ℤ}
    (hNot : ¬ IsModeBalanced m n) :
    virasoroCentralCoefficient m n = 0 := by
  unfold virasoroCentralCoefficient IsModeBalanced at *
  simp [hNot]

/-- The Virasoro central term vanishes away from the balanced mode sector. -/
@[rep_depth operator]
theorem virasoro_centralTerm_eq_zero_of_not_modeBalanced
    {m n : ℤ}
    (hNot : ¬ IsModeBalanced m n) :
    (virasoroCentralCoefficient m n : ℝ) • S.sugawara.bridge.virasoro.central = 0 := by
  have hCoeff : virasoroCentralCoefficient m n = 0 := by
    unfold virasoroCentralCoefficient IsModeBalanced at *
    simp [hNot]
  rw [hCoeff]
  simp

/--
Affine central selector for the lightcone current socket vanishes away from the
balanced mode sector.
-/
@[rep_depth operator]
theorem affineCentralSelector_eq_zero_of_not_modeBalanced
    {m n : ℤ}
    (hNot : ¬ IsModeBalanced m n) :
    (if m + n = 0 then S.kanAffine.affineLightCone.affine.kCentral else 0) = 0 :=
  S.kanAffine.centralSelector_eq_zero_of_not_modeBalanced hNot

/--
Under the compatibility predicate, the supplied Sugawara Virasoro modes act on
positive lightcone currents by the inherited affine/Virasoro action law.
-/
@[rep_depth operator]
theorem sugawara_virasoro_acts_on_uPlusCurrent
    (hUse : S.UsesLightConeAffineBridge)
    (m n : ℤ) :
    ⁅S.sugawara.bridge.virasoro.Lmode m, S.kanAffine.uPlusCurrent n⁆ =
      (-(n : ℝ)) • S.kanAffine.uPlusCurrent (m + n) := by
  have hVir := S.kanAffine.affineLightCone.bridge_virasoro_eq
  rw [hUse, hVir]
  exact S.kanAffine.virasoro_acts_on_uPlusCurrent m n

/--
Under the compatibility predicate, the supplied Sugawara Virasoro modes act on
negative lightcone currents by the inherited affine/Virasoro action law.
-/
@[rep_depth operator]
theorem sugawara_virasoro_acts_on_uMinusCurrent
    (hUse : S.UsesLightConeAffineBridge)
    (m n : ℤ) :
    ⁅S.sugawara.bridge.virasoro.Lmode m, S.kanAffine.uMinusCurrent n⁆ =
      (-(n : ℝ)) • S.kanAffine.uMinusCurrent (m + n) := by
  have hVir := S.kanAffine.affineLightCone.bridge_virasoro_eq
  rw [hUse, hVir]
  exact S.kanAffine.virasoro_acts_on_uMinusCurrent m n

end LightConeSugawaraCalibration

end InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration
