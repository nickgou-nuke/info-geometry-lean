import InfoGeometry.OperatorAlgebra.KANLightConeAffineBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration

Sugawara binding for KAN-organized lightcone affine currents.

The KAN socket owns the affine/Virasoro bridge.  This module adds only the
normal-ordered mode sum needed to construct the corresponding Sugawara datum;
no parallel bridge and no bridge-equality evidence are stored.
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
-/
@[rep_depth operator]
structure Calibration
    (E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- KAN/Bogoliubov-shadowed lightcone affine-current socket. -/
  kanAffine :
    InfoGeometry.OperatorAlgebra.KANLightConeAffineBridge.Bridge
      E Finite Alg Bog Korth Asplit Nshear CartanDiag

  /-- Normal-ordered bilinear mode sum attached to the KAN affine bridge. -/
  sugawaraModeSum :
    ℤ → Alg

namespace Calibration

variable
    {E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (S :
  Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag)

/--
The Sugawara datum constructed natively from the KAN-owned affine/Virasoro
bridge and the supplied normal-ordered mode sum.
-/
@[rep_depth operator]
def sugawara : SugawaraModeConstructionDatum Finite Alg where
  bridge := S.kanAffine.affineLightCone.bridge
  modeSum := S.sugawaraModeSum

/--
The constructed Sugawara datum uses the KAN-owned affine/Virasoro bridge
definitionally.
-/
theorem uses_lightcone_affine_bridge :
    S.sugawara.bridge = S.kanAffine.affineLightCone.bridge := by
  rfl


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
    (n : ℤ)
    (hsum :
      ∀ n : ℤ,
        S.sugawara.bridge.virasoro.Lmode n =
          (1 / (2 * (S.sugawara.bridge.level + S.sugawara.bridge.dualCoxeterNumber))) •
            S.sugawara.modeSum n) :
    S.sugawara.bridge.virasoro.Lmode n =
      S.sugawaraFactor • S.modeSum n := by
  exact S.sugawara.virasoro_mode_eq_rescaled_sum n hsum

/--
Lightcone-compatible Sugawara readback.  The lightcone bridge's Virasoro mode
is the supplied Sugawara mode-sum readout by definitional bridge ownership.
-/
@[rep_depth operator]
theorem lightcone_virasoro_mode_eq_rescaled_sum
    (n : ℤ)
    (hsum :
      ∀ n : ℤ,
        S.sugawara.bridge.virasoro.Lmode n =
          (1 / (2 * (S.sugawara.bridge.level + S.sugawara.bridge.dualCoxeterNumber))) •
            S.sugawara.modeSum n) :
    S.kanAffine.affineLightCone.bridge.virasoro.Lmode n =
      S.sugawaraFactor • S.modeSum n := by
  rw [← S.uses_lightcone_affine_bridge]
  exact S.sugawara_virasoro_mode_eq_rescaled_sum n hsum

/-- Virasoro bracket in coefficient-normalized form, inherited from the owner datum. -/
@[rep_depth operator]
theorem virasoro_bracket_modes_normalized
    (m n : ℤ)
    (hvir :
      ∀ m n : ℤ,
        ⁅S.sugawara.bridge.virasoro.Lmode m, S.sugawara.bridge.virasoro.Lmode n⁆ =
          (m - n : ℝ) • S.sugawara.bridge.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • S.sugawara.bridge.virasoro.central) :
    ⁅S.sugawara.bridge.virasoro.Lmode m, S.sugawara.bridge.virasoro.Lmode n⁆ =
      (m - n : ℝ) • S.sugawara.bridge.virasoro.Lmode (m + n) +
        (virasoroCentralCoefficient m n : ℝ) • S.sugawara.bridge.virasoro.central :=
  S.sugawara.bridge.virasoro.bracket_modes_normalized hvir m n


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
The supplied Sugawara Virasoro modes act on positive lightcone currents by the
inherited affine/Virasoro action law.
-/
@[rep_depth operator]
theorem sugawara_virasoro_acts_on_uPlusCurrent
    (m n : ℤ) :
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅S.kanAffine.affineLightCone.bridge.virasoro.Lmode m,
          S.kanAffine.affineLightCone.bridge.affine.Current n X⁆ =
          (-(n : ℝ)) • S.kanAffine.affineLightCone.bridge.affine.Current (m + n) X) →
    ⁅S.sugawara.bridge.virasoro.Lmode m, S.kanAffine.uPlusCurrent n⁆ =
      (-(n : ℝ)) • S.kanAffine.uPlusCurrent (m + n) := by
  intro hact
  have hVir := S.kanAffine.affineLightCone.bridge_virasoro_eq
  rw [S.uses_lightcone_affine_bridge, hVir]
  exact S.kanAffine.virasoro_acts_on_uPlusCurrent m n hact


/--
The supplied Sugawara Virasoro modes act on negative lightcone currents by the
inherited affine/Virasoro action law.
-/
@[rep_depth operator]
theorem sugawara_virasoro_acts_on_uMinusCurrent
    (m n : ℤ) :
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅S.kanAffine.affineLightCone.bridge.virasoro.Lmode m,
          S.kanAffine.affineLightCone.bridge.affine.Current n X⁆ =
          (-(n : ℝ)) • S.kanAffine.affineLightCone.bridge.affine.Current (m + n) X) →
    ⁅S.sugawara.bridge.virasoro.Lmode m, S.kanAffine.uMinusCurrent n⁆ =
      (-(n : ℝ)) • S.kanAffine.uMinusCurrent (m + n) := by
  intro hact
  have hVir := S.kanAffine.affineLightCone.bridge_virasoro_eq
  rw [S.uses_lightcone_affine_bridge, hVir]
  exact S.kanAffine.virasoro_acts_on_uMinusCurrent m n hact

end Calibration

end InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration
