import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-!
# Affine Cl(4,4) / so(4,4) Cardy Entropy Socket

This module installs the theorem-safe correction for the affine
`so(4,4)`/`so(8)` Sugawara central charge:

`c = k * dim(g) / (k + h∨)`, with `k = 1`, `dim so(8) = 28`, `h∨ = 6`,
so `c = 4`.

The Cardy entropy layer remains witness-gated.  No Kac-Moody construction,
Sugawara theorem, or Cardy theorem is proved here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AffineCl44CardyEntropy

open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-! ## so(4,4) / so(8) Sugawara central charge -/

/--
Installed arithmetic check for the affine `so(4,4)`/`so(8)` level-one value:
`dim = 28`, `h∨ = 6`, `k = 1` gives `c = 4`.
-/
theorem sugawaraCentralCharge_so44_levelOne :
    sugawaraCentralCharge 1 28 6 = 4 := by
  norm_num [sugawaraCentralCharge]

section BridgeDatum

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : AffineVirasoroBridgeDatum Finite Alg)

/--
If an affine-Virasoro bridge is calibrated with `k = 1`, `dim = 28`, and
`h∨ = 6`, its central charge is `4`.
-/
theorem centralCharge_eq_four_of_so44_levelOne
    (hlevel : B.level = 1)
    (hdim : B.finiteDimension = 28)
    (hdual : B.dualCoxeterNumber = 6)
    (hcc : B.centralCharge =
      B.level * B.finiteDimension / (B.level + B.dualCoxeterNumber)) :
    B.centralCharge = 4 := by
  rw [hcc, hlevel, hdim, hdual]
  norm_num

end BridgeDatum

/-! ## Cardy entropy calibration -/

/--
Witness-gated Cardy entropy calibration.

The shifted energy and entropy formula are supplied by the CFT model.  This
socket only records the readout and exposes positivity under explicit regime
witnesses.
-/
structure CardyEntropyCalibration where
  centralCharge : ℝ
  L0 : ℝ
  entropy : ℝ
  shiftedEnergy : ℝ
  shiftedEnergy_eq :
    shiftedEnergy = L0 - centralCharge / 24
  centralCharge_pos :
    0 < centralCharge
  shiftedEnergy_nonneg :
    0 ≤ shiftedEnergy
  entropy_eq_cardy :
    entropy =
      2 * Real.pi * Real.sqrt ((centralCharge / 6) * shiftedEnergy)

namespace CardyEntropyCalibration

variable (C : CardyEntropyCalibration)

/-- Re-export of the supplied Cardy entropy formula. -/
theorem entropy_eq :
    C.entropy =
      2 * Real.pi * Real.sqrt ((C.centralCharge / 6) * C.shiftedEnergy) :=
  C.entropy_eq_cardy

/-- Cardy entropy is nonnegative under the supplied high-energy regime. -/
theorem entropy_nonneg :
    0 ≤ C.entropy := by
  rw [C.entropy_eq]
  positivity

end CardyEntropyCalibration

/--
Affine Drazin/Cardy boundary entropy bridge.

The equality between a Drazin-stable boundary entropy and the Cardy readout is
model-specific and remains a supplied law.
-/
structure AffineDrazinBoundaryEntropyBridge
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  affineVirasoro :
    AffineVirasoroBridgeDatum Finite Alg
  cardy :
    CardyEntropyCalibration
  entropyAgreementLaw : Prop
  entropyAgreement_holds :
    entropyAgreementLaw

namespace AffineDrazinBoundaryEntropyBridge

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : AffineDrazinBoundaryEntropyBridge (Finite := Finite) (Alg := Alg))

/-- The supplied Drazin/Cardy entropy agreement law is available. -/
theorem entropyAgreement_holds_of_bridge :
    B.entropyAgreementLaw :=
  B.entropyAgreement_holds

end AffineDrazinBoundaryEntropyBridge

end InfoGeometry.OperatorAlgebra.AffineCl44CardyEntropy
