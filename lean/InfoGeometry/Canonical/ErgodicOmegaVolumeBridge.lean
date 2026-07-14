import InfoGeometry.Canonical.ErgodicFixedPointBridge
import InfoGeometry.Canonical.StandardFormOmegaVolumeBridge

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# InfoGeometry.Canonical.ErgodicOmegaVolumeBridge

Adapter from ergodic self-similar fixed operators to the standard-form
`Ω`-volume readout.

This file does not prove a von Neumann ergodic theorem and does not construct a
centralizer.  Those analytic facts are model-level input.  The bridge records
the calibrated socket:

* the ergodic owner supplies modular/scale fixed operators;
* the standard-form owner supplies finite natural-cone face expectations;
* a model-specific operator translation identifies fixed-point readouts with
  the existing `Ω`-localized volume readout.
-/

namespace ErgodicOmegaVolumeBridge

open InfoGeometry.Canonical.ErgodicFixedPointBridge
open InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
open InfoGeometry.Krein
open InfoGeometry.Volume.ConnesCocycle

section Core

variable {E H LieAlgebra Word : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace (DoubledSpace H)]
variable [Fintype Word] [DecidableEq Word]

local notation "EndE" => E →L[ℝ] E
local notation "H₂" => DoubledSpace H
local notation "VolEnd" => AlgebraEnd H

/--
Calibration bridge from operator ergodic fixed points to natural-cone
`Ω`-localized face volumes.

`toVolumeOperator` is explicit witness data because the ergodic observable
carrier and the standard-form volume carrier need not be definitionally the
same type in every model.
-/
@[rep_depth transport]
structure Bridge where
  /-- Modular-flow/renormalization fixed-point owner. -/
  ergodic :
    OperatorErgodicFixedPointBridge (E := E) (LieAlgebra := LieAlgebra)

  /-- Standard-form `Ω`-expectation finite face-volume owner. -/
  omegaVolume :
    NaturalConeVolumeBridge (H := H) Word

  /-- Model-supplied translation from ergodic observables to volume operators. -/
  toVolumeOperator :
    EndE → VolEnd

  /-- The fixed-point observable assigned to a finite word/face. -/
  fixedOperatorOfWord :
    Word → EndE

  /-- Each word-observable is fixed by modular time and dyadic scale. -/
  fixedOperator_selfSimilar :
    ∀ w : Word,
      OperatorErgodicFixedPointBridge.IsSelfSimilarFixedPoint
        ergodic (fixedOperatorOfWord w)

  /--
  Calibration: the fixed-point observable read through the standard-form
  volume state is the existing `Ω`-localized face expectation.
  -/
  fixedOperator_volume_calibration :
    ∀ w : Word,
      omegaVolume.volumeState (toVolumeOperator (fixedOperatorOfWord w)) =
        NaturalConeVolumeBridge.localizedExpectation omegaVolume w

namespace Bridge

variable (B : Bridge
  (E := E) (H := H) (LieAlgebra := LieAlgebra) (Word := Word))

/-- The word fixed-point observable is modular-time fixed. -/
@[rep_depth transport]
theorem fixedOperator_isModularFixed
    (w : Word) :
    OperatorErgodicFixedPointBridge.IsModularFixed
      B.ergodic (B.fixedOperatorOfWord w) :=
  (B.fixedOperator_selfSimilar w).1

/-- The word fixed-point observable is renormalization-scale fixed. -/
@[rep_depth transport]
theorem fixedOperator_isScaleFixed
    (w : Word) :
    OperatorErgodicFixedPointBridge.IsScaleFixed
      B.ergodic (B.fixedOperatorOfWord w) :=
  (B.fixedOperator_selfSimilar w).2

/--
The modular fixed-point observable lies in the model-supplied centralizer-like
sector.
-/
@[rep_depth transport]
theorem fixedOperator_mem_centralizerLike
    (w : Word) :
    B.ergodic.centralizerLike (B.fixedOperatorOfWord w) :=
  B.ergodic.modularFixed_mem_centralizerLike
    (A := B.fixedOperatorOfWord w) (B.fixedOperator_isModularFixed w)

/--
The calibrated volume of a self-similar fixed observable is the standard-form
localized `Ω`-face expectation.
-/
@[rep_depth transport]
theorem fixedOperator_volume_eq_localizedExpectation
    (w : Word) :
    B.omegaVolume.volumeState
        (B.toVolumeOperator (B.fixedOperatorOfWord w)) =
      NaturalConeVolumeBridge.localizedExpectation B.omegaVolume w :=
  B.fixedOperator_volume_calibration w

/--
Readback through the concrete Hestenes--Krein `Ω` expectation:
the calibrated fixed-point volume is `[L_w Ω, Ω]_J`.
-/
@[rep_depth transport]
theorem fixedOperator_volume_eq_omega_kreinExpectation
    (w : Word) :
    B.omegaVolume.volumeState
        (B.toVolumeOperator (B.fixedOperatorOfWord w)) =
      KreinSpace.kreinInner (H := H₂)
        ((NaturalConeVolumeBridge.localizationOp B.omegaVolume w)
          B.omegaVolume.Omega)
        B.omegaVolume.Omega := by
  rw [B.fixedOperator_volume_eq_localizedExpectation w]
  exact
    NaturalConeVolumeBridge.localizedExpectation_eq_omega_kreinExpectation
      B.omegaVolume w

end Bridge

end Core

end ErgodicOmegaVolumeBridge
