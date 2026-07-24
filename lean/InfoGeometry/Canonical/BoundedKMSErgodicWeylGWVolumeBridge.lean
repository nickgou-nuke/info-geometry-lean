import InfoGeometry.Canonical.BoundedKMSErgodicOmegaVolumeBridge
import InfoGeometry.Canonical.WeylGWVolumeBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# InfoGeometry.Canonical.BoundedKMSErgodicWeylGWVolumeBridge

Adapter joining the state-functional bounded-KMS ergodic fixed-point socket to
the existing projective Weyl/GW physical-volume socket.

This file does not introduce a new determinant or GW-volume owner.  Phase
volume/determinant invariance is explicit model data.  The proved content is
the readback chain:

```text
state-functional KMS self-similar fixed operator
  → Ω-localized natural-cone expectation
  → calibrated projective Weyl/GW physical volume.
```
-/

namespace InfoGeometry.Canonical.BoundedKMSErgodicWeylGWVolumeBridge

open InfoGeometry.Canonical.BoundedKMSErgodicOmegaVolumeBridge
open InfoGeometry.Canonical.BoundedKMSErgodicFixedPointBridge
open InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
open InfoGeometry.Canonical.WeylGWVolumeBridge
open InfoGeometry.Krein

section Core

variable {E H LieAlgebra Functional State G T Target Coeff Word : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace (DoubledSpace H)]
variable [Fintype Word] [DecidableEq Word]

local notation "EndE" => E →L[ℝ] E

/--
Fusion of a state-functional bounded-KMS self-similar fixed-point readout with
the already-owned standard-form face Weyl/GW physical-volume readout.

`phaseVolume` is a determinant/phase-volume scalar readout only where the
model supplies it.  Its modular-flow and renormalization invariance are
witness fields, not derived Type-III determinant claims.
-/
@[rep_depth projective]
structure Bridge where
  /-- State-functional bounded-KMS fixed-point to `Ω`-volume adapter. -/
  ergodicOmega :
    InfoGeometry.Canonical.BoundedKMSErgodicOmegaVolumeBridge.Bridge
      (E := E) (H := H)
      (LieAlgebra := LieAlgebra) (Word := Word)

  /-- Existing standard-form face to projective Weyl/GW physical-volume fusion. -/
  faceGW :
    StandardFormFaceWeylGWVolumeFusion (H := H) (Functional := Functional)
      (State := State) (G := G) (T := T) (Target := Target)
      (Coeff := Coeff) (Word := Word)

  /-- The two adapters use the same `Ω`-volume owner. -/
  omegaVolume_eq :
    faceGW.omegaVolume = ergodicOmega.omegaVolume

  /-- Optional determinant/phase-volume readout on ergodic observables. -/
  phaseVolume :
    EndE → ℝ

  /-- Phase-volume is invariant under the calibrated bounded KMS flow. -/
  phaseVolume_flow_invariant :
    ∀ (t : ℝ) (A : EndE),
      phaseVolume (ergodicOmega.ergodic.kms.flowDatum.flow t A) = phaseVolume A

  /--
  Phase-volume is invariant on self-similar fixed points under the supplied
  renormalization map.
  -/
  phaseVolume_renorm_invariant_of_selfSimilar :
    ∀ A : EndE,
      BoundedKMSErgodicFixedPointBridge.Bridge.IsSelfSimilarFixedPoint
        ergodicOmega.ergodic A →
        phaseVolume (ergodicOmega.ergodic.renorm A) = phaseVolume A

namespace Bridge

variable (B : Bridge
  (E := E) (H := H) (LieAlgebra := LieAlgebra)
  (Functional := Functional) (State := State) (G := G) (T := T)
  (Target := Target) (Coeff := Coeff) (Word := Word))

/--
Main adapter readback:
the calibrated physical Weyl/GW volume of a word-state is the volume of the
corresponding state-functional bounded-KMS self-similar fixed operator.
-/
@[rep_depth projective]
theorem physicalVolume_eq_fixedOperatorVolume
    (w : Word) :
    B.faceGW.projectiveFace.base.physicalVolume (B.faceGW.wordToState w) =
      B.ergodicOmega.omegaVolume.volumeState
        (B.ergodicOmega.toVolumeOperator
          (B.ergodicOmega.fixedOperatorOfWord w)) := by
  calc
    B.faceGW.projectiveFace.base.physicalVolume (B.faceGW.wordToState w)
        =
      NaturalConeVolumeBridge.localizedExpectation B.faceGW.omegaVolume w :=
        StandardFormFaceWeylGWVolumeFusion.physicalVolume_eq_localizedExpectation
          B.faceGW w
    _ =
      NaturalConeVolumeBridge.localizedExpectation B.ergodicOmega.omegaVolume w := by
        rw [B.omegaVolume_eq]
    _ =
      B.ergodicOmega.omegaVolume.volumeState
        (B.ergodicOmega.toVolumeOperator
          (B.ergodicOmega.fixedOperatorOfWord w)) := by
        rw [BoundedKMSErgodicOmegaVolumeBridge.Bridge.fixedOperator_volume_eq_localizedExpectation
          B.ergodicOmega w]

/-- The word fixed-point phase-volume is invariant under bounded KMS time. -/
@[rep_depth projective]
theorem fixedOperator_phaseVolume_flow_invariant
    (w : Word) (t : ℝ) :
    B.phaseVolume
        (B.ergodicOmega.ergodic.kms.flowDatum.flow t
          (B.ergodicOmega.fixedOperatorOfWord w)) =
      B.phaseVolume (B.ergodicOmega.fixedOperatorOfWord w) :=
  B.phaseVolume_flow_invariant t (B.ergodicOmega.fixedOperatorOfWord w)

/--
The word fixed-point phase-volume is invariant under the dyadic
renormalization map.
-/
@[rep_depth projective]
theorem fixedOperator_phaseVolume_renorm_invariant
    (w : Word) :
    B.phaseVolume
        (B.ergodicOmega.ergodic.renorm
          (B.ergodicOmega.fixedOperatorOfWord w)) =
      B.phaseVolume (B.ergodicOmega.fixedOperatorOfWord w) :=
  B.phaseVolume_renorm_invariant_of_selfSimilar
    (B.ergodicOmega.fixedOperatorOfWord w)
    (B.ergodicOmega.fixedOperator_selfSimilar w)

/-- The word fixed-point observable is in the supplied centralizer-like sector. -/
@[rep_depth projective]
theorem fixedOperator_mem_centralizerLike
    (w : Word) :
    B.ergodicOmega.ergodic.centralizerLike
      (B.ergodicOmega.fixedOperatorOfWord w) :=
  BoundedKMSErgodicOmegaVolumeBridge.Bridge.fixedOperator_mem_centralizerLike
    B.ergodicOmega w

/-- The existing projective Weyl/GW physical-volume scale invariance is retained. -/
@[rep_depth projective]
theorem physicalVolume_scale_invariant
    (c : ℝ) (hc : c ≠ 0) (s : State) :
    B.faceGW.projectiveFace.base.physicalVolume
        (B.faceGW.projectiveFace.base.scaleState c s) =
      B.faceGW.projectiveFace.base.physicalVolume s :=
  StandardFormFaceWeylGWVolumeFusion.physicalVolume_scale_invariant
    B.faceGW c hc s

end Bridge

end Core

end InfoGeometry.Canonical.BoundedKMSErgodicWeylGWVolumeBridge
