import InfoGeometry.Canonical.StandardFormNaturalConeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ModularCartanCantorSystem
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# InfoGeometry.Canonical.StandardFormOmegaVolumeBridge

Trace-to-expectation volume readout for the theorem-safe standard-form natural
cone bridge.

This file does not introduce a `VonNeumannAlgebra` class and does not use a
trace/determinant primitive.  It records the Type-III-safe replacement:

* finite Wigner--Jones/cylinder atoms are bounded projectors supplied by the
  existing natural-cone face bridge;
* volume is a normalized finite-additive state/readout on bounded operators;
* in concrete Hestenes--Krein models the readout is the real vacuum expectation
  `[A Ω, Ω]_J`;
* logarithmic sector volume is routed through the existing projective cylinder
  log-potential API.
-/

namespace InfoGeometry.Canonical.StandardFormOmegaVolumeBridge

open InfoGeometry.Canonical.StandardFormNaturalConeBridge
open InfoGeometry.Canonical.ModularCartanCantorSystem
open InfoGeometry.Volume.ConnesCocycle
open InfoGeometry.Krein

section Core

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace (DoubledSpace H)]

local notation "H₂" => DoubledSpace H
local notation "EndH" => AlgebraEnd H

noncomputable local instance omegaVolumeNormedRing : NormedRing EndH := inferInstance
noncomputable local instance omegaVolumeNormedAlgebra : NormedAlgebra ℝ EndH := inferInstance
local instance omegaVolumeTopologicalRing : IsTopologicalRing EndH := inferInstance
local instance omegaVolumeCompleteSpace : CompleteSpace EndH := inferInstance
local instance omegaVolumeSMulCommClass : SMulCommClass ℝ EndH EndH := inferInstance
local instance omegaVolumeIsScalarTower : IsScalarTower ℝ EndH EndH := inferInstance

/--
Finite-additive normalized expectation replacing trace on a finite atom partition.

The readout is intentionally real-valued: complex KMS analyticity is translated
elsewhere into the Hestenes real phase-axis language.  The field
`volumeState_eq_omega_kreinExpectation` identifies the readout with the Krein
vacuum expectation in concrete standard-form/Hestenes models.
-/
@[rep_depth operator]
structure NaturalConeVolumeBridge
    (Word : Type*) [Fintype Word] [DecidableEq Word]
    extends ModularNaturalConeFaceBridge (H := H) Word where
  /-- Distinguished standard-form/vacuum vector `Ω`. -/
  Omega : H₂

  /-- `Ω` lies in the supplied natural-cone shadow. -/
  Omega_mem_naturalCone : Omega ∈ naturalCone

  /-- Trace-replacement volume state. -/
  volumeState : EndH → ℝ

  /-- Normalization: the total unit volume is one. -/
  volumeState_one : volumeState (1 : EndH) = 1

  /-- Finite additivity of the volume state over the installed atom family. -/
  volumeState_word_sum :
    ∀ A : Word → EndH,
      volumeState (∑ w : Word, A w) = ∑ w : Word, volumeState (A w)

  /-- Concrete Hestenes--Krein readback: `ωΩ(A) = [AΩ, Ω]_J`. -/
  volumeState_eq_omega_kreinExpectation :
    ∀ A : EndH,
      volumeState A = KreinSpace.kreinInner (H := H₂) (A Omega) Omega

  /-- Wigner--Jones/cylinder atom partition of unity. -/
  cylinderProjector_partition_unity :
    (∑ w : Word, cylinderProjector w) = (1 : EndH)

namespace NaturalConeVolumeBridge

variable {Word : Type*}
variable [Fintype Word] [DecidableEq Word]
variable (B : NaturalConeVolumeBridge (H := H) Word)

/-- The supplied cylinder projector re-read as a Wigner--Jones atom. -/
@[rep_depth operator]
noncomputable def wignerJonesAtom (w : Word) : EndH :=
  B.cylinderProjector w

/-- Expectation/volume of a Wigner--Jones atom. -/
@[rep_depth operator]
noncomputable def atomExpectation (w : Word) : ℝ :=
  B.volumeState (NaturalConeVolumeBridge.wignerJonesAtom B w)

/-- Localized face operator `L_w = p_w Jp_wJ` from the natural-cone bridge. -/
@[rep_depth operator]
noncomputable def localizationOp (w : Word) : EndH :=
  ModularNaturalConeFaceBridge.localizationOp B.toModularNaturalConeFaceBridge w

/-- Localized face expectation using the modular face operator `L_w = p_w Jp_wJ`. -/
@[rep_depth operator]
noncomputable def localizedExpectation (w : Word) : ℝ :=
  B.volumeState (NaturalConeVolumeBridge.localizationOp B w)

/-- The atom expectation is the Krein vacuum expectation `[p_w Ω, Ω]_J`. -/
@[rep_depth operator]
theorem atomExpectation_eq_omega_kreinExpectation (w : Word) :
    NaturalConeVolumeBridge.atomExpectation B w =
      KreinSpace.kreinInner (H := H₂)
        ((NaturalConeVolumeBridge.wignerJonesAtom B w) B.Omega) B.Omega := by
  unfold atomExpectation
  rw [B.volumeState_eq_omega_kreinExpectation]

/-- The localized face expectation is `[L_w Ω, Ω]_J`. -/
@[rep_depth operator]
theorem localizedExpectation_eq_omega_kreinExpectation (w : Word) :
    B.volumeState (NaturalConeVolumeBridge.localizationOp B w) =
      KreinSpace.kreinInner (H := H₂)
        ((NaturalConeVolumeBridge.localizationOp B w) B.Omega) B.Omega := by
  rw [B.volumeState_eq_omega_kreinExpectation]

/-- Readback of the supplied atom partition of unity. -/
@[rep_depth operator]
theorem wignerJonesAtom_partition_unity :
    (∑ w : Word, NaturalConeVolumeBridge.wignerJonesAtom B w) = (1 : EndH) := by
  simpa [wignerJonesAtom] using B.cylinderProjector_partition_unity

/--
The total expectation of a finite atom partition is the normalized unit volume.

This is the theorem-safe replacement for `Tr(∑ p_w) = Tr(1)`: no trace appears.
-/
@[rep_depth operator]
theorem total_expectation_is_unity :
    (∑ w : Word, NaturalConeVolumeBridge.atomExpectation B w) = 1 := by
  calc
    (∑ w : Word, NaturalConeVolumeBridge.atomExpectation B w)
        = B.volumeState (∑ w : Word, NaturalConeVolumeBridge.wignerJonesAtom B w) := by
            simpa [atomExpectation] using
              (B.volumeState_word_sum
                (fun w : Word => NaturalConeVolumeBridge.wignerJonesAtom B w)).symm
    _ = B.volumeState (1 : EndH) := by
          rw [NaturalConeVolumeBridge.wignerJonesAtom_partition_unity B]
    _ = 1 := B.volumeState_one

/--
If the modular localizers themselves form a partition of unity, their localized
expectations also sum to one.
-/
@[rep_depth operator]
theorem total_localizedExpectation_is_unity
    (hLocalPartition :
      (∑ w : Word, NaturalConeVolumeBridge.localizationOp B w) = (1 : EndH)) :
    (∑ w : Word, B.volumeState (NaturalConeVolumeBridge.localizationOp B w)) = 1 := by
  calc
    (∑ w : Word, B.volumeState (NaturalConeVolumeBridge.localizationOp B w))
        = B.volumeState (∑ w : Word, NaturalConeVolumeBridge.localizationOp B w) := by
            simpa using
              (B.volumeState_word_sum (fun w : Word => NaturalConeVolumeBridge.localizationOp B w)).symm
    _ = B.volumeState (1 : EndH) := by rw [hLocalPartition]
    _ = 1 := B.volumeState_one

/-- Type-III log-volume potential of an atom: `-log ωΩ(p_w)`. -/
@[rep_depth projective]
noncomputable def modularVolumePotential (w : Word) : ℝ :=
  cylinderLogPotential (fun v : Word => NaturalConeVolumeBridge.atomExpectation B v) w

/-- Type-III log-volume increment between two atoms/cylinders. -/
@[rep_depth projective]
noncomputable def modularVolumeIncrement (parent child : Word) : ℝ :=
  cylinderLogIncrement
    (fun v : Word => NaturalConeVolumeBridge.atomExpectation B v) parent child

/-- Definitional readback of the log-volume potential. -/
@[rep_depth projective]
theorem modularVolumePotential_eq_neg_log_atomExpectation (w : Word) :
    NaturalConeVolumeBridge.modularVolumePotential B w =
      -Real.log (NaturalConeVolumeBridge.atomExpectation B w) := by
  rfl

/-- Definitional readback of the log-volume increment. -/
@[rep_depth projective]
theorem modularVolumeIncrement_eq_neg_log_ratio (parent child : Word) :
    NaturalConeVolumeBridge.modularVolumeIncrement B parent child =
      -Real.log
        (NaturalConeVolumeBridge.atomExpectation B child /
          NaturalConeVolumeBridge.atomExpectation B parent) := by
  rfl

/--
The logarithmic increment is projective: common positive rescaling of all atom
weights cancels.  This is the finite atom shadow of the Connes/Weyl cocycle
being a projective logarithmic gauge.
-/
@[rep_depth projective]
theorem modularVolumeIncrement_common_pos_smul
    (parent child : Word) {c : ℝ} (hc : 0 < c) :
    cylinderLogIncrement
        (fun w : Word => c * NaturalConeVolumeBridge.atomExpectation B w) parent child =
      NaturalConeVolumeBridge.modularVolumeIncrement B parent child := by
  simpa [modularVolumeIncrement] using
    cylinderLogIncrement_common_pos_smul
      (weight := fun w : Word => NaturalConeVolumeBridge.atomExpectation B w)
      parent child (hc := hc)

end NaturalConeVolumeBridge

end Core

end InfoGeometry.Canonical.StandardFormOmegaVolumeBridge

end
