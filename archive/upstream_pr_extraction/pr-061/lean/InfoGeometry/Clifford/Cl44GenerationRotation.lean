import InfoGeometry.Canonical.SplitHierarchy
import InfoGeometry.Quantum.SplitTrialityKernel

/-!
# Split `Cl(4,4)` generation rotation

This file records the label-level `S₃` rotation layer suggested by the split
triality corridor.

What is owned here:

* the existing split hierarchy diagnostic packet;
* a concrete `Fin 3` label action by permutations;
* a canonical packet packaging those two surfaces together.

What is not claimed here:

* no `Cl(5,5)` embedding theorem;
* no three-generation fermion classification theorem;
* no split-octonion multiplication theorem.

This is deliberately a rotation/label packet, not a hidden replacement for the
conformal or projective comparison layers.
-/

namespace InfoGeometry.Clifford.Cl44GenerationRotation

open InfoGeometry.Canonical.SplitHierarchy

/-- The three generation labels used by the diagnostic rotation layer. -/
abbrev GenerationLabel : Type :=
  Fin 3

/--
The canonical `S₃` action on generation labels.

This is only the label action; it does not assert a new family theorem.
-/
def rotateGenerationLabel (σ : Equiv.Perm GenerationLabel) :
    GenerationLabel → GenerationLabel :=
  fun i => σ i

@[simp] theorem rotateGenerationLabel_apply
    (σ : Equiv.Perm GenerationLabel) (i : GenerationLabel) :
    rotateGenerationLabel σ i = σ i :=
  rfl

@[simp] theorem rotateGenerationLabel_id :
    rotateGenerationLabel (Equiv.refl GenerationLabel) = id :=
  rfl

@[simp] theorem rotateGenerationLabel_comp
    (σ τ : Equiv.Perm GenerationLabel) :
    rotateGenerationLabel (σ.trans τ)
      = (rotateGenerationLabel τ).comp (rotateGenerationLabel σ) :=
  by
    funext i
    simpa [rotateGenerationLabel, Function.comp] using
      (Equiv.trans_apply σ τ i)

/--
Diagnostic packet for the split `Cl(4,4)` generation layer.

The hierarchy package carries the existing split `Cl(4,4)` / triality /
conformal-normalization readout, while the label action records the `S₃`
rotation on three generation labels.
-/
structure SplitCl44GenerationRotationPacket where
  hierarchy : SplitHierarchyDiagnostic
  labelAction : Equiv.Perm GenerationLabel → GenerationLabel → GenerationLabel
  labelAction_id : labelAction (Equiv.refl GenerationLabel) = id
  labelAction_comp :
    ∀ σ τ : Equiv.Perm GenerationLabel,
      labelAction (σ.trans τ) = (labelAction τ).comp (labelAction σ)

/-- Canonical label-level generation-rotation packet. -/
def canonicalGenerationRotationPacket : SplitCl44GenerationRotationPacket where
  hierarchy := canonicalDiagnostic
  labelAction := rotateGenerationLabel
  labelAction_id := by ext i; rfl
  labelAction_comp := by
    intro σ τ
    funext i
    simpa [rotateGenerationLabel, Function.comp] using
      (Equiv.trans_apply σ τ i)

/-- The canonical packet carries the canonical hierarchy diagnostic. -/
theorem canonicalGenerationRotationPacket_hierarchy :
    canonicalGenerationRotationPacket.hierarchy = canonicalDiagnostic :=
  rfl

/-- The canonical packet rotates labels by the canonical `S₃` action. -/
theorem canonicalGenerationRotationPacket_labelAction :
    canonicalGenerationRotationPacket.labelAction = rotateGenerationLabel :=
  rfl

end InfoGeometry.Clifford.Cl44GenerationRotation
