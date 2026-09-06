import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.RelativeModularCore

Relative modular carrier data above the current standard-form seed.

This file stays intentionally narrow:
- projective relative-state pairs,
- their exact cocycle laws from `RelativePotentialCore`,
- restriction/reweighting data for local subsystems,
- the shift formulas induced by restricted log-density reweighting.

It does **not** yet define the full relative modular operator `Δ_{ω|μ}` or a
standard-form von Neumann algebra package. Those belong in later owner files.
-/

namespace InfoGeometry.Canonical.RelativeModularCore

open InfoGeometry.Canonical.PositiveRayCore
open RelativePotentialCore
open StandardFormCore

section RelativeStates

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Ordered pair of projective positive states for relative modular data. -/
structure RelativeStatePair
    (α : Type*) [Fintype α] [Nonempty α] where
  source : PositiveRay α
  target : PositiveRay α

/-- Projective relative density for a state pair. -/
@[rep_depth projective]
noncomputable def RelativeStatePair.density
    (R : RelativeStatePair α) : α → ℝ :=
  relativeDensity R.source R.target

/-- Projective relative logarithmic density for a state pair. -/
@[rep_depth projective]
noncomputable def RelativeStatePair.logDensity
    (R : RelativeStatePair α) : α → ℝ :=
  relativeLogDensity R.source R.target

/-- Projective relative modular potential for a state pair. -/
@[rep_depth projective]
noncomputable def RelativeStatePair.modularPotential
    (R : RelativeStatePair α) : α → ℝ :=
  relativeModularPotential R.source R.target

@[rep_depth projective, simp] theorem RelativeStatePair.modularPotential_eq_neg_logDensity
    (R : RelativeStatePair α) (a : α) :
    R.modularPotential a = -R.logDensity a := by
  exact relativeModularPotential_eq_neg_relativeLogDensity R.source R.target a

@[rep_depth projective, simp] theorem
    RelativeStatePair.modularPotential_eq_logDensity_target_sub_source
    (R : RelativeStatePair α) (a : α) :
    R.modularPotential a
      = InfoGeometry.Canonical.PositiveRayCore.logDensity (α := α) R.target a
        - InfoGeometry.Canonical.PositiveRayCore.logDensity (α := α) R.source a := by
  exact relativeModularPotential_eq_logDensity_base_sub_logDensity R.source R.target a

/-- Compose two relative state pairs along a shared middle state. -/
def RelativeStatePair.compose
    (R₁₂ R₂₃ : RelativeStatePair α) :
    RelativeStatePair α where
  source := R₁₂.source
  target := R₂₃.target

@[rep_depth projective, simp] theorem RelativeStatePair.compose_density
    (R₁₂ R₂₃ : RelativeStatePair α) (h : R₁₂.target = R₂₃.source) (a : α) :
    (R₁₂.compose R₂₃).density a = R₁₂.density a * R₂₃.density a := by
  unfold RelativeStatePair.compose
  rw [RelativeStatePair.density, RelativeStatePair.density,
    RelativeStatePair.density]
  rw [relativeDensity_cocycle R₁₂.source R₁₂.target R₂₃.target a]
  rw [h]

@[rep_depth projective, simp] theorem RelativeStatePair.compose_logDensity
    (R₁₂ R₂₃ : RelativeStatePair α) (h : R₁₂.target = R₂₃.source) (a : α) :
    (R₁₂.compose R₂₃).logDensity a = R₁₂.logDensity a + R₂₃.logDensity a := by
  unfold RelativeStatePair.compose
  rw [RelativeStatePair.logDensity, RelativeStatePair.logDensity,
    RelativeStatePair.logDensity]
  rw [relativeLogDensity_cocycle R₁₂.source R₁₂.target R₂₃.target a]
  rw [h]

@[rep_depth projective, simp] theorem RelativeStatePair.compose_modularPotential
    (R₁₂ R₂₃ : RelativeStatePair α) (h : R₁₂.target = R₂₃.source) (a : α) :
    (R₁₂.compose R₂₃).modularPotential a
      = R₁₂.modularPotential a + R₂₃.modularPotential a := by
  unfold RelativeStatePair.compose
  rw [RelativeStatePair.modularPotential, RelativeStatePair.modularPotential,
    RelativeStatePair.modularPotential]
  rw [relativeModularPotential_cocycle R₁₂.source R₁₂.target R₂₃.target a]
  rw [h]

end RelativeStates

section Restriction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {β : Type*} [Fintype β] [Nonempty β]

/--
Restriction/reweighting carrier for a local subsystem.

The local source and target log-densities are allowed to differ from the
ambient pullbacks by additive constants. These constants encode the local
reweighting needed before surface normalization.
-/
structure RestrictedRelativeModularData
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (α : Type*) [Fintype α] [Nonempty α]
    (β : Type*) [Fintype β] [Nonempty β] where
  carrier : RelativeModularBridge H α
  embed : β ↪ α
  localSource : PositiveRay β
  localTarget : PositiveRay β
  sourceLogShift : ℝ
  targetLogShift : ℝ
  source_logDensity_eq_pullback_add_shift :
    ∀ b : β,
      InfoGeometry.Canonical.PositiveRayCore.logDensity (α := β) localSource b
        = InfoGeometry.Canonical.PositiveRayCore.logDensity (α := α) carrier.source (embed b)
          + sourceLogShift
  target_logDensity_eq_pullback_add_shift :
    ∀ b : β,
      InfoGeometry.Canonical.PositiveRayCore.logDensity (α := β) localTarget b
        = InfoGeometry.Canonical.PositiveRayCore.logDensity (α := α) carrier.target (embed b)
          + targetLogShift

/-- The local source/target pair induced by the restriction data. -/
@[rep_depth projective]
noncomputable def RestrictedRelativeModularData.localPair
    (R : RestrictedRelativeModularData H α β) : RelativeStatePair β where
  source := R.localSource
  target := R.localTarget

/-- The ambient source/target pair carried by the operator bridge. -/
@[rep_depth projective]
noncomputable def RestrictedRelativeModularData.ambientPair
    (R : RestrictedRelativeModularData H α β) : RelativeStatePair α where
  source := R.carrier.source
  target := R.carrier.target

/--
Restricted relative log-density equals the ambient pullback plus the difference
between the source and target logarithmic reweightings.
-/
@[rep_depth projective, simp] theorem
    RestrictedRelativeModularData.local_logDensity_eq_pullback_add_shiftDiff
    (R : RestrictedRelativeModularData H α β) (b : β) :
    R.localPair.logDensity b
      = R.carrier.projectiveLogDensity (R.embed b)
          + (R.sourceLogShift - R.targetLogShift) := by
  unfold RelativeStatePair.logDensity RelativeModularBridge.projectiveLogDensity
  unfold RestrictedRelativeModularData.localPair
  rw [relativeLogDensity_eq_logDensity_sub_logDensity]
  rw [relativeLogDensity_eq_logDensity_sub_logDensity]
  rw [R.source_logDensity_eq_pullback_add_shift, R.target_logDensity_eq_pullback_add_shift]
  ring

/--
Restricted relative modular potential equals the ambient pullback plus the
difference between the target and source logarithmic reweightings.
-/
@[rep_depth projective, simp] theorem
    RestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R : RestrictedRelativeModularData H α β) (b : β) :
    R.localPair.modularPotential b
      = R.carrier.projectiveModularPotential (R.embed b)
          + (R.targetLogShift - R.sourceLogShift) := by
  rw [RelativeStatePair.modularPotential_eq_neg_logDensity]
  rw [RelativeModularBridge.projectiveModularPotential_eq_neg_projectiveLogDensity]
  rw [R.local_logDensity_eq_pullback_add_shiftDiff]
  ring

/-- Equal source/target reweighting preserves the pulled-back relative log-density exactly. -/
@[rep_depth projective, simp] theorem
    RestrictedRelativeModularData.local_logDensity_eq_pullback_of_equal_shift
    (R : RestrictedRelativeModularData H α β)
    (hshift : R.sourceLogShift = R.targetLogShift) (b : β) :
    R.localPair.logDensity b = R.carrier.projectiveLogDensity (R.embed b) := by
  rw [R.local_logDensity_eq_pullback_add_shiftDiff]
  rw [hshift]
  ring

/-- Equal source/target reweighting preserves the pulled-back modular potential exactly. -/
@[rep_depth projective, simp] theorem
    RestrictedRelativeModularData.local_modularPotential_eq_pullback_of_equal_shift
    (R : RestrictedRelativeModularData H α β)
    (hshift : R.sourceLogShift = R.targetLogShift) (b : β) :
    R.localPair.modularPotential b = R.carrier.projectiveModularPotential (R.embed b) := by
  rw [R.local_modularPotential_eq_pullback_add_shiftDiff]
  rw [hshift]
  ring

end Restriction

end InfoGeometry.Canonical.RelativeModularCore
