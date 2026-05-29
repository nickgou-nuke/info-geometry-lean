import InfoGeometry.Canonical.RelativeModularPolarizedBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.RelativeModularRecomposition

Recomposition laws for the polarized restricted relative-modular corridor.

This file sits immediately above `RelativeModularPolarizedBridge` and records:
- the common ambient carrier seen by both polarized sectors,
- the sectorwise logarithmic and modular-potential defects,
- exact recomposition formulas for the whole polarized object,
- vanishing-coupling criteria separating sectorwise and global visibility.
-/

namespace InfoGeometry.Canonical.RelativeModularRecomposition

open InfoGeometry.Canonical.StandardFormCore
open InfoGeometry.Canonical.RelativeModularCore
open InfoGeometry.Canonical.RelativeModularPolarizedBridge

section Recomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {βplus : Type*} [Fintype βplus] [Nonempty βplus]
variable {βminus : Type*} [Fintype βminus] [Nonempty βminus]

/--
Minimal owner package for recomposing polarized restricted relative-modular
data back into a whole object over a common ambient carrier.
-/
structure PolarizedRecompositionData
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (α : Type*) [Fintype α] [Nonempty α]
    (βplus : Type*) [Fintype βplus] [Nonempty βplus]
    (βminus : Type*) [Fintype βminus] [Nonempty βminus] where
  polarized : PolarizedRelativeModularPair H α βplus βminus

/-- Common ambient carrier used to compare the two polarized sectors. -/
@[rep_depth projective]
noncomputable def PolarizedRecompositionData.carrier
    (R : PolarizedRecompositionData H α βplus βminus) : RelativeModularBridge H α :=
  R.polarized.plus.data.carrier

@[rep_depth projective, simp] theorem PolarizedRecompositionData.carrier_eq_plus
    (R : PolarizedRecompositionData H α βplus βminus) :
    R.carrier = R.polarized.plus.data.carrier := rfl

@[rep_depth projective, simp] theorem PolarizedRecompositionData.carrier_eq_minus
    (R : PolarizedRecompositionData H α βplus βminus) :
    R.carrier = R.polarized.minus.data.carrier := by
  exact R.polarized.sameCarrier

/-- Plus-sector logarithmic defect relative to ambient pullback. -/
@[rep_depth projective]
def PolarizedRecompositionData.plusLogDefect
    (R : PolarizedRecompositionData H α βplus βminus) : ℝ :=
  R.polarized.plus.data.sourceLogShift - R.polarized.plus.data.targetLogShift

/-- Minus-sector logarithmic defect relative to ambient pullback. -/
@[rep_depth projective]
def PolarizedRecompositionData.minusLogDefect
    (R : PolarizedRecompositionData H α βplus βminus) : ℝ :=
  R.polarized.minus.data.sourceLogShift - R.polarized.minus.data.targetLogShift

/-- Global coupling defect seen by recomposed logarithmic densities. -/
@[rep_depth projective]
def PolarizedRecompositionData.couplingLogDefect
    (R : PolarizedRecompositionData H α βplus βminus) : ℝ :=
  R.plusLogDefect + R.minusLogDefect

/-- Global coupling defect seen by recomposed modular potentials. -/
@[rep_depth projective]
def PolarizedRecompositionData.couplingPotentialDefect
    (R : PolarizedRecompositionData H α βplus βminus) : ℝ :=
  -R.couplingLogDefect

@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.couplingPotentialDefect_eq_neg_couplingLogDefect
    (R : PolarizedRecompositionData H α βplus βminus) :
    R.couplingPotentialDefect = -R.couplingLogDefect := rfl

/-- Sectorwise exactness means both polarized shift defects vanish individually. -/
@[rep_depth projective]
def PolarizedRecompositionData.sectorwiseExact
    (R : PolarizedRecompositionData H α βplus βminus) : Prop :=
  R.polarized.plus.data.sourceLogShift = R.polarized.plus.data.targetLogShift ∧
    R.polarized.minus.data.sourceLogShift = R.polarized.minus.data.targetLogShift

/-- Global vanishing coupling for the recomposed logarithmic defect. -/
@[rep_depth projective]
def PolarizedRecompositionData.vanishingCoupling
    (R : PolarizedRecompositionData H α βplus βminus) : Prop :=
  R.couplingLogDefect = 0

/-- Whole recomposed logarithmic density from the plus/minus local sectors. -/
@[rep_depth projective]
noncomputable def PolarizedRecompositionData.recomposedLogDensity
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) : ℝ :=
  R.polarized.plus.data.localPair.logDensity bplus
    + R.polarized.minus.data.localPair.logDensity bminus

/-- Whole recomposed modular potential from the plus/minus local sectors. -/
@[rep_depth projective]
noncomputable def PolarizedRecompositionData.recomposedModularPotential
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) : ℝ :=
  R.polarized.plus.data.localPair.modularPotential bplus
    + R.polarized.minus.data.localPair.modularPotential bminus

/--
Ambient logarithmic pullback seen separately by the plus and minus sector
embeddings before collapsing to a common carrier.
-/
@[rep_depth projective]
noncomputable def PolarizedRecompositionData.recomposedAmbientLogDensity
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) : ℝ :=
  R.polarized.plus.data.carrier.projectiveLogDensity (R.polarized.plus.data.embed bplus)
    + R.polarized.minus.data.carrier.projectiveLogDensity (R.polarized.minus.data.embed bminus)

/--
Ambient modular-potential pullback seen separately by the plus and minus sector
embeddings before collapsing to a common carrier.
-/
@[rep_depth projective]
noncomputable def PolarizedRecompositionData.recomposedAmbientModularPotential
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) : ℝ :=
  R.polarized.plus.data.carrier.projectiveModularPotential (R.polarized.plus.data.embed bplus)
    + R.polarized.minus.data.carrier.projectiveModularPotential (R.polarized.minus.data.embed bminus)

/-- Ambient logarithmic pullback rewritten through the common carrier. -/
@[rep_depth projective]
noncomputable def PolarizedRecompositionData.recomposedCommonCarrierLogDensity
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) : ℝ :=
  R.carrier.projectiveLogDensity (R.polarized.plus.data.embed bplus)
    + R.carrier.projectiveLogDensity (R.polarized.minus.data.embed bminus)

/-- Ambient modular-potential pullback rewritten through the common carrier. -/
@[rep_depth projective]
noncomputable def PolarizedRecompositionData.recomposedCommonCarrierModularPotential
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) : ℝ :=
  R.carrier.projectiveModularPotential (R.polarized.plus.data.embed bplus)
    + R.carrier.projectiveModularPotential (R.polarized.minus.data.embed bminus)

/-- Global exactness of logarithmic recomposition through the common carrier. -/
@[rep_depth projective]
def PolarizedRecompositionData.exactLogRecomposition
    (R : PolarizedRecompositionData H α βplus βminus) : Prop :=
  ∀ bplus : βplus, ∀ bminus : βminus,
    R.recomposedLogDensity bplus bminus = R.recomposedCommonCarrierLogDensity bplus bminus

/-- Global exactness of modular-potential recomposition through the common carrier. -/
@[rep_depth projective]
def PolarizedRecompositionData.exactPotentialRecomposition
    (R : PolarizedRecompositionData H α βplus βminus) : Prop :=
  ∀ bplus : βplus, ∀ bminus : βminus,
    R.recomposedModularPotential bplus bminus
      = R.recomposedCommonCarrierModularPotential bplus bminus

@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedAmbientLogDensity_eq_commonCarrier
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) :
    R.recomposedAmbientLogDensity bplus bminus = R.recomposedCommonCarrierLogDensity bplus bminus := by
  unfold PolarizedRecompositionData.recomposedAmbientLogDensity
  unfold PolarizedRecompositionData.recomposedCommonCarrierLogDensity
  have hminus :
      R.polarized.plus.data.carrier.projectiveLogDensity (R.polarized.minus.data.embed bminus)
        = R.polarized.minus.data.carrier.projectiveLogDensity (R.polarized.minus.data.embed bminus) := by
    simpa using congrArg
      (fun C =>
        RelativeModularBridge.projectiveLogDensity (H := H) (α := α) C
          (R.polarized.minus.data.embed bminus))
      R.polarized.sameCarrier
  simpa [PolarizedRecompositionData.carrier] using hminus.symm

@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedAmbientModularPotential_eq_commonCarrier
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) :
    R.recomposedAmbientModularPotential bplus bminus
      = R.recomposedCommonCarrierModularPotential bplus bminus := by
  unfold PolarizedRecompositionData.recomposedAmbientModularPotential
  unfold PolarizedRecompositionData.recomposedCommonCarrierModularPotential
  have hminus :
      R.polarized.plus.data.carrier.projectiveModularPotential
          (R.polarized.minus.data.embed bminus)
        = R.polarized.minus.data.carrier.projectiveModularPotential
            (R.polarized.minus.data.embed bminus) := by
    simpa using congrArg
      (fun C =>
        RelativeModularBridge.projectiveModularPotential (H := H) (α := α) C
          (R.polarized.minus.data.embed bminus))
      R.polarized.sameCarrier
  simpa [PolarizedRecompositionData.carrier] using hminus.symm

/-- Exact recomposition of logarithmic density into ambient pullback plus coupling defect. -/
@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedLogDensity_eq_ambient_add_coupling
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) :
    R.recomposedLogDensity bplus bminus
      = R.recomposedAmbientLogDensity bplus bminus + R.couplingLogDefect := by
  unfold PolarizedRecompositionData.recomposedLogDensity
  unfold PolarizedRecompositionData.recomposedAmbientLogDensity
  unfold PolarizedRecompositionData.couplingLogDefect
  unfold PolarizedRecompositionData.plusLogDefect
  unfold PolarizedRecompositionData.minusLogDefect
  rw [PlusRestrictedRelativeModularData.local_logDensity_eq_pullback_add_shiftDiff
    (R := R.polarized.plus) (b := bplus)]
  rw [MinusRestrictedRelativeModularData.local_logDensity_eq_pullback_add_shiftDiff
    (R := R.polarized.minus) (b := bminus)]
  ring

/-- Exact recomposition of logarithmic density through the common carrier plus coupling defect. -/
@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_add_coupling
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) :
    R.recomposedLogDensity bplus bminus
      = R.recomposedCommonCarrierLogDensity bplus bminus + R.couplingLogDefect := by
  rw [PolarizedRecompositionData.recomposedLogDensity_eq_ambient_add_coupling]
  rw [PolarizedRecompositionData.recomposedAmbientLogDensity_eq_commonCarrier]

/-- Exact recomposition of modular potential into ambient pullback plus coupling defect. -/
@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedModularPotential_eq_ambient_add_coupling
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) :
    R.recomposedModularPotential bplus bminus
      = R.recomposedAmbientModularPotential bplus bminus + R.couplingPotentialDefect := by
  unfold PolarizedRecompositionData.recomposedModularPotential
  unfold PolarizedRecompositionData.recomposedAmbientModularPotential
  unfold PolarizedRecompositionData.couplingPotentialDefect
  unfold PolarizedRecompositionData.couplingLogDefect
  unfold PolarizedRecompositionData.plusLogDefect
  unfold PolarizedRecompositionData.minusLogDefect
  rw [PlusRestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R := R.polarized.plus) (b := bplus)]
  rw [MinusRestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R := R.polarized.minus) (b := bminus)]
  ring

/-- Exact recomposition of modular potential through the common carrier plus coupling defect. -/
@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_add_coupling
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) :
    R.recomposedModularPotential bplus bminus
      = R.recomposedCommonCarrierModularPotential bplus bminus + R.couplingPotentialDefect := by
  rw [PolarizedRecompositionData.recomposedModularPotential_eq_ambient_add_coupling]
  rw [PolarizedRecompositionData.recomposedAmbientModularPotential_eq_commonCarrier]

/-- Recomposition still respects the modular-potential equals minus log-density law. -/
@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedModularPotential_eq_neg_recomposedLogDensity
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) :
    R.recomposedModularPotential bplus bminus = -R.recomposedLogDensity bplus bminus := by
  unfold PolarizedRecompositionData.recomposedModularPotential
  unfold PolarizedRecompositionData.recomposedLogDensity
  rw [RelativeStatePair.modularPotential_eq_neg_logDensity (R := R.polarized.plus.data.localPair)
      (a := bplus)]
  rw [RelativeStatePair.modularPotential_eq_neg_logDensity (R := R.polarized.minus.data.localPair)
      (a := bminus)]
  ring

/-- Vanishing coupling is equivalent to exact logarithmic recomposition through the common carrier. -/
@[rep_depth projective] theorem
    PolarizedRecompositionData.vanishingCoupling_iff_exactLogRecomposition
    (R : PolarizedRecompositionData H α βplus βminus) :
    R.vanishingCoupling ↔ R.exactLogRecomposition := by
  constructor
  · intro hcoupling bplus bminus
    rw [PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_add_coupling]
    rw [hcoupling]
    ring
  · intro hexact
    classical
    let bplus0 : βplus := Classical.choice ‹Nonempty βplus›
    let bminus0 : βminus := Classical.choice ‹Nonempty βminus›
    have h0 := hexact bplus0 bminus0
    rw [PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_add_coupling] at h0
    have h1 := congrArg (fun x => x - R.recomposedCommonCarrierLogDensity bplus0 bminus0) h0
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1

/-- Vanishing global coupling forces exact recomposition through the common carrier. -/
@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_of_vanishingCoupling
    (R : PolarizedRecompositionData H α βplus βminus)
    (hcoupling : R.couplingLogDefect = 0) (bplus : βplus) (bminus : βminus) :
    R.recomposedLogDensity bplus bminus = R.recomposedCommonCarrierLogDensity bplus bminus := by
  rw [PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_add_coupling]
  rw [hcoupling]
  ring

/-- Vanishing global coupling forces exact modular-potential recomposition through the common carrier. -/
@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_of_vanishingCoupling
    (R : PolarizedRecompositionData H α βplus βminus)
    (hcoupling : R.couplingLogDefect = 0) (bplus : βplus) (bminus : βminus) :
    R.recomposedModularPotential bplus bminus
      = R.recomposedCommonCarrierModularPotential bplus bminus := by
  rw [PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_add_coupling]
  rw [PolarizedRecompositionData.couplingPotentialDefect_eq_neg_couplingLogDefect]
  rw [hcoupling]
  ring

/-- Vanishing coupling is equivalent to exact modular-potential recomposition through the common carrier. -/
@[rep_depth projective] theorem
    PolarizedRecompositionData.vanishingCoupling_iff_exactPotentialRecomposition
    (R : PolarizedRecompositionData H α βplus βminus) :
    R.vanishingCoupling ↔ R.exactPotentialRecomposition := by
  constructor
  · intro hcoupling bplus bminus
    exact PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_of_vanishingCoupling
      (R := R) (hcoupling := hcoupling) (bplus := bplus) (bminus := bminus)
  · intro hexact
    classical
    let bplus0 : βplus := Classical.choice ‹Nonempty βplus›
    let bminus0 : βminus := Classical.choice ‹Nonempty βminus›
    have h0 := hexact bplus0 bminus0
    rw [PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_add_coupling] at h0
    have h1 := congrArg (fun x => x - R.recomposedCommonCarrierModularPotential bplus0 bminus0) h0
    have hpot : R.couplingPotentialDefect = 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
    rw [PolarizedRecompositionData.couplingPotentialDefect_eq_neg_couplingLogDefect] at hpot
    simpa using hpot

/-- Logarithmic and modular-potential exact recomposition are equivalent. -/
@[rep_depth projective] theorem
    PolarizedRecompositionData.exactLogRecomposition_iff_exactPotentialRecomposition
    (R : PolarizedRecompositionData H α βplus βminus) :
    R.exactLogRecomposition ↔ R.exactPotentialRecomposition := by
  constructor
  · intro hexact
    have hcoupling :
        R.vanishingCoupling := by
      exact (PolarizedRecompositionData.vanishingCoupling_iff_exactLogRecomposition
        (R := R)).mpr hexact
    exact (PolarizedRecompositionData.vanishingCoupling_iff_exactPotentialRecomposition
      (R := R)).mp hcoupling
  · intro hexact
    have hcoupling :
        R.vanishingCoupling := by
      exact (PolarizedRecompositionData.vanishingCoupling_iff_exactPotentialRecomposition
        (R := R)).mpr hexact
    exact (PolarizedRecompositionData.vanishingCoupling_iff_exactLogRecomposition
      (R := R)).mp hcoupling

/--
Stronger sectorwise exactness implies vanishing global coupling. The converse is
not asserted here: global cancellation may hide nontrivial sector defects.
-/
@[rep_depth projective] theorem PolarizedRecompositionData.couplingLogDefect_eq_zero_of_sectorwiseExact
    (R : PolarizedRecompositionData H α βplus βminus)
    (hplus : R.polarized.plus.data.sourceLogShift = R.polarized.plus.data.targetLogShift)
    (hminus : R.polarized.minus.data.sourceLogShift = R.polarized.minus.data.targetLogShift) :
    R.couplingLogDefect = 0 := by
  unfold PolarizedRecompositionData.couplingLogDefect
  unfold PolarizedRecompositionData.plusLogDefect
  unfold PolarizedRecompositionData.minusLogDefect
  rw [hplus, hminus]
  ring

/-- Sectorwise exactness implies vanishing global coupling. -/
@[rep_depth projective] theorem
    PolarizedRecompositionData.vanishingCoupling_of_sectorwiseExact
    (R : PolarizedRecompositionData H α βplus βminus)
    (hexact : R.sectorwiseExact) :
    R.vanishingCoupling := by
  rcases hexact with ⟨hplus, hminus⟩
  exact PolarizedRecompositionData.couplingLogDefect_eq_zero_of_sectorwiseExact
    (R := R) (hplus := hplus) (hminus := hminus)

/-- Sectorwise exactness implies exact logarithmic recomposition through the common carrier. -/
@[rep_depth projective] theorem
    PolarizedRecompositionData.exactLogRecomposition_of_sectorwiseExact
    (R : PolarizedRecompositionData H α βplus βminus)
    (hexact : R.sectorwiseExact) :
    R.exactLogRecomposition := by
  exact (PolarizedRecompositionData.vanishingCoupling_iff_exactLogRecomposition
    (R := R)).mp <|
      PolarizedRecompositionData.vanishingCoupling_of_sectorwiseExact
        (R := R) (hexact := hexact)

/-- Sectorwise exactness implies exact recomposition of logarithmic density through the common carrier. -/
@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_of_sectorwiseExact
    (R : PolarizedRecompositionData H α βplus βminus)
    (hplus : R.polarized.plus.data.sourceLogShift = R.polarized.plus.data.targetLogShift)
    (hminus : R.polarized.minus.data.sourceLogShift = R.polarized.minus.data.targetLogShift)
    (bplus : βplus) (bminus : βminus) :
    R.recomposedLogDensity bplus bminus = R.recomposedCommonCarrierLogDensity bplus bminus := by
  exact PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_of_vanishingCoupling
    (R := R)
    (hcoupling := R.couplingLogDefect_eq_zero_of_sectorwiseExact hplus hminus)
    (bplus := bplus) (bminus := bminus)

/-- Sectorwise exactness implies exact modular-potential recomposition through the common carrier. -/
@[rep_depth projective] theorem
    PolarizedRecompositionData.exactPotentialRecomposition_of_sectorwiseExact
    (R : PolarizedRecompositionData H α βplus βminus)
    (hexact : R.sectorwiseExact) :
    R.exactPotentialRecomposition := by
  exact (PolarizedRecompositionData.vanishingCoupling_iff_exactPotentialRecomposition
    (R := R)).mp <|
      PolarizedRecompositionData.vanishingCoupling_of_sectorwiseExact
        (R := R) (hexact := hexact)

/-- Sectorwise exactness implies exact modular-potential recomposition through the common carrier. -/
@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_of_sectorwiseExact
    (R : PolarizedRecompositionData H α βplus βminus)
    (hplus : R.polarized.plus.data.sourceLogShift = R.polarized.plus.data.targetLogShift)
    (hminus : R.polarized.minus.data.sourceLogShift = R.polarized.minus.data.targetLogShift)
    (bplus : βplus) (bminus : βminus) :
    R.recomposedModularPotential bplus bminus
      = R.recomposedCommonCarrierModularPotential bplus bminus := by
  exact PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_of_vanishingCoupling
    (R := R)
    (hcoupling := R.couplingLogDefect_eq_zero_of_sectorwiseExact hplus hminus)
    (bplus := bplus) (bminus := bminus)

end Recomposition

end InfoGeometry.Canonical.RelativeModularRecomposition
