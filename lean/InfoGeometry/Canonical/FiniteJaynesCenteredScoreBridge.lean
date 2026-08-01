import InfoGeometry.Canonical.JaynesLDDSCentering

/-!
# InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge

Finite Jaynes centered-score bridge.

This module isolates the finite statistical skeleton that can later be connected
to AF/direct-limit compatibility:

* a finite reference weight family;
* an observation family on the same finite index set;
* centered score `obsᵢ - refᵢ`;
* zero total centered score under equal total mass;
* relative-density centering `obsᵢ / refᵢ - 1`, with the nonzero reference
  hypothesis explicit.

No entropy theorem.
No LDDS/measure limit.
No state uniqueness theorem.
No spectral, Tomita, or conformal-completion claim.
-/

namespace InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge

open Finset
open JaynesLDDSCentering

/-- A finite profile over an arbitrary finite index type. -/
abbrev FiniteProfile (ι : Type*) :=
  ι → ℝ

/-- A finite reference weight family.  Positivity/normalization remain explicit hypotheses. -/
abbrev FiniteReferenceState (ι : Type*) := FiniteProfile ι

namespace FiniteReferenceState

/-- Compatibility projection for the former named reference weight field. -/
abbrev weight {ι : Type*} (R : FiniteReferenceState ι) : ι → ℝ := R

end FiniteReferenceState

/-- A finite Jaynes pair: observation data with equal total mass to the reference. -/
structure FiniteJaynesPair (ι : Type*) [Fintype ι] where
  /-- Reference/background finite LDDS weights. -/
  reference : FiniteReferenceState ι
  /-- Observed finite density/profile on the same atoms. -/
  observation : FiniteProfile ι
  /-- Jaynes-compatible finite normalization: observed and reference masses agree. -/
  equal_mass : ∑ i : ι, observation i = ∑ i : ι, reference i

namespace FiniteReferenceStateOps

variable {ι : Type*} [Fintype ι]

/-- Positivity predicate for a finite reference state. -/
def IsPositive (R : FiniteReferenceState ι) : Prop :=
  ∀ i : ι, 0 < R i

/-- Normalization predicate for a finite reference state. -/
def IsNormalized (R : FiniteReferenceState ι) : Prop :=
  ∑ i : ι, R i = 1

/-- Total mass of an observation family. -/
def observationMass (_R : FiniteReferenceState ι) (obs : ι → ℝ) : ℝ :=
  ∑ i : ι, obs i

/-- Total reference mass. -/
def referenceMass (R : FiniteReferenceState ι) : ℝ :=
  ∑ i : ι, R i

/-- Additive centered score: subtract the reference background. -/
def centeredScore (R : FiniteReferenceState ι) (obs : ι → ℝ) (i : ι) : ℝ :=
  obs i - R i

/-- Relative density against the finite reference. -/
noncomputable def densityRatio (R : FiniteReferenceState ι) (obs : ι → ℝ) (i : ι) : ℝ :=
  obs i / R i

/-- Multiplicative centered score `obsᵢ / refᵢ - 1`. -/
noncomputable def relativeCenteredScore
    (R : FiniteReferenceState ι) (obs : ι → ℝ) (i : ι) : ℝ :=
  densityRatio R obs i - 1

omit [Fintype ι] in
/-- The reference observation has zero additive centered score. -/
@[simp]
theorem centeredScore_ref_zero (R : FiniteReferenceState ι) :
    FiniteReferenceStateOps.centeredScore R R = 0 := by
  funext i
  simp [FiniteReferenceStateOps.centeredScore]

omit [Fintype ι] in
/-- Pointwise readback for additive centering. -/
theorem centeredScore_eq_sub (R : FiniteReferenceState ι) (obs : ι → ℝ) (i : ι) :
    FiniteReferenceStateOps.centeredScore R obs i = obs i - R i :=
  rfl

/-- The total additive centered score is the mass difference. -/
theorem sum_centeredScore_eq_mass_sub
    (R : FiniteReferenceState ι) (obs : ι → ℝ) :
    (∑ i : ι, FiniteReferenceStateOps.centeredScore R obs i) =
      FiniteReferenceStateOps.observationMass R obs -
        FiniteReferenceStateOps.referenceMass R := by
  unfold FiniteReferenceStateOps.centeredScore
  unfold FiniteReferenceStateOps.observationMass FiniteReferenceStateOps.referenceMass
  rw [Finset.sum_sub_distrib]

/-- Equal total mass gives zero total additive centered score. -/
theorem sum_centeredScore_eq_zero_of_equal_mass
    (R : FiniteReferenceState ι) (obs : ι → ℝ)
    (hmass :
      FiniteReferenceStateOps.observationMass R obs =
        FiniteReferenceStateOps.referenceMass R) :
    (∑ i : ι, FiniteReferenceStateOps.centeredScore R obs i) = 0 := by
  rw [FiniteReferenceStateOps.sum_centeredScore_eq_mass_sub R obs, hmass]
  ring

/-- A normalized reference has reference mass one. -/
theorem referenceMass_eq_one_of_normalized
    (R : FiniteReferenceState ι) (hR : IsNormalized R) :
    FiniteReferenceStateOps.referenceMass R = 1 :=
  by simpa [FiniteReferenceStateOps.referenceMass] using hR

omit [Fintype ι] in
/-- Positivity implies every reference weight is nonzero. -/
theorem weight_ne_zero_of_positive
    (R : FiniteReferenceState ι) (hR : IsPositive R) (i : ι) :
    R i ≠ 0 :=
  ne_of_gt (hR i)

omit [Fintype ι] in
/-- Relative centering clears denominators to the additive centered score. -/
theorem weight_mul_relativeCenteredScore_eq_centeredScore
    (R : FiniteReferenceState ι) (obs : ι → ℝ) {i : ι}
    (href : R i ≠ 0) :
    R i * FiniteReferenceStateOps.relativeCenteredScore R obs i =
      FiniteReferenceStateOps.centeredScore R obs i := by
  unfold FiniteReferenceStateOps.relativeCenteredScore
  unfold FiniteReferenceStateOps.densityRatio FiniteReferenceStateOps.centeredScore
  field_simp [href]

omit [Fintype ι] in
/-- Relative centering equals additive centering divided by the reference weight. -/
theorem relativeCenteredScore_eq_centeredScore_div
    (R : FiniteReferenceState ι) (obs : ι → ℝ) {i : ι}
    (href : R i ≠ 0) :
    FiniteReferenceStateOps.relativeCenteredScore R obs i =
      FiniteReferenceStateOps.centeredScore R obs i / R i := by
  unfold FiniteReferenceStateOps.relativeCenteredScore
  unfold FiniteReferenceStateOps.densityRatio FiniteReferenceStateOps.centeredScore
  field_simp [href]

omit [Fintype ι] in
/-- Positive references permit the denominator-cleared centered-score readback. -/
theorem weight_mul_relativeCenteredScore_eq_centeredScore_of_positive
    (R : FiniteReferenceState ι) (hR : IsPositive R) (obs : ι → ℝ) (i : ι) :
    R i * FiniteReferenceStateOps.relativeCenteredScore R obs i =
      FiniteReferenceStateOps.centeredScore R obs i :=
  FiniteReferenceStateOps.weight_mul_relativeCenteredScore_eq_centeredScore
    R obs (FiniteReferenceStateOps.weight_ne_zero_of_positive R hR i)

/-- Convert this finite bridge datum to the LDDS-centering datum from `JaynesLDDSCentering`. -/
def toFiniteLDDSDatum (R : FiniteReferenceState ι) (obs : ι → ℝ) : FiniteLDDSDatum ι :=
  (obs, R)

omit [Fintype ι] in
/-- The LDDS centered score agrees with the relative centered score here. -/
theorem ldds_centeredScore_eq_relativeCenteredScore
    (R : FiniteReferenceState ι) (obs : ι → ℝ) (i : ι) :
    (toFiniteLDDSDatum R obs).centeredScore i =
      FiniteReferenceStateOps.relativeCenteredScore R obs i :=
  rfl

omit [Fintype ι] in
/-- The LDDS weighted centered score agrees with the reference-weighted relative score. -/
theorem ldds_weightedCenteredScore_eq
    (R : FiniteReferenceState ι) (obs : ι → ℝ) (i : ι) :
    (toFiniteLDDSDatum R obs).weightedCenteredScore i =
      R i * FiniteReferenceStateOps.relativeCenteredScore R obs i :=
  rfl

end FiniteReferenceStateOps

section PublicCenteredSurface

variable {ι : Type*} [Fintype ι]

/-- Public alias for the finite Jaynes relative density `obsᵢ / refᵢ`. -/
noncomputable def relativeDensity
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι) (i : ι) : ℝ :=
  FiniteReferenceStateOps.densityRatio R obs i

/-- Public alias for the centered relative density `obsᵢ / refᵢ - 1`. -/
noncomputable def centeredRelativeDensity
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι) (i : ι) : ℝ :=
  FiniteReferenceStateOps.relativeCenteredScore R obs i

omit [Fintype ι] in
/-- The reference profile has zero centered relative density where the reference is nonzero. -/
@[simp]
theorem centeredRelativeDensity_self
    (R : FiniteReferenceState ι) (href : ∀ i : ι, R i ≠ 0) :
    centeredRelativeDensity R R = 0 := by
  funext i
  change R i / R i - 1 = 0
  rw [div_self (href i)]
  ring

omit [Fintype ι] in
/-- Relative density is one plus the centered relative density. -/
theorem relativeDensity_eq_one_add_centered
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι) :
    relativeDensity R obs = fun i => 1 + centeredRelativeDensity R obs i := by
  funext i
  unfold relativeDensity centeredRelativeDensity FiniteReferenceStateOps.relativeCenteredScore
  ring

/--
The reference-weighted centered relative density is the observed mass minus the
reference mass, assuming all reference denominators are nonzero.
-/
theorem ref_weighted_centeredRelativeDensity_eq_mass_sub
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι)
    (href : ∀ i : ι, R i ≠ 0) :
    (∑ i : ι, R i * centeredRelativeDensity R obs i) =
      FiniteReferenceStateOps.observationMass R obs -
        FiniteReferenceStateOps.referenceMass R := by
  calc
    (∑ i : ι, R i * centeredRelativeDensity R obs i) =
        ∑ i : ι, FiniteReferenceStateOps.centeredScore R obs i := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      unfold centeredRelativeDensity
      exact FiniteReferenceStateOps.weight_mul_relativeCenteredScore_eq_centeredScore
        R obs (href i)
    _ = FiniteReferenceStateOps.observationMass R obs -
        FiniteReferenceStateOps.referenceMass R := by
      exact FiniteReferenceStateOps.sum_centeredScore_eq_mass_sub R obs

/-- Equal finite mass gives zero reference-weighted centered relative density. -/
theorem ref_weighted_centeredRelativeDensity_eq_zero_of_equal_mass
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι)
    (href : ∀ i : ι, R i ≠ 0)
    (hmass : FiniteReferenceStateOps.observationMass R obs =
      FiniteReferenceStateOps.referenceMass R) :
    (∑ i : ι, R i * centeredRelativeDensity R obs i) = 0 := by
  rw [ref_weighted_centeredRelativeDensity_eq_mass_sub R obs href, hmass]
  ring

/-- A normalized finite Jaynes pair has zero reference-weighted centered score. -/
theorem FiniteJaynesPair.ref_weighted_centeredRelativeDensity_eq_zero
    (P : FiniteJaynesPair ι) (href : ∀ i : ι, P.reference i ≠ 0) :
    (∑ i : ι, P.reference i *
      centeredRelativeDensity P.reference P.observation i) = 0 := by
  exact ref_weighted_centeredRelativeDensity_eq_zero_of_equal_mass
    P.reference P.observation href P.equal_mass

end PublicCenteredSurface

end InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge
