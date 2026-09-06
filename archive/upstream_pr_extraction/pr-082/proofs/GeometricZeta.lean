import Mathlib

/-!
# Geometric Zeta: Layer-12 Lightcone Geometry of the Graded Index

This file encodes the geometric climax of the arithmetic dictionary.

Core finite claims:

* `Z_fermion_graded` is the graded supertrace `1/ζ(s)` (formal),
  i.e. the reciprocal determinant of a bosonic partition model.
* zeros of the bosonic denominator are singularities of this reciprocal index,
  and are explicitly modeled by `geometricReciprocalSingularity`.
* a split-signature paravector temperature has determinant `σ² - γ²`;
  the parabolic locus is exactly `det = 0`.
* assuming a model-level correspondence, zeros of the index can be sent into the
  parabolic locus: a lightcone interpretation.
-/

noncomputable section

/-- Local reciprocal model for a graded fermionic arithmetical supertrace. -/
def Z_fermion_graded (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  (Z s)⁻¹

/-- Candidate singularity of the graded reciprocal determinant. -/
def geometricReciprocalSingularity (Z : ℂ → ℂ) (s : ℂ) : Prop :=
  Z s = 0

/-- Minimal split-signature paravector coordinate model (Hestenes/Krein spirit). -/
structure SplitParavector where
  scalar : ℝ
  bivector : ℝ
  deriving DecidableEq

/-- Split determinant/paravector norm. -/
def SplitParavector.det (v : SplitParavector) : ℝ :=
  v.scalar ^ 2 - v.bivector ^ 2

/-- Parabolic locus of the split model. -/
def SplitParavector.parabolic (v : SplitParavector) : Prop :=
  v.det = 0

/-- Split paravector temperature from complex inverse-temperature coordinates. -/
def paravector_temperature (σ γ : ℝ) : SplitParavector :=
  { scalar := σ, bivector := γ }

/-- Backward-compatible camel-case alias used elsewhere. -/
def paravectorTemperature (σ γ : ℝ) : SplitParavector :=
  paravector_temperature σ γ

/-- Formal dictionary: a reciprocal index pole iff denominator vanishes. -/
theorem geometricGradedIndexPole_iff_denominator_zero {Z : ℂ → ℂ} {s : ℂ} :
    geometricReciprocalSingularity Z s ↔ Z s = 0 := by
  rfl

/-- `1/ζ(s)` is formally the reciprocal of `ζ(s)`; at a denominator zero this is
    the algebraic singular value for this local reciprocal model. -/
theorem geometricGradedIndex_singularity (Z : ℂ → ℂ) {s : ℂ}
    (hzero : Z s = 0) :
    Z_fermion_graded Z s = 0 := by
  rw [Z_fermion_graded, hzero]
  simp

/-- Determinant of the split paravector temperature is the usual split form. -/
theorem geometric_paravector_det (σ γ : ℝ) :
    (paravector_temperature σ γ).det = σ ^ 2 - γ ^ 2 := by
  rfl

/-- Parabolic criterion in coordinates. -/
theorem geometric_lightcone_iff_det_zero (σ γ : ℝ) :
    (paravector_temperature σ γ).parabolic ↔ σ ^ 2 = γ ^ 2 := by
  simp [SplitParavector.parabolic, SplitParavector.det, paravector_temperature]
  constructor <;> intro h <;> nlinarith

/-- Layer-12 bridge: graded-index poles map into the parabolic locus. -/
def riemann_zeros_to_lightcones_model (Z : ℂ → ℂ) : Prop :=
  ∀ s, Z s = 0 → (paravector_temperature s.re s.im).parabolic

/-- The core Layer-12 assertion, parameterized by an explicit model predicate. -/
theorem riemann_zeros_are_lightcones {Z : ℂ → ℂ}
    (H : riemann_zeros_to_lightcones_model Z) :
    ∀ s, Z s = 0 → (paravector_temperature s.re s.im).parabolic := by
  simpa using H

/-- Consolidated geometric-zeta package: graded reciprocal pole, paravector
    determinant, and coordinate form of the parabolic locus. -/
theorem geometric_zeta_lightcone_synthesis :
    (∀ Z : ℂ → ℂ, ∀ s, geometricReciprocalSingularity Z s ↔ Z s = 0) ∧
    (∀ Z : ℂ → ℂ, ∀ s, geometricReciprocalSingularity Z s →
      Z_fermion_graded Z s = 0) ∧
    (∀ σ γ : ℝ, (paravector_temperature σ γ).det = σ ^ 2 - γ ^ 2) ∧
    (∀ σ γ : ℝ, (paravector_temperature σ γ).parabolic ↔ σ ^ 2 = γ ^ 2) := by
  constructor
  · intro Z s
    change Z s = 0 ↔ Z s = 0
    rfl
  constructor
  · intro Z s hs
    rw [Z_fermion_graded, geometricReciprocalSingularity] at *
    rw [hs]
    simp
  constructor
  · intro σ γ
    rfl
  · intro σ γ
    simp [SplitParavector.parabolic, SplitParavector.det, paravector_temperature]
    constructor <;> intro h <;> nlinarith

end noncomputable section
