import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Projective Twistor Space

Compatibility layer exposing the Penrose twistor model under the
`InfoGeometry.Projective` namespace.

Repository policy boundary:
* This file does not identify twistor space definitionally with split octonions.
* The target direction is theorem-level: appropriate quantized twistor algebra
  carries split-octonion / `G2*` structure under explicit hypotheses.

The actual Hermitian-form proof and projective-null cone are owned by
`InfoGeometry.Twistor.PenroseTwistor`; this file re-exports the projective
names and keeps the older module path alive.
-/

open scoped Classical
open scoped LinearAlgebra.Projectivization
open Module

abbrev TwistorSpace : Type := InfoGeometry.Twistor.PenroseTwistor.TwistorCarrier

instance : AddCommGroup TwistorSpace := inferInstance
instance : Module ℂ TwistorSpace := inferInstance

theorem twistor_space_dim : finrank ℂ TwistorSpace = 4 := by
  simpa [TwistorSpace] using InfoGeometry.Twistor.PenroseTwistor.twistor_space_dim

/-- The Penrose twistor Hermitian form. -/
noncomputable def twistorNorm : TwistorSpace →ₗ⋆[ℂ] TwistorSpace →ₗ[ℂ] ℂ :=
  InfoGeometry.Twistor.PenroseTwistor.twistorHermitian

theorem twistorNorm_apply (Z W : TwistorSpace) :
    twistorNorm Z W =
      ∑ x : Fin 4, if (x : ℕ) < 2 then (starRingEnd ℂ) (Z x) * W x else -((starRingEnd ℂ) (Z x) * W x) := by
  simpa [twistorNorm] using InfoGeometry.Twistor.PenroseTwistor.twistorHermitian_apply Z W

noncomputable def helicity (Z : TwistorSpace) : ℝ :=
  InfoGeometry.Twistor.PenroseTwistor.helicity Z

theorem twistorNorm_smul_right (c : ℂ) (Z W : TwistorSpace) :
    twistorNorm Z (c • W) = c • twistorNorm Z W := by
  simpa [twistorNorm] using InfoGeometry.Twistor.PenroseTwistor.twistorHermitian_smul_right c Z W

theorem twistorNorm_smul_self (c : ℂ) (Z : TwistorSpace) :
    twistorNorm (c • Z) (c • Z) = (Complex.normSq c : ℂ) * twistorNorm Z Z := by
  simpa [twistorNorm] using InfoGeometry.Twistor.PenroseTwistor.twistorHermitian_smul_self c Z

theorem twistor_classification_disjoint (Z : TwistorSpace) :
    ¬ (InfoGeometry.Twistor.PenroseTwistor.IsPositiveTwistor Z ∧
      InfoGeometry.Twistor.PenroseTwistor.IsNegativeTwistor Z) ∧
    ¬ (InfoGeometry.Twistor.PenroseTwistor.IsPositiveTwistor Z ∧
      InfoGeometry.Twistor.PenroseTwistor.IsNullTwistor Z) ∧
    ¬ (InfoGeometry.Twistor.PenroseTwistor.IsNegativeTwistor Z ∧
      InfoGeometry.Twistor.PenroseTwistor.IsNullTwistor Z) := by
  simpa using
    InfoGeometry.Twistor.PenroseTwistor.twistor_classification_disjoint Z

abbrev ProjectiveTwistorSpace : Type _ :=
  InfoGeometry.Twistor.PenroseTwistor.ProjectiveTwistorSpace

abbrev NullTwistorSpace : Type _ :=
  InfoGeometry.Twistor.PenroseTwistor.NullTwistorSpace

abbrev RealNullTwistorSpace : Type _ :=
  InfoGeometry.Twistor.PenroseTwistor.RealNullTwistorSpace

theorem projective_twistor_classification_disjoint (p : _root_.ProjectiveTwistorSpace) :
    ¬ (InfoGeometry.Twistor.PenroseTwistor.IsProjectivePositive p ∧ InfoGeometry.Twistor.PenroseTwistor.IsProjectiveNegative p) ∧
    ¬ (InfoGeometry.Twistor.PenroseTwistor.IsProjectivePositive p ∧ InfoGeometry.Twistor.PenroseTwistor.IsProjectiveNull p) ∧
    ¬ (InfoGeometry.Twistor.PenroseTwistor.IsProjectiveNegative p ∧ InfoGeometry.Twistor.PenroseTwistor.IsProjectiveNull p) := by
  simpa using InfoGeometry.Twistor.PenroseTwistor.projective_twistor_classification_disjoint p

theorem projective_twistor_sign_trichotomy (p : _root_.ProjectiveTwistorSpace) :
    InfoGeometry.Twistor.PenroseTwistor.IsProjectivePositive p ∨
      InfoGeometry.Twistor.PenroseTwistor.IsProjectiveNegative p ∨
      InfoGeometry.Twistor.PenroseTwistor.IsProjectiveNull p := by
  simpa using InfoGeometry.Twistor.PenroseTwistor.projective_twistor_sign_trichotomy p

def twistorMk (Z : TwistorSpace) (hZ : Z ≠ 0) (hnull : helicity Z = 0) :
    _root_.NullTwistorSpace :=
  InfoGeometry.Twistor.PenroseTwistor.twistorMk Z hZ hnull

noncomputable abbrev twistorRealQuadraticForm : QuadraticForm ℝ TwistorSpace :=
  InfoGeometry.Twistor.PenroseTwistor.twistorRealQuadraticForm

noncomputable def realNullTwistorMk (Z : TwistorSpace) (hZ : Z ≠ 0)
    (hnull : _root_.twistorRealQuadraticForm Z = 0) :
    _root_.RealNullTwistorSpace :=
  InfoGeometry.Twistor.PenroseTwistor.realNullTwistorMk Z hZ hnull

@[simp] theorem isProjectiveNull_mk_iff (Z : TwistorSpace) (hZ : Z ≠ 0) :
    InfoGeometry.Twistor.PenroseTwistor.IsProjectiveNull
      (Projectivization.mk ℂ Z hZ) ↔ InfoGeometry.Twistor.PenroseTwistor.helicity Z = 0 := by
  simpa using InfoGeometry.Twistor.PenroseTwistor.isProjectiveNull_mk_iff Z hZ

@[simp] theorem twistorMk_rep (Z : TwistorSpace) (hZ : Z ≠ 0) (hnull : helicity Z = 0) :
    (_root_.twistorMk Z hZ hnull).1 = Projectivization.mk ℂ Z hZ := by
  simpa [twistorMk] using InfoGeometry.Twistor.PenroseTwistor.twistorMk_rep Z hZ hnull

@[simp] theorem realNullTwistorMk_rep (Z : TwistorSpace) (hZ : Z ≠ 0)
    (hnull : _root_.twistorRealQuadraticForm Z = 0) :
    (_root_.realNullTwistorMk Z hZ hnull).1 = Projectivization.mk ℝ Z hZ := by
  simpa [realNullTwistorMk, twistorRealQuadraticForm] using
    InfoGeometry.Twistor.PenroseTwistor.realNullTwistorMk_rep Z hZ hnull
