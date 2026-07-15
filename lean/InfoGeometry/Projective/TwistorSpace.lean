import InfoGeometry.Twistor.PenroseTwistor

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

abbrev TwistorSpace : Type := PenroseTwistor.TwistorCarrier

instance : AddCommGroup TwistorSpace := inferInstance
instance : Module ℂ TwistorSpace := inferInstance

theorem twistor_space_dim : finrank ℂ TwistorSpace = 4 := by
  simpa [TwistorSpace] using PenroseTwistor.twistor_space_dim

/-- The Penrose twistor Hermitian form. -/
noncomputable def twistorNorm : TwistorSpace →ₗ⋆[ℂ] TwistorSpace →ₗ[ℂ] ℂ :=
  PenroseTwistor.twistorHermitian

theorem twistorNorm_apply (Z W : TwistorSpace) :
    twistorNorm Z W =
      ∑ x : Fin 4, if (x : ℕ) < 2 then (starRingEnd ℂ) (Z x) * W x else -((starRingEnd ℂ) (Z x) * W x) := by
  simpa [twistorNorm] using PenroseTwistor.twistorHermitian_apply Z W

noncomputable def helicity (Z : TwistorSpace) : ℝ :=
  PenroseTwistor.helicity Z

abbrev IsPositiveTwistor (Z : TwistorSpace) : Prop :=
  PenroseTwistor.IsPositiveTwistor Z

abbrev IsNegativeTwistor (Z : TwistorSpace) : Prop :=
  PenroseTwistor.IsNegativeTwistor Z

abbrev IsNullTwistor (Z : TwistorSpace) : Prop :=
  PenroseTwistor.IsNullTwistor Z

theorem twistorNorm_smul_right (c : ℂ) (Z W : TwistorSpace) :
    twistorNorm Z (c • W) = c • twistorNorm Z W := by
  simpa [twistorNorm] using PenroseTwistor.twistorHermitian_smul_right c Z W

theorem twistorNorm_smul_self (c : ℂ) (Z : TwistorSpace) :
    twistorNorm (c • Z) (c • Z) = (Complex.normSq c : ℂ) * twistorNorm Z Z := by
  simpa [twistorNorm] using PenroseTwistor.twistorHermitian_smul_self c Z

theorem twistor_classification_disjoint (Z : TwistorSpace) :
    ¬ (_root_.IsPositiveTwistor Z ∧ _root_.IsNegativeTwistor Z) ∧
    ¬ (_root_.IsPositiveTwistor Z ∧ _root_.IsNullTwistor Z) ∧
    ¬ (_root_.IsNegativeTwistor Z ∧ _root_.IsNullTwistor Z) := by
  simpa [_root_.IsPositiveTwistor, _root_.IsNegativeTwistor, _root_.IsNullTwistor] using
    PenroseTwistor.twistor_classification_disjoint Z

abbrev ProjectiveTwistorSpace : Type _ :=
  PenroseTwistor.ProjectiveTwistorSpace

abbrev NullTwistorSpace : Type _ :=
  PenroseTwistor.NullTwistorSpace

abbrev RealNullTwistorSpace : Type _ :=
  PenroseTwistor.RealNullTwistorSpace

theorem projective_twistor_classification_disjoint (p : _root_.ProjectiveTwistorSpace) :
    ¬ (PenroseTwistor.IsProjectivePositive p ∧ PenroseTwistor.IsProjectiveNegative p) ∧
    ¬ (PenroseTwistor.IsProjectivePositive p ∧ PenroseTwistor.IsProjectiveNull p) ∧
    ¬ (PenroseTwistor.IsProjectiveNegative p ∧ PenroseTwistor.IsProjectiveNull p) := by
  simpa using PenroseTwistor.projective_twistor_classification_disjoint p

theorem projective_twistor_sign_trichotomy (p : _root_.ProjectiveTwistorSpace) :
    PenroseTwistor.IsProjectivePositive p ∨
      PenroseTwistor.IsProjectiveNegative p ∨
      PenroseTwistor.IsProjectiveNull p := by
  simpa using PenroseTwistor.projective_twistor_sign_trichotomy p

def twistorMk (Z : TwistorSpace) (hZ : Z ≠ 0) (hnull : helicity Z = 0) :
    _root_.NullTwistorSpace :=
  PenroseTwistor.twistorMk Z hZ hnull

noncomputable abbrev twistorRealQuadraticForm : QuadraticForm ℝ TwistorSpace :=
  PenroseTwistor.twistorRealQuadraticForm

noncomputable def realNullTwistorMk (Z : TwistorSpace) (hZ : Z ≠ 0)
    (hnull : _root_.twistorRealQuadraticForm Z = 0) :
    _root_.RealNullTwistorSpace :=
  PenroseTwistor.realNullTwistorMk Z hZ hnull

@[simp] theorem isProjectiveNull_mk_iff (Z : TwistorSpace) (hZ : Z ≠ 0) :
    PenroseTwistor.IsProjectiveNull
      (Projectivization.mk ℂ Z hZ) ↔ PenroseTwistor.helicity Z = 0 := by
  simpa using PenroseTwistor.isProjectiveNull_mk_iff Z hZ

@[simp] theorem twistorMk_rep (Z : TwistorSpace) (hZ : Z ≠ 0) (hnull : helicity Z = 0) :
    (_root_.twistorMk Z hZ hnull).1 = Projectivization.mk ℂ Z hZ := by
  simpa [twistorMk] using PenroseTwistor.twistorMk_rep Z hZ hnull

@[simp] theorem realNullTwistorMk_rep (Z : TwistorSpace) (hZ : Z ≠ 0)
    (hnull : _root_.twistorRealQuadraticForm Z = 0) :
    (_root_.realNullTwistorMk Z hZ hnull).1 = Projectivization.mk ℝ Z hZ := by
  simpa [realNullTwistorMk, twistorRealQuadraticForm] using
    PenroseTwistor.realNullTwistorMk_rep Z hZ hnull
