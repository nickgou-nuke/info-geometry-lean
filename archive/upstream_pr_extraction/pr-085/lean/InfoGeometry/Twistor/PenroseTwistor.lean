import Mathlib.Algebra.Module.LinearMap.Star
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic
import InfoGeometry.Twistor.NullProjective

/-!
# Penrose twistor space

This module gives a concrete complex twistor carrier `ℂ^4`, a signature `(2,2)`
Hermitian form on that carrier, and the induced projective null-cone boundary.

The repository already owns a separate quadratic-form-based null-projective
abstraction.  This file keeps the Penrose presentation explicit and honest:

* the carrier is `Fin 4 → ℂ`;
* the Hermitian form is diagonal with signature `(2,2)`;
* positive, negative, and null twistors are defined at the vector level;
* the projective null boundary is obtained by quotienting nonzero null rays.

This does not claim a full projective-sign decomposition theorem on rays yet.
That would require a separate scale-invariance lift for the sign predicates.
-/

open scoped Classical
open scoped LinearAlgebra.Projectivization
open Module

namespace InfoGeometry.Twistor.PenroseTwistor

/-- The underlying complex 4-space of twistors. -/
abbrev TwistorCarrier : Type := Fin 4 → ℂ

instance : AddCommGroup TwistorCarrier := inferInstance
instance : Module ℂ TwistorCarrier := inferInstance

theorem twistor_space_dim : finrank ℂ TwistorCarrier = 4 := by
  simpa [TwistorCarrier] using (Module.finrank_pi (R := ℂ) (ι := Fin 4))

/-- Diagonal matrix with signature `(2,2)` used by the Penrose form. -/
def twistorMetricMatrix : Matrix (Fin 4) (Fin 4) ℂ := fun i j =>
  if i = j then if i.val < 2 then 1 else -1 else 0

/--
The Penrose Hermitian form on `ℂ^4`.

The first two coordinates contribute positively and the last two contribute
negatively, giving the standard signature `(2,2)` diagonal model.
-/
noncomputable def twistorHermitian : TwistorCarrier →ₗ⋆[ℂ] TwistorCarrier →ₗ[ℂ] ℂ :=
  Matrix.toLinearMapₛₗ₂' ℂ (starRingEnd ℂ) (RingHom.id ℂ) twistorMetricMatrix

@[simp] theorem twistorHermitian_apply (z w : TwistorCarrier) :
    twistorHermitian z w =
      ∑ x : Fin 4, if (x : ℕ) < 2 then (starRingEnd ℂ) (z x) * w x else -((starRingEnd ℂ) (z x) * w x) :=
  by
    simpa [twistorHermitian, twistorMetricMatrix] using
      (Matrix.toLinearMapₛₗ₂'_apply (R := ℂ) (σ₁ := starRingEnd ℂ) (σ₂ := RingHom.id ℂ)
        twistorMetricMatrix z w)

theorem twistorHermitian_smul_right (c : ℂ) (z w : TwistorCarrier) :
    twistorHermitian z (c • w) = c • twistorHermitian z w := by
  simpa using (twistorHermitian z).map_smul c w

theorem twistorHermitian_smul_self (c : ℂ) (z : TwistorCarrier) :
    twistorHermitian (c • z) (c • z) = (Complex.normSq c : ℂ) * twistorHermitian z z := by
  calc
    twistorHermitian (c • z) (c • z) = star c * twistorHermitian z (c • z) := by
      simpa using (twistorHermitian.map_smulₛₗ₂ c z (c • z))
    _ = (Complex.normSq c : ℂ) * twistorHermitian z z := by
      rw [twistorHermitian_smul_right]
      simp [Complex.normSq_eq_conj_mul_self, mul_assoc, mul_left_comm, mul_comm]

/-- The helicity readout is the real part of the Hermitian self-pairing. -/
noncomputable def helicity (z : TwistorCarrier) : ℝ :=
  Complex.re (twistorHermitian z z)

/--
A real bilinear readout obtained by taking the real part of the Hermitian form.

This is the canonical real quadratic substrate underlying the Penrose null
boundary: the hermitian `(2,2)` form is still the geometric source, but the
null-projective quotient in `InfoGeometry.Twistor.NullProjective` expects a
real quadratic form.
-/
noncomputable def twistorRealBilinear : LinearMap.BilinMap ℝ TwistorCarrier ℝ := by
  refine LinearMap.mk₂ ℝ (fun z w => Complex.re (twistorHermitian z w)) ?_ ?_ ?_ ?_
  · intro z₁ z₂ w
    simp [twistorHermitian, Complex.add_re]
  · intro c z w
    have h := congrArg (fun f : TwistorCarrier →ₗ[ℂ] ℂ => f w)
      (twistorHermitian.map_smulₛₗ (c := (c : ℂ)) z)
    simpa using congrArg Complex.re h
  · intro z w₁ w₂
    simp [twistorHermitian, Complex.add_re]
  · intro c z w
    have h := (twistorHermitian z).map_smul c w
    simpa using congrArg Complex.re h

@[simp] theorem twistorRealBilinear_apply (z w : TwistorCarrier) :
    twistorRealBilinear z w = Complex.re (twistorHermitian z w) :=
  rfl

/-- The real quadratic form obtained from the Penrose Hermitian pairing. -/
noncomputable def twistorRealQuadraticForm : QuadraticForm ℝ TwistorCarrier :=
  twistorRealBilinear.toQuadraticMap

@[simp] theorem twistorRealQuadraticForm_apply (z : TwistorCarrier) :
    twistorRealQuadraticForm z = helicity z := by
  simp [twistorRealQuadraticForm, helicity]

/-- Helicity scales by the squared norm of a complex scalar. -/
theorem helicity_smul (c : ℂ) (z : TwistorCarrier) :
    helicity (c • z) = Complex.normSq c * helicity z := by
  rw [helicity, twistorHermitian_smul_self]
  simp [helicity, Complex.re_ofReal_mul]

/-- Positive-helicity twistors. -/
def IsPositiveTwistor (z : TwistorCarrier) : Prop :=
  z ≠ 0 ∧ 0 < helicity z

/-- Negative-helicity twistors. -/
def IsNegativeTwistor (z : TwistorCarrier) : Prop :=
  z ≠ 0 ∧ helicity z < 0

/-- Null twistors. -/
def IsNullTwistor (z : TwistorCarrier) : Prop :=
  z ≠ 0 ∧ helicity z = 0

theorem twistor_classification_disjoint (z : TwistorCarrier) :
    ¬ (IsPositiveTwistor z ∧ IsNegativeTwistor z) ∧
    ¬ (IsPositiveTwistor z ∧ IsNullTwistor z) ∧
    ¬ (IsNegativeTwistor z ∧ IsNullTwistor z) := by
  constructor
  · intro h
    linarith [h.1.2, h.2.2]
  · constructor
    · intro h
      linarith [h.1.2, h.2.2]
    · intro h
      linarith [h.1.2, h.2.2]
/-- Projective complex twistor space. -/
abbrev ProjectiveTwistorSpace : Type _ := ℙ ℂ TwistorCarrier

/-- A projective point is positive if any nonzero representative has positive helicity. -/
def IsProjectivePositive (p : ProjectiveTwistorSpace) : Prop :=
  Projectivization.lift
    (f := fun v : { v : TwistorCarrier // v ≠ 0 } => 0 < helicity v)
    (hf := by
      intro a b t ht
      apply propext
      constructor
      · intro ha
        have ht0 : t ≠ 0 := by
          intro htz
          have hzero : (a : TwistorCarrier) = 0 := by
            simpa [htz] using ht
          exact a.2 hzero
        have hpos : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht0
        have hscaled : 0 < helicity ((t : ℂ) • (b : TwistorCarrier)) := by
          simpa [ht] using ha
        have hscaled' : 0 < Complex.normSq t * helicity (b : TwistorCarrier) := by
          rw [helicity_smul] at hscaled
          exact hscaled
        exact (mul_pos_iff_of_pos_left hpos).mp hscaled'
      · intro hb
        have ht0 : t ≠ 0 := by
          intro htz
          have hzero : (a : TwistorCarrier) = 0 := by
            simpa [htz] using ht
          exact a.2 hzero
        have hpos : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht0
        have hscaled : 0 < helicity ((t : ℂ) • (b : TwistorCarrier)) := by
          rw [helicity_smul]
          exact mul_pos hpos hb
        simpa [ht] using hscaled
    ) p

/-- A projective point is negative if any nonzero representative has negative helicity. -/
def IsProjectiveNegative (p : ProjectiveTwistorSpace) : Prop :=
  Projectivization.lift
    (f := fun v : { v : TwistorCarrier // v ≠ 0 } => helicity v < 0)
    (hf := by
      intro a b t ht
      apply propext
      constructor
      · intro ha
        have ht0 : t ≠ 0 := by
          intro htz
          have hzero : (a : TwistorCarrier) = 0 := by
            simpa [htz] using ht
          exact a.2 hzero
        have hpos : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht0
        have hscaled : helicity ((t : ℂ) • (b : TwistorCarrier)) < 0 := by
          simpa [ht] using ha
        have hscaled' : Complex.normSq t * helicity (b : TwistorCarrier) < 0 := by
          rw [helicity_smul] at hscaled
          exact hscaled
        exact (pos_iff_neg_of_mul_neg (a := Complex.normSq t) (b := helicity (b : TwistorCarrier)) hscaled').mp hpos
      · intro hb
        have ht0 : t ≠ 0 := by
          intro htz
          have hzero : (a : TwistorCarrier) = 0 := by
            simpa [htz] using ht
          exact a.2 hzero
        have hpos : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht0
        have hscaled : helicity ((t : ℂ) • (b : TwistorCarrier)) < 0 := by
          rw [helicity_smul]
          exact mul_neg_of_pos_of_neg hpos hb
        simpa [ht] using hscaled
    ) p

/-- A projective point is null if any nonzero representative has zero helicity. -/
def IsProjectiveNull (p : ProjectiveTwistorSpace) : Prop :=
  Projectivization.lift
    (f := fun v : { v : TwistorCarrier // v ≠ 0 } => helicity v = 0)
    (hf := by
      intro a b t ht
      apply propext
      constructor
      · intro ha
        have ht0 : t ≠ 0 := by
          intro htz
          have hzero : (a : TwistorCarrier) = 0 := by
            simpa [htz] using ht
          exact a.2 hzero
        have hscaled : helicity ((t : ℂ) • (b : TwistorCarrier)) = 0 := by
          simpa [ht] using ha
        have hmul : Complex.normSq t * helicity (b : TwistorCarrier) = 0 := by
          rw [helicity_smul] at hscaled
          exact hscaled
        have hpos : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht0
        have hne : Complex.normSq t ≠ 0 := ne_of_gt hpos
        exact (mul_eq_zero.mp hmul).resolve_left hne
      · intro hb
        have hscaled : helicity ((t : ℂ) • (b : TwistorCarrier)) = 0 := by
          rw [helicity_smul]
          simp [hb]
        simpa [ht] using hscaled
    ) p

/-- The projective null twistor space. -/
abbrev NullTwistorSpace : Type _ := { p : ProjectiveTwistorSpace // IsProjectiveNull p }

/-- The projective null cone of the underlying real quadratic Penrose form. -/
abbrev RealNullTwistorSpace : Type _ :=
  InfoGeometry.Twistor.TwistorSpace twistorRealQuadraticForm

/-- A nonzero null vector defines a projective null twistor. -/
def twistorMk (z : TwistorCarrier) (hz : z ≠ 0) (hnull : helicity z = 0) :
    NullTwistorSpace :=
  ⟨Projectivization.mk ℂ z hz, by
    simpa [IsProjectiveNull] using hnull⟩

/-- A nonzero vector null for the real quadratic Penrose form defines a projective null twistor. -/
noncomputable def realNullTwistorMk (z : TwistorCarrier) (hz : z ≠ 0)
    (hnull : twistorRealQuadraticForm z = 0) :
    RealNullTwistorSpace :=
  InfoGeometry.Twistor.twistorMk twistorRealQuadraticForm z hz <| by
    simpa [twistorRealQuadraticForm] using hnull

@[simp] theorem isProjectiveNull_mk_iff (z : TwistorCarrier) (hz : z ≠ 0) :
    IsProjectiveNull (Projectivization.mk ℂ z hz) ↔ helicity z = 0 := by
  simp [IsProjectiveNull]

@[simp] theorem twistorMk_rep (z : TwistorCarrier) (hz : z ≠ 0)
    (hnull : helicity z = 0) :
    (twistorMk z hz hnull).1 = Projectivization.mk ℂ z hz :=
  rfl

@[simp] theorem realNullTwistorMk_rep (z : TwistorCarrier) (hz : z ≠ 0)
    (hnull : twistorRealQuadraticForm z = 0) :
    (realNullTwistorMk z hz hnull).1 = Projectivization.mk ℝ z hz :=
  rfl

@[simp] theorem isProjectivePositive_mk_iff (z : TwistorCarrier) (hz : z ≠ 0) :
    IsProjectivePositive (Projectivization.mk ℂ z hz) ↔ 0 < helicity z := by
  simp [IsProjectivePositive]

@[simp] theorem isProjectiveNegative_mk_iff (z : TwistorCarrier) (hz : z ≠ 0) :
    IsProjectiveNegative (Projectivization.mk ℂ z hz) ↔ helicity z < 0 := by
  simp [IsProjectiveNegative]

/-- On a canonical projective representative, the positive, negative, and null conditions are pairwise disjoint. -/
theorem projective_twistor_classification_disjoint_mk (z : TwistorCarrier) (hz : z ≠ 0) :
    ¬ (IsProjectivePositive (Projectivization.mk ℂ z hz) ∧
      IsProjectiveNegative (Projectivization.mk ℂ z hz)) ∧
    ¬ (IsProjectivePositive (Projectivization.mk ℂ z hz) ∧
      IsProjectiveNull (Projectivization.mk ℂ z hz)) ∧
    ¬ (IsProjectiveNegative (Projectivization.mk ℂ z hz) ∧
      IsProjectiveNull (Projectivization.mk ℂ z hz)) := by
  constructor
  · intro h
    have hpos : 0 < helicity z := by
      simpa using h.1
    have hneg : helicity z < 0 := by
      simpa using h.2
    linarith
  · constructor
    · intro h
      have hpos : 0 < helicity z := by
        simpa using h.1
      have hzero : helicity z = 0 := by
        simpa using h.2
      linarith
    · intro h
      have hneg : helicity z < 0 := by
        simpa using h.1
      have hzero : helicity z = 0 := by
        simpa using h.2
      linarith

/-- The projective positive, negative, and null regions are pairwise disjoint. -/
theorem projective_twistor_classification_disjoint (p : ProjectiveTwistorSpace) :
    ¬ (IsProjectivePositive p ∧ IsProjectiveNegative p) ∧
    ¬ (IsProjectivePositive p ∧ IsProjectiveNull p) ∧
    ¬ (IsProjectiveNegative p ∧ IsProjectiveNull p) := by
  refine Quotient.inductionOn p ?_
  intro z
  change ¬ (0 < helicity z.1 ∧ helicity z.1 < 0) ∧
    ¬ (0 < helicity z.1 ∧ helicity z.1 = 0) ∧
    ¬ (helicity z.1 < 0 ∧ helicity z.1 = 0)
  exact projective_twistor_classification_disjoint_mk z.1 z.2

/-- Every projective twistor is positive, negative, or null. -/
theorem projective_twistor_sign_trichotomy (p : ProjectiveTwistorSpace) :
    IsProjectivePositive p ∨ IsProjectiveNegative p ∨ IsProjectiveNull p := by
  refine Quotient.inductionOn p ?_
  intro z
  by_cases hpos : 0 < helicity z.1
  · exact Or.inl (by simpa [IsProjectivePositive] using hpos)
  · by_cases hneg : helicity z.1 < 0
    · exact Or.inr (Or.inl (by simpa [IsProjectiveNegative] using hneg))
    · have hzero : helicity z.1 = 0 := by
        have hle : helicity z.1 ≤ 0 := le_of_not_gt hpos
        have hge : 0 ≤ helicity z.1 := le_of_not_gt hneg
        linarith
      exact Or.inr (Or.inr (by simpa [IsProjectiveNull] using hzero))

end InfoGeometry.Twistor.PenroseTwistor
