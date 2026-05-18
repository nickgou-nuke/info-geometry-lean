import InfoGeometry.Basic
import InfoGeometry.Measure.Normalized
import InfoGeometry.MeasureProjective
import InfoGeometry.Canonical.PositiveRayCore

/-!
# InfoGeometry.Canonical.IBProjective

Generic normalization and projective score geometry for finite IB slices.
-/

open scoped BigOperators ENNReal NNReal

namespace InfoGeometry.Canonical.IB

variable {T : Type}

/--
`PMF.normalize` is invariant under positive finite global rescaling of the score.

This is the local projective-ray/Weyl-gauge invariance statement for finite PMFs.
-/
lemma pmf_normalize_eq_of_scale
    (f : T → ℝ≥0∞)
    (hf0 : (∑' t, f t) ≠ 0)
    (hfTop : (∑' t, f t) ≠ ⊤)
    (c : ℝ≥0∞)
    (hc0 : c ≠ 0)
    (hcTop : c ≠ ⊤) :
    PMF.normalize
      (fun t => c * f t)
      (by
        simpa [ENNReal.tsum_mul_left] using
          (mul_ne_zero hc0 hf0))
      (by
        rw [ENNReal.tsum_mul_left]
        exact ENNReal.mul_ne_top hcTop hfTop)
      = PMF.normalize f hf0 hfTop := by
  ext t
  rw [PMF.normalize_apply, PMF.normalize_apply]
  calc
    c * f t * (∑' x, c * f x)⁻¹
        = (c * f t) / (∑' x, c * f x) := by
            rw [div_eq_mul_inv]
    _ = (c * f t) / (c * ∑' x, f x) := by
          rw [ENNReal.tsum_mul_left]
    _ = f t / (∑' x, f x) := by
          simpa using ENNReal.mul_div_mul_left
            (a := f t) (b := (∑' x, f x)) (c := c) hc0 hcTop
    _ = f t * (∑' x, f x)⁻¹ := by
          rw [div_eq_mul_inv]

/--
`toReal` pointwise formula for `PMF.normalize`.
-/
lemma pmf_normalize_apply_toReal
    (f : T → ℝ≥0∞)
    (hf0 : (∑' t, f t) ≠ 0)
    (hfTop : (∑' t, f t) ≠ ⊤)
    (t : T) :
    ((PMF.normalize f hf0 hfTop t).toReal)
      = (f t).toReal * ((∑' x, f x).toReal)⁻¹ := by
  rw [PMF.normalize_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]

/--
Two score functions lie on the same positive projective ray.
-/
def SameScoreRay (f g : T → ℝ≥0∞) : Prop :=
  ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ g = fun t => c * f t

lemma SameScoreRay.refl (f : T → ℝ≥0∞) :
    SameScoreRay (T := T) f f := by
  refine ⟨1, one_ne_zero, ENNReal.one_ne_top, ?_⟩
  funext t
  simp

lemma SameScoreRay.symm {f g : T → ℝ≥0∞}
    (h : SameScoreRay (T := T) f g) :
    SameScoreRay (T := T) g f := by
  rcases h with ⟨c, hc0, hcTop, rfl⟩
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hcTop, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  funext t
  have hmul : c⁻¹ * (c * f t) = f t := by
    calc
      c⁻¹ * (c * f t) = (c⁻¹ * c) * f t := by ac_rfl
      _ = 1 * f t := by rw [ENNReal.inv_mul_cancel hc0 hcTop]
      _ = f t := by simp
  simpa [mul_assoc] using hmul.symm

lemma SameScoreRay.trans {f g h : T → ℝ≥0∞}
    (hfg : SameScoreRay (T := T) f g)
    (hgh : SameScoreRay (T := T) g h) :
    SameScoreRay (T := T) f h := by
  rcases hfg with ⟨c₁, hc₁0, hc₁Top, hg⟩
  rcases hgh with ⟨c₂, hc₂0, hc₂Top, hh⟩
  refine ⟨c₂ * c₁, mul_ne_zero hc₂0 hc₁0, ENNReal.mul_ne_top hc₂Top hc₁Top, ?_⟩
  funext t
  rw [hh, hg]
  simp [mul_comm, mul_left_comm]

instance sameScoreRaySetoid : Setoid (T → ℝ≥0∞) where
  r := SameScoreRay (T := T)
  iseqv := by
    refine ⟨SameScoreRay.refl (T := T), ?_, ?_⟩
    · intro f g hfg
      exact SameScoreRay.symm (T := T) hfg
    · intro f g h hfg hgh
      exact SameScoreRay.trans (T := T) hfg hgh

/--
Radial (volume-changing) degree of an unnormalized score: total slice mass.
-/
noncomputable def scoreRayDegree (f : T → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t, f t

/--
Projective (volume-preserving) gauge section of an unnormalized score.
-/
noncomputable def scoreProjectiveGauge
    (f : T → ℝ≥0∞)
    (hf0 : scoreRayDegree (T := T) f ≠ 0)
    (hfTop : scoreRayDegree (T := T) f ≠ ⊤) : FinProb T :=
  PMF.normalize f hf0 hfTop

/--
Normalization depends only on the projective ray of the score.
-/
lemma pmf_normalize_eq_of_sameScoreRay
    {f g : T → ℝ≥0∞}
    (hRay : SameScoreRay (T := T) f g)
    (hf0 : (∑' t, f t) ≠ 0)
    (hfTop : (∑' t, f t) ≠ ⊤)
    (hg0 : (∑' t, g t) ≠ 0)
    (hgTop : (∑' t, g t) ≠ ⊤) :
    PMF.normalize g hg0 hgTop = PMF.normalize f hf0 hfTop := by
  rcases hRay with ⟨c, hc0, hcTop, rfl⟩
  have h0eq :
      hg0 =
        (by
          simpa [ENNReal.tsum_mul_left] using
            (mul_ne_zero hc0 hf0)) := by
    exact Subsingleton.elim _ _
  have hTopeq :
      hgTop =
        (by
          rw [ENNReal.tsum_mul_left]
          exact ENNReal.mul_ne_top hcTop hfTop) := by
    exact Subsingleton.elim _ _
  cases h0eq
  cases hTopeq
  exact pmf_normalize_eq_of_scale
    (T := T) f hf0 hfTop c hc0 hcTop

/-- Dilation rescales score-ray degree multiplicatively. -/
lemma scoreRayDegree_scale
    (f : T → ℝ≥0∞)
    (c : ℝ≥0∞) :
    scoreRayDegree (T := T) (fun t => c * f t)
      = c * scoreRayDegree (T := T) f := by
  unfold scoreRayDegree
  rw [ENNReal.tsum_mul_left]

/--
Projective gauge is invariant on score rays.
-/
lemma scoreProjectiveGauge_eq_of_sameScoreRay
    {f g : T → ℝ≥0∞}
    (hRay : SameScoreRay (T := T) f g)
    (hf0 : scoreRayDegree (T := T) f ≠ 0)
    (hfTop : scoreRayDegree (T := T) f ≠ ⊤)
    (hg0 : scoreRayDegree (T := T) g ≠ 0)
    (hgTop : scoreRayDegree (T := T) g ≠ ⊤) :
    scoreProjectiveGauge (T := T) g hg0 hgTop
      = scoreProjectiveGauge (T := T) f hf0 hfTop := by
  exact pmf_normalize_eq_of_sameScoreRay
    (T := T) hRay hf0 hfTop hg0 hgTop

/--
Finite nonzero score slice: a concrete representative of a projective score ray.
-/
structure ScoreSlice where
  f : T → ℝ≥0∞
  nonzero : scoreRayDegree (T := T) f ≠ 0
  finite : scoreRayDegree (T := T) f ≠ ⊤

instance scoreSliceSetoid : Setoid (ScoreSlice (T := T)) where
  r s₁ s₂ := SameScoreRay (T := T) s₁.f s₂.f
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      exact SameScoreRay.refl (T := T) s.f
    · intro s₁ s₂ h
      exact SameScoreRay.symm (T := T) h
    · intro s₁ s₂ s₃ h₁₂ h₂₃
      exact SameScoreRay.trans (T := T) h₁₂ h₂₃

/-- Projective score-ray state space (unnormalized cone modulo positive scaling). -/
abbrev ScoreRay : Type := Quotient (scoreSliceSetoid (T := T))

namespace ScoreSlice

/-- Canonical PMF gauge section attached to a concrete nonzero finite score slice. -/
noncomputable def gaugeSection (s : ScoreSlice (T := T)) : FinProb T :=
  scoreProjectiveGauge (T := T) s.f s.nonzero s.finite

end ScoreSlice

namespace ScoreRay

/-- Canonical PMF gauge section attached to a projective score ray class. -/
noncomputable def gaugeSection : ScoreRay (T := T) → FinProb T :=
  Quotient.lift
    (fun s : ScoreSlice (T := T) => s.gaugeSection)
    (by
      intro s₁ s₂ hs
      exact scoreProjectiveGauge_eq_of_sameScoreRay
        (T := T)
        hs
        s₁.nonzero s₁.finite
        s₂.nonzero s₂.finite |> Eq.symm)

@[simp] theorem gaugeSection_mk (s : ScoreSlice (T := T)) :
    gaugeSection (T := T) (Quotient.mk (scoreSliceSetoid (T := T)) s) = s.gaugeSection := rfl

section ProjectiveState

open InfoGeometry.MeasureProjective
open InfoGeometry.MeasureProjective.ProjectiveState
open InfoGeometry.MeasureProjective.Normalized

variable [MeasurableSpace T] [MeasurableSingletonClass T] [Nonempty T]

/-- A concrete nonzero finite IB score slice viewed in the widened projective-state substrate. -/
noncomputable def toProjectiveState (s : ScoreSlice (T := T)) : ProjectiveState T :=
  pmfToProjectiveState s.gaugeSection

@[simp] theorem normalize_toProjectiveState (s : ScoreSlice (T := T)) :
    normalize (toProjectiveState s) = pmfToProbMeasure s.gaugeSection := by
  simp [toProjectiveState]

/-- A projective IB score ray viewed in the widened nonnegative projective substrate. -/
noncomputable def projectiveState : ScoreRay (T := T) → ProjectiveState T :=
  Quotient.lift
    (fun s : ScoreSlice (T := T) => toProjectiveState s)
    (by
      intro s₁ s₂ hs
      exact congrArg pmfToProjectiveState <|
        scoreProjectiveGauge_eq_of_sameScoreRay
          (T := T)
          hs
          s₁.nonzero s₁.finite
          s₂.nonzero s₂.finite |>.symm)

@[simp] theorem projectiveState_mk (s : ScoreSlice (T := T)) :
    projectiveState (T := T) (Quotient.mk (scoreSliceSetoid (T := T)) s) = toProjectiveState s := rfl

@[simp] theorem normalize_projectiveState
    (q : ScoreRay (T := T)) :
    normalize (projectiveState (T := T) q) = pmfToProbMeasure (gaugeSection (T := T) q) := by
  refine Quotient.inductionOn q ?_
  intro s
  simp [projectiveState, toProjectiveState]

end ProjectiveState

end ScoreRay

/--
Full-support finite score slice: zeros and infinities are excluded pointwise, so
this slice lands in the strict-positive `PositiveRay` corridor.
-/
structure FullSupportScoreSlice extends ScoreSlice (T := T) where
  pointwise_nonzero : ∀ t : T, f t ≠ 0
  pointwise_finite : ∀ t : T, f t ≠ ⊤

instance fullSupportScoreSliceSetoid : Setoid (FullSupportScoreSlice (T := T)) where
  r s₁ s₂ := SameScoreRay (T := T) s₁.f s₂.f
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      exact SameScoreRay.refl (T := T) s.f
    · intro s₁ s₂ h
      exact SameScoreRay.symm (T := T) h
    · intro s₁ s₂ s₃ h₁₂ h₂₃
      exact SameScoreRay.trans (T := T) h₁₂ h₂₃

/-- Full-support score-ray state space. -/
abbrev FullSupportScoreRay : Type := Quotient (fullSupportScoreSliceSetoid (T := T))

namespace FullSupportScoreSlice

open InfoGeometry.Canonical.PositiveRayCore

/-- A full-support score slice as a strictly positive real-valued measure. -/
noncomputable def toPositiveMeasure (s : FullSupportScoreSlice (T := T)) : InfoGeometry.PositiveMeasure T ℝ where
  mass := fun t => (s.f t).toReal
  pos := fun t => ENNReal.toReal_pos (s.pointwise_nonzero t) (s.pointwise_finite t)

@[simp] theorem toPositiveMeasure_apply (s : FullSupportScoreSlice (T := T)) (t : T) :
    toPositiveMeasure s t = (s.f t).toReal := rfl

lemma sameRay_toPositiveMeasure
    {s₁ s₂ : FullSupportScoreSlice (T := T)}
    (hs : SameScoreRay (T := T) s₁.f s₂.f) :
    InfoGeometry.PositiveMeasure.SameRay (toPositiveMeasure s₁) (toPositiveMeasure s₂) := by
  rcases hs with ⟨c, hc0, hcTop, hscale⟩
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hcTop, ?_⟩
  ext t
  change (s₂.f t).toReal = c.toReal * (s₁.f t).toReal
  rw [hscale]
  simp [ENNReal.toReal_mul]

/-- A full-support score slice as a strict-positive projective ray. -/
noncomputable def positiveRay (s : FullSupportScoreSlice (T := T)) : PositiveRay T :=
  Quotient.mk _ (toPositiveMeasure s)

end FullSupportScoreSlice

namespace FullSupportScoreRay

open InfoGeometry.Canonical.PositiveRayCore

/-- Full-support score rays land canonically in the strict-positive `PositiveRay` substrate. -/
noncomputable def positiveRay : FullSupportScoreRay (T := T) → PositiveRay T :=
  Quotient.lift
    (fun s : FullSupportScoreSlice (T := T) => s.positiveRay)
    (by
      intro s₁ s₂ hs
      exact Quotient.sound <| FullSupportScoreSlice.sameRay_toPositiveMeasure (T := T) hs)

@[simp] theorem positiveRay_mk (s : FullSupportScoreSlice (T := T)) :
    positiveRay (T := T) (Quotient.mk (fullSupportScoreSliceSetoid (T := T)) s) = s.positiveRay := rfl

end FullSupportScoreRay

/--
Radial/projective factorization for any finite nonzero score slice.
-/
lemma score_radial_projective_factorization
    (f : T → ℝ≥0∞)
    (hf0 : scoreRayDegree (T := T) f ≠ 0)
    (hfTop : scoreRayDegree (T := T) f ≠ ⊤)
    (t : T) :
    scoreRayDegree (T := T) f
      * (scoreProjectiveGauge (T := T) f hf0 hfTop t)
      = f t := by
  unfold scoreRayDegree scoreProjectiveGauge
  rw [PMF.normalize_apply]
  have hcancel : (∑' x, f x) * (∑' x, f x)⁻¹ = 1 := by
    simpa [scoreRayDegree] using (ENNReal.mul_inv_cancel hf0 hfTop)
  calc
    (∑' x, f x) * (f t * (∑' x, f x)⁻¹)
        = f t * ((∑' x, f x) * (∑' x, f x)⁻¹) := by ac_rfl
    _ = f t * 1 := by rw [hcancel]
    _ = f t := by simp

/--
Normalization of an already normalized finite law is proof-irrelevant and
returns the same PMF.
-/
lemma pmf_normalize_eq_self
    [Fintype T]
    (p : FinProb T) :
    PMF.normalize
      (fun t => p t)
      (by
        classical
        rcases p.support_nonempty with ⟨t0, ht0⟩
        have hp0 : p t0 ≠ 0 := by
          exact (p.mem_support_iff t0).1 ht0
        have hpPos : 0 < p t0 := by
          exact lt_of_le_of_ne bot_le (Ne.symm hp0)
        have hle : p t0 ≤ ∑' t, p t := by
          rw [tsum_fintype]
          exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ t0)
        exact ne_of_gt (lt_of_lt_of_le hpPos hle))
      p.tsum_coe_ne_top = p := by
  ext t
  have hsum : (∑ t, p t) = (1 : ℝ≥0∞) := by
    have htsum := p.tsum_coe
    rw [tsum_fintype] at htsum
    exact htsum
  simp [PMF.normalize_apply, hsum]

end InfoGeometry.Canonical.IB
