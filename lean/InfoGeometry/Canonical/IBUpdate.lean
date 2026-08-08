import InfoGeometry.Canonical.IBProjective
import InfoGeometry.Canonical.IBBase
import InfoGeometry.Canonical.IBFrozenJaynes
import Mathlib.Topology.MetricSpace.Contracting

/-!
# InfoGeometry.Canonical.IBUpdate

Canonical BA update, projective machinery, and one-step contraction reductions
for the finite Information Bottleneck scaffold.
-/

open scoped BigOperators ENNReal NNReal

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.IB

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

/--
Frozen-target normalized BA step.
-/
noncomputable def ibBlahutArimotoStepFrozen
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y) : X → FinProb T := by
  classical
  intro x
  exact PMF.normalize
    (baScoreFrozen prob qT mY_givenT x)
    (baScoreFrozen_slice_ne_zero prob qT mY_givenT x)
    (baScoreFrozen_slice_ne_top prob qT mY_givenT x)

/--
If the frozen distortion term is uniform in `t` at a fixed slice `x`, the BA
update collapses to the frozen prior `qT`.

Interpretation: along this symmetry-flat slice there is no nontrivial
optimization direction after projective normalization.
-/
theorem ibBlahutArimotoStepFrozen_eq_prior_of_uniformDistortion
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (d : ℝ)
    (hUniform :
      ∀ t : T,
        (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal = d) :
    ibBlahutArimotoStepFrozen prob qT mY_givenT x = qT := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-prob.beta * d))
  have hc0 : c ≠ 0 := by
    have hcpos : 0 < c := by
      exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
    exact ne_of_gt hcpos
  have hcTop : c ≠ ⊤ := by
    simp [c]
  have hscore :
      ∀ t : T, baScoreFrozen prob qT mY_givenT x t = qT t * c := by
    intro t
    unfold baScoreFrozen
    simpa [c, hUniform t, mul_assoc, mul_left_comm, mul_comm]
  have hsum :
      (∑' t, baScoreFrozen prob qT mY_givenT x t) = c := by
    calc
      (∑' t, baScoreFrozen prob qT mY_givenT x t)
          = ∑' t, qT t * c := by
              refine tsum_congr ?_
              intro t
              exact hscore t
      _ = (∑' t, qT t) * c := by
            simpa using (ENNReal.tsum_mul_right (f := fun t => qT t) (a := c))
      _ = c := by
            rw [qT.tsum_coe, one_mul]
  ext t
  unfold ibBlahutArimotoStepFrozen
  rw [PMF.normalize_apply]
  calc
    baScoreFrozen prob qT mY_givenT x t
        * (∑' t', baScoreFrozen prob qT mY_givenT x t')⁻¹
      = (qT t * c) * c⁻¹ := by
          rw [hscore t, hsum]
    _ = qT t * (c * c⁻¹) := by
          ac_rfl
    _ = qT t * 1 := by
          rw [ENNReal.mul_inv_cancel hc0 hcTop]
    _ = qT t := by simp

/--
Slice-wise projective/Weyl invariance of the frozen BA update:
rescaling the frozen score by a positive finite factor does not change the
normalized update.
-/
lemma ibBlahutArimotoStepFrozen_slice_eq_of_score_scale
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (c : ℝ≥0∞)
    (hc0 : c ≠ 0)
    (hcTop : c ≠ ⊤) :
    PMF.normalize
      (fun t => c * baScoreFrozen prob qT mY_givenT x t)
      (by
        simpa [ENNReal.tsum_mul_left] using
          (mul_ne_zero hc0 (baScoreFrozen_slice_ne_zero prob qT mY_givenT x)))
      (by
        rw [ENNReal.tsum_mul_left]
        exact ENNReal.mul_ne_top hcTop (baScoreFrozen_slice_ne_top prob qT mY_givenT x))
      =
    ibBlahutArimotoStepFrozen prob qT mY_givenT x := by
  simpa [ibBlahutArimotoStepFrozen] using
    (pmf_normalize_eq_of_scale
      (T := T)
      (f := baScoreFrozen prob qT mY_givenT x)
      (hf0 := baScoreFrozen_slice_ne_zero prob qT mY_givenT x)
      (hfTop := baScoreFrozen_slice_ne_top prob qT mY_givenT x)
      (c := c) hc0 hcTop)

/--
Full frozen-step projective/Weyl invariance:
for any positive finite per-slice scaling `κ(x)`, the normalized BA update is unchanged.
-/
theorem ibBlahutArimotoStepFrozen_eq_of_score_ray_scale
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (κ : X → ℝ≥0∞)
    (hκ0 : ∀ x : X, κ x ≠ 0)
    (hκTop : ∀ x : X, κ x ≠ ⊤) :
    (fun x =>
      PMF.normalize
        (fun t => κ x * baScoreFrozen prob qT mY_givenT x t)
        (by
          simpa [ENNReal.tsum_mul_left] using
            (mul_ne_zero (hκ0 x) (baScoreFrozen_slice_ne_zero prob qT mY_givenT x)))
        (by
          rw [ENNReal.tsum_mul_left]
          exact ENNReal.mul_ne_top (hκTop x) (baScoreFrozen_slice_ne_top prob qT mY_givenT x)))
      =
    ibBlahutArimotoStepFrozen prob qT mY_givenT := by
  funext x
  exact ibBlahutArimotoStepFrozen_slice_eq_of_score_scale
    (X := X) (Y := Y) (T := T) prob qT mY_givenT x (κ x) (hκ0 x) (hκTop x)

/--
The standard unnormalized Blahut-Arimoto score, recovered by passing the
induced self-consistent marginal and projection into the frozen formulation.
-/
noncomputable def baScore
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : X → T → ℝ≥0∞ :=
  baScoreFrozen prob
    (inducedMarginalT prob pT_givenX)
    (inducedMProjection prob pT_givenX)

private lemma baScore_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) (t : T) :
    baScore prob pT_givenX x t ≠ ⊤ := by
  simpa [baScore] using
    baScoreFrozen_ne_top
      (prob := prob)
      (qT := inducedMarginalT prob pT_givenX)
      (mY_givenT := inducedMProjection prob pT_givenX)
      (x := x) (t := t)

/--
Intrinsic score upper bound: BA score mass at each `(x,t)` is at most `1`.

This is the projective-cone side of the estimate:
`baScore = q(t) * exp(-β·KL)` with `0 < β`, `KL ≥ 0`, hence
`exp(-β·KL) ≤ 1` and `q(t) ≤ 1`.
-/
private lemma baScore_toReal_le_one
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) (t : T) :
    (baScore prob pT_givenX x t).toReal ≤ 1 := by
  let qT := inducedMarginalT prob pT_givenX
  let d : ℝ :=
    (InfoGeometry.fin_kl_div (condYGivenX prob x) ((inducedMProjection prob pT_givenX) t)).toReal
  have hd_nonneg : 0 ≤ d := by
    simp [d]
  have hexp_le_one : Real.exp (-prob.beta * d) ≤ 1 := by
    have harg_le_zero : -prob.beta * d ≤ 0 := by
      nlinarith [prob.beta_pos, hd_nonneg]
    exact Real.exp_le_one_iff.mpr harg_le_zero
  have hq_nonneg : 0 ≤ (qT t).toReal := ENNReal.toReal_nonneg
  have hq_le_one : (qT t).toReal ≤ 1 := by
    have hq_le_one_enn : qT t ≤ (1 : ℝ≥0∞) := PMF.coe_le_one qT t
    exact (ENNReal.toReal_le_toReal (pmf_val_ne_top qT t) ENNReal.one_ne_top).2 hq_le_one_enn
  have hexp_enn_le_one :
      ENNReal.ofReal (Real.exp (-prob.beta * d)) ≤ 1 := by
    simpa using (ENNReal.ofReal_le_ofReal hexp_le_one)
  have hba_le_q : baScore prob pT_givenX x t ≤ qT t := by
    unfold baScore
    dsimp [baScoreFrozen, qT, d]
    calc
      qT t * ENNReal.ofReal (Real.exp (-prob.beta * d))
          ≤ qT t * 1 := by
            simpa [mul_comm] using mul_le_mul_right hexp_enn_le_one (qT t)
      _ = qT t := by simp
  have hba_toReal_le_q_toReal :
      (baScore prob pT_givenX x t).toReal ≤ (qT t).toReal := by
    exact (ENNReal.toReal_le_toReal
      (baScore_ne_top prob pT_givenX x t)
      (pmf_val_ne_top qT t)).2 hba_le_q
  calc
    (baScore prob pT_givenX x t).toReal
        ≤ (qT t).toReal := hba_toReal_le_q_toReal
    _ ≤ 1 := hq_le_one

private lemma baScore_slice_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    (∑' t, baScore prob pT_givenX x t) ≠ ⊤ := by
  simpa [baScore] using
    baScoreFrozen_slice_ne_top
      (prob := prob)
      (qT := inducedMarginalT prob pT_givenX)
      (mY_givenT := inducedMProjection prob pT_givenX)
      (x := x)

/--
The BA score mass is strictly positive (hence nonzero): one can pick a support
point of `qT = inducedMarginalT prob pT_givenX`, and the exponential factor in
`baScore` is always strictly positive.
-/
private lemma baScore_slice_ne_zero
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    (∑' t, baScore prob pT_givenX x t) ≠ 0 := by
  simpa [baScore] using
    baScoreFrozen_slice_ne_zero
      (prob := prob)
      (qT := inducedMarginalT prob pT_givenX)
      (mY_givenT := inducedMProjection prob pT_givenX)
      (x := x)

/--
The standard canonical BA update, recovered as a pure specialization of the
frozen step.
-/
noncomputable def ibBlahutArimotoStep
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : X → FinProb T :=
  ibBlahutArimotoStepFrozen prob
    (inducedMarginalT prob pT_givenX)
    (inducedMProjection prob pT_givenX)

/--
Primary BA object: the unnormalized score field (projective ray representative).
-/
noncomputable def ibBlahutArimotoStepUnnormalized
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : X → T → ℝ≥0∞ :=
  baScore prob pT_givenX

/--
Canonical BA score slice as a finite nonzero representative in the unnormalized cone.
-/
noncomputable def ibBlahutArimotoScoreSlice
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) : ScoreSlice (T := T) where
  f := ibBlahutArimotoStepUnnormalized prob pT_givenX x
  nonzero := baScore_slice_ne_zero prob pT_givenX x
  finite := baScore_slice_ne_top prob pT_givenX x

/--
Canonical BA score ray (projective unnormalized state) at each slice `x`.
-/
noncomputable def ibBlahutArimotoScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : X → ScoreRay (T := T) :=
  fun x => Quotient.mk (scoreSliceSetoid (T := T))
    (ibBlahutArimotoScoreSlice prob pT_givenX x)

/--
If BA unnormalized scores are slice-wise on the same projective ray, BA score rays coincide.
-/
theorem ibBlahutArimotoScoreRay_eq_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay : ∀ x : X, SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
      =
    ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q := by
  funext x
  apply Quotient.sound
  simpa [ibBlahutArimotoScoreSlice, ibBlahutArimotoStepUnnormalized] using hRay x

/--
Radial degree (volume-changing part) of the BA unnormalized score at a slice.
-/
noncomputable def ibBlahutArimotoStepDegree
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X) : ℝ≥0∞ :=
  scoreRayDegree (T := T) (ibBlahutArimotoStepUnnormalized prob pT_givenX x)

/--
When the BA score mass is nonzero, the BA step is exactly the normalization
of the BA score.
-/
lemma ibBlahutArimotoStep_apply_eq_normalize
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X)
    (h0 : (∑' t, baScore prob pT_givenX x t) ≠ 0) :
    ibBlahutArimotoStep prob pT_givenX x
      = PMF.normalize (baScore prob pT_givenX x) h0
          (baScoreFrozen_slice_ne_top prob _ _ x) := by
  have hproof :
      h0 = baScoreFrozen_slice_ne_zero prob
        (inducedMarginalT prob pT_givenX)
        (inducedMProjection prob pT_givenX) x := by
    exact Subsingleton.elim _ _
  cases hproof
  rfl

/--
The normalized BA update is exactly the projective gauge-fixing of the
unnormalized BA score.
-/
lemma ibBlahutArimotoStep_eq_scoreProjectiveGauge
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X) :
    ibBlahutArimotoStep prob pT_givenX x
      =
    scoreProjectiveGauge (T := T)
      (ibBlahutArimotoStepUnnormalized prob pT_givenX x)
      (baScore_slice_ne_zero prob pT_givenX x)
      (baScore_slice_ne_top prob pT_givenX x) := by
  simpa [scoreProjectiveGauge, ibBlahutArimotoStepUnnormalized] using
    (ibBlahutArimotoStep_apply_eq_normalize
      (X := X) (Y := Y) (T := T) prob pT_givenX x
      (baScore_slice_ne_zero prob pT_givenX x))

/--
BA normalization is exactly the gauge section of the BA score ray.
-/
lemma ibBlahutArimotoStep_eq_scoreRayGaugeSection
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    ibBlahutArimotoStep prob pT_givenX x
      = ScoreRay.gaugeSection (T := T) (ibBlahutArimotoScoreRay prob pT_givenX x) := by
  simp [ibBlahutArimotoScoreRay, ibBlahutArimotoScoreSlice,
    ScoreSlice.gaugeSection, ibBlahutArimotoStep_eq_scoreProjectiveGauge]

/--
Normalized BA updates are derived from score rays: equality of BA score-ray maps
implies equality of BA normalized updates.
-/
theorem ibBlahutArimotoStep_eq_of_scoreRay_eq
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
        =
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q) :
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p
      =
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q := by
  funext x
  have hx :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p x
        =
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q x := by
    simpa using congrArg (fun F => F x) hRay
  calc
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p x
        = ScoreRay.gaugeSection (T := T)
            (ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p x) :=
          ibBlahutArimotoStep_eq_scoreRayGaugeSection
            (X := X) (Y := Y) (T := T) prob p x
    _ = ScoreRay.gaugeSection (T := T)
          (ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q x) := by
          simpa [hx]
    _ = ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q x := by
          symm
          exact ibBlahutArimotoStep_eq_scoreRayGaugeSection
            (X := X) (Y := Y) (T := T) prob q x

/--
Global BA update equality from slice-wise score-ray equivalence.
This is the canonical corollary: PMF-level equality is derived from ray-level equality.
-/
theorem ibBlahutArimotoStep_eq_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay : ∀ x : X, SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p
      =
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q := by
  exact ibBlahutArimotoStep_eq_of_scoreRay_eq
    (X := X) (Y := Y) (T := T) prob p q
    (ibBlahutArimotoScoreRay_eq_of_sameScoreRay
      (X := X) (Y := Y) (T := T) prob p q hRay)

/--
Slice-wise radial/projective decomposition of BA:
unnormalized score = degree × normalized projective representative.
-/
theorem ibBlahutArimotoStep_radial_projective_split
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) (t : T) :
    ibBlahutArimotoStepDegree prob pT_givenX x
      * (ibBlahutArimotoStep prob pT_givenX x t)
      =
    ibBlahutArimotoStepUnnormalized prob pT_givenX x t := by
  unfold ibBlahutArimotoStepDegree
  rw [ibBlahutArimotoStep_eq_scoreProjectiveGauge (X := X) (Y := Y) (T := T) prob pT_givenX x]
  exact score_radial_projective_factorization
    (T := T)
    (f := ibBlahutArimotoStepUnnormalized prob pT_givenX x)
    (hf0 := baScore_slice_ne_zero prob pT_givenX x)
    (hfTop := baScore_slice_ne_top prob pT_givenX x)
    t

/--
Intrinsic BA projective invariance under positive finite per-slice dilations of
the unnormalized score.
-/
theorem ibBlahutArimotoStep_eq_of_score_ray_scale
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (κ : X → ℝ≥0∞)
    (hκ0 : ∀ x : X, κ x ≠ 0)
    (hκTop : ∀ x : X, κ x ≠ ⊤) :
    (fun x =>
      PMF.normalize
        (fun t => κ x * ibBlahutArimotoStepUnnormalized prob pT_givenX x t)
        (by
          simpa [ibBlahutArimotoStepUnnormalized, ENNReal.tsum_mul_left] using
            (mul_ne_zero (hκ0 x) (baScore_slice_ne_zero prob pT_givenX x)))
        (by
          rw [ENNReal.tsum_mul_left]
          simpa [ibBlahutArimotoStepUnnormalized] using
            (ENNReal.mul_ne_top (hκTop x) (baScore_slice_ne_top prob pT_givenX x))))
      = ibBlahutArimotoStep prob pT_givenX := by
  funext x
  rw [ibBlahutArimotoStep_eq_scoreProjectiveGauge (X := X) (Y := Y) (T := T) prob pT_givenX x]
  exact pmf_normalize_eq_of_scale
    (T := T)
    (f := ibBlahutArimotoStepUnnormalized prob pT_givenX x)
    (hf0 := baScore_slice_ne_zero prob pT_givenX x)
    (hfTop := baScore_slice_ne_top prob pT_givenX x)
    (c := κ x) (hκ0 x) (hκTop x)

/--
Cartan-style split under BA-score dilations:
radial degree scales multiplicatively, projective BA update is invariant.
-/
theorem ibBlahutArimotoStep_dilation_split
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (κ : X → ℝ≥0∞)
    (hκ0 : ∀ x : X, κ x ≠ 0)
    (hκTop : ∀ x : X, κ x ≠ ⊤) :
    (∀ x : X,
      scoreRayDegree (T := T)
        (fun t => κ x * ibBlahutArimotoStepUnnormalized prob pT_givenX x t)
          = κ x * ibBlahutArimotoStepDegree prob pT_givenX x)
    ∧
    ((fun x =>
      PMF.normalize
        (fun t => κ x * ibBlahutArimotoStepUnnormalized prob pT_givenX x t)
        (by
          simpa [ibBlahutArimotoStepUnnormalized, ENNReal.tsum_mul_left] using
            (mul_ne_zero (hκ0 x) (baScore_slice_ne_zero prob pT_givenX x)))
        (by
          rw [ENNReal.tsum_mul_left]
          simpa [ibBlahutArimotoStepUnnormalized] using
            (ENNReal.mul_ne_top (hκTop x) (baScore_slice_ne_top prob pT_givenX x))))
      = ibBlahutArimotoStep prob pT_givenX) := by
  refine ⟨?_, ?_⟩
  · intro x
    unfold ibBlahutArimotoStepDegree
    simpa [ibBlahutArimotoStepUnnormalized] using
      scoreRayDegree_scale
        (T := T)
        (f := ibBlahutArimotoStepUnnormalized prob pT_givenX x)
        (c := κ x)
  · exact ibBlahutArimotoStep_eq_of_score_ray_scale
      (X := X) (Y := Y) (T := T) prob pT_givenX κ hκ0 hκTop

section MeasureProjectiveBridge

variable [Nonempty T]

/--
Canonical BA slice as a measure-projective ray class.
This keeps the ontology at ray level, with normalization only as section choice.
-/
noncomputable def ibBlahutArimotoProjectiveState
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) :
    X → InfoGeometry.MeasureProjective.ProjectiveState T :=
  fun x =>
    ScoreRay.projectiveState (T := T)
      (ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob pT_givenX x)

/--
Slice equality of BA updates under score-ray equivalence.
-/
lemma ibBlahutArimotoStep_slice_eq_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (x : X)
    (hRay : SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ibBlahutArimotoStep prob p x = ibBlahutArimotoStep prob q x := by
  have hp :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x
        = PMF.normalize
            (baScore prob p x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x) := by
    simpa using
      (ibBlahutArimotoStep_apply_eq_normalize
        (X := X) (Y := Y) (T := T) prob p x
        (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x))
  have hq :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x
        = PMF.normalize
            (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x) := by
    simpa using
      (ibBlahutArimotoStep_apply_eq_normalize
        (X := X) (Y := Y) (T := T) prob q x
        (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x))
  have hnorm :
      PMF.normalize
          (baScore prob q x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)
        =
      PMF.normalize
          (baScore prob p x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x) := by
    simpa using
      (pmf_normalize_eq_of_sameScoreRay
        (T := T)
        (hRay := hRay)
        (hf0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
        (hfTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x)
        (hg0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
        (hgTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
  rw [hp, hq]
  exact hnorm.symm

/--
Global BA projective-state invariance under slice-wise score-ray equivalence.
-/
theorem ibBlahutArimotoProjectiveState_eq_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay : ∀ x : X, SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ibBlahutArimotoProjectiveState (X := X) (Y := Y) (T := T) prob p
      =
    ibBlahutArimotoProjectiveState (X := X) (Y := Y) (T := T) prob q := by
  have hScore :=
    ibBlahutArimotoScoreRay_eq_of_sameScoreRay
      (X := X) (Y := Y) (T := T) prob p q hRay
  funext x
  simpa [ibBlahutArimotoProjectiveState] using
    congrArg (fun F => ScoreRay.projectiveState (T := T) (F x)) hScore

/--
Projective BA state equality derived directly from equality of BA score-ray maps.
-/
theorem ibBlahutArimotoProjectiveState_eq_of_scoreRay_eq
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
        =
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q) :
    ibBlahutArimotoProjectiveState (X := X) (Y := Y) (T := T) prob p
      =
    ibBlahutArimotoProjectiveState (X := X) (Y := Y) (T := T) prob q := by
  funext x
  simpa [ibBlahutArimotoProjectiveState] using
    congrArg (fun F => ScoreRay.projectiveState (T := T) (F x)) hRay

/--
BA projective-state invariance under positive finite score dilations.
-/
theorem ibBlahutArimotoProjectiveState_eq_of_score_ray_scale
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (κ : X → ℝ≥0∞)
    (hκ0 : ∀ x : X, κ x ≠ 0)
    (hκTop : ∀ x : X, κ x ≠ ⊤) :
    (fun x =>
      InfoGeometry.MeasureProjective.Normalized.pmfToProjectiveState
        (PMF.normalize
          (fun t => κ x * ibBlahutArimotoStepUnnormalized prob pT_givenX x t)
          (by
            simpa [ibBlahutArimotoStepUnnormalized, ENNReal.tsum_mul_left] using
              (mul_ne_zero (hκ0 x) (baScore_slice_ne_zero prob pT_givenX x)))
          (by
            rw [ENNReal.tsum_mul_left]
            simpa [ibBlahutArimotoStepUnnormalized] using
              (ENNReal.mul_ne_top (hκTop x) (baScore_slice_ne_top prob pT_givenX x)))))
      =
    ibBlahutArimotoProjectiveState (X := X) (Y := Y) (T := T) prob pT_givenX := by
  funext x
  have hscale :=
    ibBlahutArimotoStep_eq_of_score_ray_scale
      (X := X) (Y := Y) (T := T) prob pT_givenX κ hκ0 hκTop
  have hx :
      PMF.normalize
          (fun t => κ x * ibBlahutArimotoStepUnnormalized prob pT_givenX x t)
          (by
            simpa [ibBlahutArimotoStepUnnormalized, ENNReal.tsum_mul_left] using
              (mul_ne_zero (hκ0 x) (baScore_slice_ne_zero prob pT_givenX x)))
          (by
            rw [ENNReal.tsum_mul_left]
            simpa [ibBlahutArimotoStepUnnormalized] using
              (ENNReal.mul_ne_top (hκTop x) (baScore_slice_ne_top prob pT_givenX x)))
        = ibBlahutArimotoStep prob pT_givenX x := by
    simpa using congrArg (fun f => f x) hscale
  simpa [ibBlahutArimotoProjectiveState] using
    congrArg InfoGeometry.MeasureProjective.Normalized.pmfToProjectiveState hx

end MeasureProjectiveBridge

/--
The intrinsic BA score is the frozen score specialized to induced target data.
-/
@[simp] lemma baScore_eq_baScoreFrozen_induced
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    baScore prob pT_givenX x
      = baScoreFrozen prob (inducedMarginalT prob pT_givenX) (inducedMProjection prob pT_givenX) x := rfl

/--
The intrinsic BA step is the frozen-target normalized step specialized to
induced target data.
-/
lemma ibBlahutArimotoStep_eq_frozen_induced
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) :
    ibBlahutArimotoStep prob pT_givenX
      = ibBlahutArimotoStepFrozen prob (inducedMarginalT prob pT_givenX) (inducedMProjection prob pT_givenX) := rfl

/-! ### Concrete Sup-Metric Contraction Reductions -/

/--
Concrete finite sup metric on `FinProb T`, using pointwise masses in `ℝ≥0∞`.
-/
noncomputable def finProbMassNndist
    (p q : FinProb T) : ℝ≥0 :=
  Finset.sup Finset.univ (fun t => nndist (p t).toReal (q t).toReal)

/--
Pointwise mass-distance is bounded by the finite sup metric on `FinProb T`.
-/
lemma nndist_eval_le_finProbMassNndist
    (p q : FinProb T) (t : T) :
    nndist (p t).toReal (q t).toReal ≤ finProbMassNndist (T := T) p q := by
  unfold finProbMassNndist
  exact Finset.le_sup
    (s := Finset.univ)
    (f := fun t : T => nndist (p t).toReal (q t).toReal)
    (Finset.mem_univ t)

/--
Concrete encoder sup metric obtained by taking finite sup over `x` of
`finProbMassNndist` on each conditional law `p(·|x)`.
-/
noncomputable def encoderMassNndist
    (p q : X → FinProb T) : ℝ≥0 :=
  Finset.sup Finset.univ (fun x => finProbMassNndist (T := T) (p x) (q x))

/--
Pointwise encoder slice distance is bounded by encoder sup metric.
-/
lemma finProbMassNndist_eval_le_encoderMassNndist
    (p q : X → FinProb T) (x : X) :
    finProbMassNndist (T := T) (p x) (q x) ≤ encoderMassNndist (X := X) (T := T) p q := by
  unfold encoderMassNndist
  exact Finset.le_sup
    (s := Finset.univ)
    (f := fun x : X => finProbMassNndist (T := T) (p x) (q x))
    (Finset.mem_univ x)

/--
Intrinsic normalize stability under projective score-ray equivalence:
if two BA scores at slice `x` lie on the same positive ray, their normalized
updates coincide, hence the mass-sup distance vanishes (`K = 0`).
-/
theorem ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay : ∀ x : X, SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ∀ x : X,
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ (0 : ℝ≥0) * finProbMassNndist (T := T) (p x) (q x) := by
  intro x
  have hp :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x
        = PMF.normalize
            (baScore prob p x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x) := by
    simpa using
      (ibBlahutArimotoStep_apply_eq_normalize
        (X := X) (Y := Y) (T := T) prob p x
        (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x))
  have hq :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x
        = PMF.normalize
            (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x) := by
    simpa using
      (ibBlahutArimotoStep_apply_eq_normalize
        (X := X) (Y := Y) (T := T) prob q x
        (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x))
  have hnorm :
      PMF.normalize
          (baScore prob q x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)
        =
      PMF.normalize
          (baScore prob p x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x) := by
    simpa using
      (pmf_normalize_eq_of_sameScoreRay
        (T := T)
        (hRay := hRay x)
        (hf0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
        (hfTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x)
        (hg0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
        (hgTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
  have hstep :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x
        = (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x := by
    rw [hp, hq]
    exact hnorm.symm
  have hdist :
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        = 0 := by
    simpa [hstep, finProbMassNndist]
  simpa [hdist]

/--
Concrete contraction lift in the explicit mass sup metric:
pointwise contraction on each `x` implies global contraction on encoders.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_of_pointwise
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hPointwise :
      ∀ p q : X → FinProb T, ∀ x : X,
        finProbMassNndist (T := T)
          ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
          ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x)) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderMassNndist (X := X) (T := T) p q := by
  intro p q
  unfold encoderMassNndist
  refine Finset.sup_le ?_
  intro x hx
  calc
    finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ Kc * finProbMassNndist (T := T) (p x) (q x) := hPointwise p q x
    _ ≤ Kc * Finset.sup Finset.univ
          (fun x => finProbMassNndist (T := T) (p x) (q x)) := by
      have hsup :
          finProbMassNndist (T := T) (p x) (q x) ≤
            Finset.sup Finset.univ (fun x => finProbMassNndist (T := T) (p x) (q x)) := by
        exact Finset.le_sup
          (s := Finset.univ)
          (f := fun x : X => finProbMassNndist (T := T) (p x) (q x))
          (Finset.mem_univ x)
      exact mul_le_mul_of_nonneg_left hsup Kc.2

/--
Global encoder contraction under slice-wise score-ray equivalence (`K = 0`).
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_zero_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (hRay :
      ∀ p q : X → FinProb T, ∀ x : X,
        SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ (0 : ℝ≥0) * encoderMassNndist (X := X) (T := T) p q := by
  exact ibBlahutArimotoStep_encoderMassNndist_le_of_pointwise
    (X := X) (Y := Y) (T := T) (prob := prob) (Kc := 0)
    (hPointwise := by
      intro p q x
      exact ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_sameScoreRay
        (X := X) (Y := Y) (T := T) prob p q (fun x' => hRay p q x') x)

/--
Pointwise zero-contraction corollary driven directly by BA score-ray map equality.
-/
theorem ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_scoreRay_eq
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
        =
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q) :
    ∀ x : X,
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ (0 : ℝ≥0) * finProbMassNndist (T := T) (p x) (q x) := by
  intro x
  have hstep :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x
        = (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x := by
    simpa using congrArg (fun F => F x)
      (ibBlahutArimotoStep_eq_of_scoreRay_eq
        (X := X) (Y := Y) (T := T) prob p q hRay)
  have hdist :
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        = 0 := by
    simpa [hstep, finProbMassNndist]
  simpa [hdist]

/--
Global zero-contraction corollary driven directly by BA score-ray map equality.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_zero_of_scoreRay_eq
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
        =
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q) :
    encoderMassNndist (X := X) (T := T)
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
      ≤ (0 : ℝ≥0) * encoderMassNndist (X := X) (T := T) p q := by
  unfold encoderMassNndist
  refine Finset.sup_le ?_
  intro x hx
  calc
    finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ (0 : ℝ≥0) * finProbMassNndist (T := T) (p x) (q x) :=
      ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_scoreRay_eq
        (X := X) (Y := Y) (T := T) prob p q hRay x
    _ = 0 := by simp
    _ = (0 : ℝ≥0) * encoderMassNndist (X := X) (T := T) p q := by simp

/--
Pointwise BA contraction reduction:
it is enough to prove the contraction estimate after rewriting BA updates as
normalizations of BA scores (under nonzero score mass).
-/
theorem ibBlahutArimotoStep_pointwise_massNndist_le_of_normalize
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hNonzero :
      ∀ p : X → FinProb T, ∀ x : X,
        (∑' t, baScore prob p x t) ≠ 0)
    (hNormalize :
      ∀ p q : X → FinProb T, ∀ x : X,
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x) (hNonzero p x) (baScore_slice_ne_top prob p x))
          (PMF.normalize (baScore prob q x) (hNonzero q x) (baScore_slice_ne_top prob q x))
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x)) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x) := by
  intro p q x
  have hp :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x
        = PMF.normalize (baScore prob p x) (hNonzero p x) (baScore_slice_ne_top prob p x) := by
    simpa using ibBlahutArimotoStep_apply_eq_normalize (X := X) (Y := Y) (T := T) prob p x (hNonzero p x)
  have hq :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x
        = PMF.normalize (baScore prob q x) (hNonzero q x) (baScore_slice_ne_top prob q x) := by
    simpa using ibBlahutArimotoStep_apply_eq_normalize (X := X) (Y := Y) (T := T) prob q x (hNonzero q x)
  simpa [hp, hq] using hNormalize p q x

/--
Global BA contraction reduction in the explicit mass sup metric:
combine the normalize-form pointwise estimate with finite-sup lifting.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_of_normalize
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hNonzero :
      ∀ p : X → FinProb T, ∀ x : X,
        (∑' t, baScore prob p x t) ≠ 0)
    (hNormalize :
      ∀ p q : X → FinProb T, ∀ x : X,
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x) (hNonzero p x) (baScore_slice_ne_top prob p x))
          (PMF.normalize (baScore prob q x) (hNonzero q x) (baScore_slice_ne_top prob q x))
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x)) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderMassNndist (X := X) (T := T) p q := by
  exact ibBlahutArimotoStep_encoderMassNndist_le_of_pointwise
    (X := X) (Y := Y) (T := T) prob
    (hPointwise :=
      ibBlahutArimotoStep_pointwise_massNndist_le_of_normalize
        (X := X) (Y := Y) (T := T) prob hNonzero hNormalize)

/--
Pointwise BA contraction reduction with intrinsic nonzero-score discharge:
only the normalize-form estimate remains as an external analytic obligation.
-/
theorem ibBlahutArimotoStep_pointwise_massNndist_le_of_normalize_intrinsicNonzero
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hNormalize :
      ∀ p q : X → FinProb T, ∀ x : X,
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x))
          (PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x))
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x)) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x) := by
  intro p q x
  simpa [ibBlahutArimotoStep] using hNormalize p q x

/--
Internal normalize-form zero-contraction property:
slice-wise score-ray equivalence implies the normalize inequality with `K = 0`.
-/
theorem baNormalize_pointwise_massNndist_le_zero_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (hRay :
      ∀ p q : X → FinProb T, ∀ x : X,
        SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        (PMF.normalize (baScore prob p x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x))
        (PMF.normalize (baScore prob q x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
        ≤ (0 : ℝ≥0) * finProbMassNndist (T := T) (p x) (q x) := by
  intro p q x
  have hnorm :
      PMF.normalize (baScore prob q x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)
        =
      PMF.normalize (baScore prob p x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x) := by
    simpa using
      (pmf_normalize_eq_of_sameScoreRay
        (T := T)
        (hRay := hRay p q x)
        (hf0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
        (hfTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x)
        (hg0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
        (hgTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
  have hdist :
      finProbMassNndist (T := T)
        (PMF.normalize (baScore prob p x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x))
        (PMF.normalize (baScore prob q x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
        = 0 := by
    have hnorm' :
        PMF.normalize (baScore prob p x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x)
          =
        PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x) := hnorm.symm
    have hrewrite :
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x))
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
          =
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)) := by
      exact congrArg
        (fun r =>
          finProbMassNndist (T := T) r
            (PMF.normalize (baScore prob q x)
              (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
              (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)))
        hnorm'
    calc
      finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x))
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
          =
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)) := by
              exact hrewrite
      _ = 0 := by simp [finProbMassNndist]
  simpa [hdist]

/--
General normalize-Lipschitz estimate (nonzero `Kc`) under explicit lower-mass
control on score slices.

The bound is driven by:
- slice mass lower bound (`m`)
- pointwise score Lipschitz (`Kscore`)
- reciprocal-mass Lipschitz (`Kinv`)
- pointwise score upper bound (`ub`)
-/
theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz
    (prob : IBProblem (X := X) (Y := Y))
    {m Kscore Kinv ub : ℝ}
    (Kc : ℝ≥0)
    (hm : 0 < m)
    (hKscore_nonneg : 0 ≤ Kscore)
    (hKinv_nonneg : 0 ≤ Kinv)
    (hKc : (Kc : ℝ) = Kscore / m + ub * Kinv)
    (hMassLower :
      ∀ p : X → FinProb T, ∀ x : X,
        m ≤ ((∑' t, baScore prob p x t).toReal))
    (hScoreUpper :
      ∀ p : X → FinProb T, ∀ x : X, ∀ t : T,
        (baScore prob p x t).toReal ≤ ub)
    (hScoreLip :
      ∀ p q : X → FinProb T, ∀ x : X, ∀ t : T,
        |(baScore prob p x t).toReal - (baScore prob q x t).toReal|
          ≤ Kscore * ((finProbMassNndist (T := T) (p x) (q x) : ℝ)))
    (hMassInvLip :
      ∀ p q : X → FinProb T, ∀ x : X,
        |((∑' t, baScore prob p x t).toReal)⁻¹
            - ((∑' t, baScore prob q x t).toReal)⁻¹|
          ≤ Kinv * ((finProbMassNndist (T := T) (p x) (q x) : ℝ))) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        (PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x))
        (PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x))
        ≤ Kc * (finProbMassNndist (T := T) (p x) (q x)) := by
  intro p q x
  let d : ℝ := (finProbMassNndist (T := T) (p x) (q x) : ℝ)
  have hd_nonneg : 0 ≤ d := by
    exact (show 0 ≤ (finProbMassNndist (T := T) (p x) (q x) : ℝ≥0) from (finProbMassNndist (T := T) (p x) (q x)).2)
  unfold finProbMassNndist
  refine Finset.sup_le ?_
  intro t ht
  have hdist_nndist_real :
      ((nndist
        ((PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x) t).toReal)
        ((PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x) t).toReal) : ℝ))
        ≤ (Kc : ℝ) * d := by
    let Sp : ℝ := ((∑' τ, baScore prob p x τ).toReal)
    let Sq : ℝ := ((∑' τ, baScore prob q x τ).toReal)
    let a : ℝ := (baScore prob p x t).toReal
    let b : ℝ := (baScore prob q x t).toReal
    have hSp_ge : m ≤ Sp := by simpa [Sp] using hMassLower p x
    have hSq_ge : m ≤ Sq := by simpa [Sq] using hMassLower q x
    have hSp_pos : 0 < Sp := lt_of_lt_of_le hm hSp_ge
    have hSq_pos : 0 < Sq := lt_of_lt_of_le hm hSq_ge
    have hSpInv_le : Sp⁻¹ ≤ m⁻¹ := (inv_le_inv₀ hSp_pos hm).2 hSp_ge
    have hSpInv_nonneg : 0 ≤ Sp⁻¹ := by positivity
    have hb_nonneg : 0 ≤ b := by
      simpa [b] using (ENNReal.toReal_nonneg : 0 ≤ (baScore prob q x t).toReal)
    have hNum : |a - b| ≤ Kscore * d := by
      simpa [a, b, d] using hScoreLip p q x t
    have hInv : |Sp⁻¹ - Sq⁻¹| ≤ Kinv * d := by
      simpa [Sp, Sq, d] using hMassInvLip p q x
    have hb_le_ub : b ≤ ub := by
      simpa [b] using hScoreUpper q x t
    have htri :
        |a * Sp⁻¹ - b * Sq⁻¹|
          ≤ |a * Sp⁻¹ - b * Sp⁻¹| + |b * Sp⁻¹ - b * Sq⁻¹| := by
      exact abs_sub_le _ _ _
    have hfirst :
        |a * Sp⁻¹ - b * Sp⁻¹| = |a - b| * Sp⁻¹ := by
      have hsplit : a * Sp⁻¹ - b * Sp⁻¹ = (a - b) * Sp⁻¹ := by ring
      rw [hsplit, abs_mul, abs_of_nonneg hSpInv_nonneg]
    have hsecond :
        |b * Sp⁻¹ - b * Sq⁻¹| = b * |Sp⁻¹ - Sq⁻¹| := by
      have hsplit : b * Sp⁻¹ - b * Sq⁻¹ = b * (Sp⁻¹ - Sq⁻¹) := by ring
      rw [hsplit, abs_mul, abs_of_nonneg hb_nonneg]
    have hfirst_le :
        |a * Sp⁻¹ - b * Sp⁻¹| ≤ (Kscore * d) * m⁻¹ := by
      rw [hfirst]
      have hKd_nonneg : 0 ≤ Kscore * d := mul_nonneg hKscore_nonneg hd_nonneg
      have h1 : |a - b| * Sp⁻¹ ≤ (Kscore * d) * Sp⁻¹ :=
        mul_le_mul_of_nonneg_right hNum hSpInv_nonneg
      have h2 : (Kscore * d) * Sp⁻¹ ≤ (Kscore * d) * m⁻¹ :=
        mul_le_mul_of_nonneg_left hSpInv_le hKd_nonneg
      exact le_trans h1 h2
    have hsecond_le :
        |b * Sp⁻¹ - b * Sq⁻¹| ≤ ub * (Kinv * d) := by
      rw [hsecond]
      have hKd_nonneg : 0 ≤ Kinv * d := mul_nonneg hKinv_nonneg hd_nonneg
      have h1 : b * |Sp⁻¹ - Sq⁻¹| ≤ b * (Kinv * d) :=
        mul_le_mul_of_nonneg_left hInv hb_nonneg
      have h2 : b * (Kinv * d) ≤ ub * (Kinv * d) :=
        mul_le_mul_of_nonneg_right hb_le_ub hKd_nonneg
      exact le_trans h1 h2
    have htotal :
        |a * Sp⁻¹ - b * Sq⁻¹| ≤ (Kscore * d) * m⁻¹ + ub * (Kinv * d) := by
      exact le_trans htri (add_le_add hfirst_le hsecond_le)
    have hrhs :
        (Kscore * d) * m⁻¹ + ub * (Kinv * d)
          = (Kscore / m + ub * Kinv) * d := by
      calc
        (Kscore * d) * m⁻¹ + ub * (Kinv * d)
            = (Kscore * m⁻¹ + ub * Kinv) * d := by ring
        _ = (Kscore / m + ub * Kinv) * d := by
              rw [div_eq_mul_inv]
    have hnorm_p :
        ((PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x) t).toReal)
          = a * Sp⁻¹ := by
      simpa [a, Sp] using
        (pmf_normalize_apply_toReal
          (T := T)
          (f := baScore prob p x)
          (hf0 := baScore_slice_ne_zero prob p x)
          (hfTop := baScore_slice_ne_top prob p x)
          (t := t))
    have hnorm_q :
        ((PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x) t).toReal)
          = b * Sq⁻¹ := by
      simpa [b, Sq] using
        (pmf_normalize_apply_toReal
          (T := T)
          (f := baScore prob q x)
          (hf0 := baScore_slice_ne_zero prob q x)
          (hfTop := baScore_slice_ne_top prob q x)
          (t := t))
    have hdist_real :
        |((PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x) t).toReal)
          - ((PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x) t).toReal)|
          ≤ (Kc : ℝ) * d := by
      calc
        |((PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x) t).toReal)
          - ((PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x) t).toReal)|
            = |a * Sp⁻¹ - b * Sq⁻¹| := by
                rw [hnorm_p, hnorm_q]
        _ ≤ (Kscore * d) * m⁻¹ + ub * (Kinv * d) := htotal
        _ = (Kscore / m + ub * Kinv) * d := hrhs
        _ = (Kc : ℝ) * d := by rw [hKc]
    simpa [Real.nndist_eq] using hdist_real
  exact_mod_cast hdist_nndist_real

/--
Intrinsic normalize-Lipschitz estimate (nonzero `Kc`) with projective cone
upper control derived internally from BA score structure.

Compared to `baNormalize_pointwise_massNndist_le_of_massRecipLipschitz`, this
eliminates the external `hScoreUpper` property by using
`baScore_toReal_le_one`.
-/
theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz_intrinsicUpper
    (prob : IBProblem (X := X) (Y := Y))
    {m Kscore Kinv : ℝ}
    (Kc : ℝ≥0)
    (hm : 0 < m)
    (hKscore_nonneg : 0 ≤ Kscore)
    (hKinv_nonneg : 0 ≤ Kinv)
    (hKc : (Kc : ℝ) = Kscore / m + Kinv)
    (hMassLower :
      ∀ p : X → FinProb T, ∀ x : X,
        m ≤ ((∑' t, baScore prob p x t).toReal))
    (hScoreLip :
      ∀ p q : X → FinProb T, ∀ x : X, ∀ t : T,
        |(baScore prob p x t).toReal - (baScore prob q x t).toReal|
          ≤ Kscore * ((finProbMassNndist (T := T) (p x) (q x) : ℝ)))
    (hMassInvLip :
      ∀ p q : X → FinProb T, ∀ x : X,
        |((∑' t, baScore prob p x t).toReal)⁻¹
            - ((∑' t, baScore prob q x t).toReal)⁻¹|
          ≤ Kinv * ((finProbMassNndist (T := T) (p x) (q x) : ℝ))) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        (PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x))
        (PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x))
        ≤ Kc * (finProbMassNndist (T := T) (p x) (q x)) := by
  have hKc' : (Kc : ℝ) = Kscore / m + (1 : ℝ) * Kinv := by
    simpa [one_mul] using hKc
  exact baNormalize_pointwise_massNndist_le_of_massRecipLipschitz
    (X := X) (Y := Y) (T := T)
    (prob := prob)
    (m := m) (Kscore := Kscore) (Kinv := Kinv) (ub := 1)
    (Kc := Kc)
    (hm := hm)
    (hKscore_nonneg := hKscore_nonneg)
    (hKinv_nonneg := hKinv_nonneg)
    (hKc := hKc')
    (hMassLower := hMassLower)
    (hScoreUpper := by
      intro p x t
      exact baScore_toReal_le_one (X := X) (Y := Y) (T := T) prob p x t)
    (hScoreLip := hScoreLip)
    (hMassInvLip := hMassInvLip)

/--
Pointwise BA-step contraction from the intrinsic normalize-Lipschitz estimate
with internally derived score upper bound.
-/
theorem ibBlahutArimotoStep_pointwise_massNndist_le_of_massRecipLipschitz_intrinsicUpper
    (prob : IBProblem (X := X) (Y := Y))
    {m Kscore Kinv : ℝ}
    (Kc : ℝ≥0)
    (hm : 0 < m)
    (hKscore_nonneg : 0 ≤ Kscore)
    (hKinv_nonneg : 0 ≤ Kinv)
    (hKc : (Kc : ℝ) = Kscore / m + Kinv)
    (hMassLower :
      ∀ p : X → FinProb T, ∀ x : X,
        m ≤ ((∑' t, baScore prob p x t).toReal))
    (hScoreLip :
      ∀ p q : X → FinProb T, ∀ x : X, ∀ t : T,
        |(baScore prob p x t).toReal - (baScore prob q x t).toReal|
          ≤ Kscore * ((finProbMassNndist (T := T) (p x) (q x) : ℝ)))
    (hMassInvLip :
      ∀ p q : X → FinProb T, ∀ x : X,
        |((∑' t, baScore prob p x t).toReal)⁻¹
            - ((∑' t, baScore prob q x t).toReal)⁻¹|
          ≤ Kinv * ((finProbMassNndist (T := T) (p x) (q x) : ℝ))) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ Kc * (finProbMassNndist (T := T) (p x) (q x)) := by
  intro p q x
  simpa [ibBlahutArimotoStep] using
    (baNormalize_pointwise_massNndist_le_of_massRecipLipschitz_intrinsicUpper
      (X := X) (Y := Y) (T := T)
      (prob := prob)
      (Kc := Kc)
      (hm := hm)
      (hKscore_nonneg := hKscore_nonneg)
      (hKinv_nonneg := hKinv_nonneg)
      (hKc := hKc)
      (hMassLower := hMassLower)
      (hScoreLip := hScoreLip)
      (hMassInvLip := hMassInvLip)
      p q x)

/--
Global BA-step contraction in `encoderMassNndist` from the intrinsic
normalize-Lipschitz estimate with internally derived score upper bound.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_of_massRecipLipschitz_intrinsicUpper
    (prob : IBProblem (X := X) (Y := Y))
    {m Kscore Kinv : ℝ}
    (Kc : ℝ≥0)
    (hm : 0 < m)
    (hKscore_nonneg : 0 ≤ Kscore)
    (hKinv_nonneg : 0 ≤ Kinv)
    (hKc : (Kc : ℝ) = Kscore / m + Kinv)
    (hMassLower :
      ∀ p : X → FinProb T, ∀ x : X,
        m ≤ ((∑' t, baScore prob p x t).toReal))
    (hScoreLip :
      ∀ p q : X → FinProb T, ∀ x : X, ∀ t : T,
        |(baScore prob p x t).toReal - (baScore prob q x t).toReal|
          ≤ Kscore * ((finProbMassNndist (T := T) (p x) (q x) : ℝ)))
    (hMassInvLip :
      ∀ p q : X → FinProb T, ∀ x : X,
        |((∑' t, baScore prob p x t).toReal)⁻¹
            - ((∑' t, baScore prob q x t).toReal)⁻¹|
          ≤ Kinv * ((finProbMassNndist (T := T) (p x) (q x) : ℝ))) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderMassNndist (X := X) (T := T) p q := by
  exact ibBlahutArimotoStep_encoderMassNndist_le_of_pointwise
    (X := X) (Y := Y) (T := T) (prob := prob)
    (hPointwise :=
      ibBlahutArimotoStep_pointwise_massNndist_le_of_massRecipLipschitz_intrinsicUpper
        (X := X) (Y := Y) (T := T)
        (prob := prob)
        (Kc := Kc)
        (hm := hm)
        (hKscore_nonneg := hKscore_nonneg)
        (hKinv_nonneg := hKinv_nonneg)
        (hKc := hKc)
        (hMassLower := hMassLower)
        (hScoreLip := hScoreLip)
        (hMassInvLip := hMassInvLip))

/--
Global BA contraction in `encoderMassNndist` obtained from the explicit
normalize-Lipschitz estimate with lower-mass control.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_of_massRecipLipschitz
    (prob : IBProblem (X := X) (Y := Y))
    {m Kscore Kinv ub : ℝ}
    (Kc : ℝ≥0)
    (hm : 0 < m)
    (hKscore_nonneg : 0 ≤ Kscore)
    (hKinv_nonneg : 0 ≤ Kinv)
    (hKc : (Kc : ℝ) = Kscore / m + ub * Kinv)
    (hMassLower :
      ∀ p : X → FinProb T, ∀ x : X,
        m ≤ ((∑' t, baScore prob p x t).toReal))
    (hScoreUpper :
      ∀ p : X → FinProb T, ∀ x : X, ∀ t : T,
        (baScore prob p x t).toReal ≤ ub)
    (hScoreLip :
      ∀ p q : X → FinProb T, ∀ x : X, ∀ t : T,
        |(baScore prob p x t).toReal - (baScore prob q x t).toReal|
          ≤ Kscore * ((finProbMassNndist (T := T) (p x) (q x) : ℝ)))
    (hMassInvLip :
      ∀ p q : X → FinProb T, ∀ x : X,
        |((∑' t, baScore prob p x t).toReal)⁻¹
            - ((∑' t, baScore prob q x t).toReal)⁻¹|
          ≤ Kinv * ((finProbMassNndist (T := T) (p x) (q x) : ℝ))) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderMassNndist (X := X) (T := T) p q := by
  exact ibBlahutArimotoStep_encoderMassNndist_le_of_pointwise
    (X := X) (Y := Y) (T := T) (prob := prob)
    (hPointwise :=
      baNormalize_pointwise_massNndist_le_of_massRecipLipschitz
        (X := X) (Y := Y) (T := T)
        (prob := prob) (Kc := Kc)
        (hm := hm)
        (hKscore_nonneg := hKscore_nonneg)
        (hKinv_nonneg := hKinv_nonneg)
        (hKc := hKc)
        (hMassLower := hMassLower)
        (hScoreUpper := hScoreUpper)
        (hScoreLip := hScoreLip)
        (hMassInvLip := hMassInvLip))

/--
Global BA contraction reduction with intrinsic nonzero-score discharge:
it now depends only on the normalize-form pointwise estimate.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_of_normalize_intrinsicNonzero
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hNormalize :
      ∀ p q : X → FinProb T, ∀ x : X,
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x))
          (PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x))
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x)) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderMassNndist (X := X) (T := T) p q := by
  exact ibBlahutArimotoStep_encoderMassNndist_le_of_normalize
    (X := X) (Y := Y) (T := T) prob
    (hNonzero := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob)
    (hNormalize := hNormalize)

/--
Concrete encoder sup-metric (as `ℝ≥0`) induced by pointwise `nndist`.
-/
noncomputable def encoderNndist
    [PseudoMetricSpace (FinProb T)]
    (p q : X → FinProb T) : ℝ≥0 :=
  Finset.sup Finset.univ (fun x => nndist (p x) (q x))

/--
Pointwise `nndist` is bounded by the encoder sup-metric.
-/
lemma nndist_eval_le_encoderNndist
    [PseudoMetricSpace (FinProb T)]
    (p q : X → FinProb T) (x : X) :
    nndist (p x) (q x) ≤ encoderNndist (X := X) (T := T) p q := by
  unfold encoderNndist
  exact Finset.le_sup
    (s := Finset.univ)
    (f := fun x : X => nndist (p x) (q x))
    (Finset.mem_univ x)

/--
Concrete contraction lift in encoder sup-metric:
pointwise `nndist` contraction implies global encoder sup-metric contraction.
-/
theorem ibBlahutArimotoStep_encoderNndist_le_of_pointwise
    [PseudoMetricSpace (FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hPointwise :
      ∀ p q : X → FinProb T, ∀ x : X,
        nndist ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
          ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
          ≤ Kc * nndist (p x) (q x)) :
    ∀ p q : X → FinProb T,
      encoderNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderNndist (X := X) (T := T) p q := by
  intro p q
  unfold encoderNndist
  refine Finset.sup_le ?_
  intro x hx
  calc
    nndist ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ Kc * nndist (p x) (q x) := hPointwise p q x
    _ ≤ Kc * Finset.sup Finset.univ (fun x => nndist (p x) (q x)) := by
      have hsup :
          nndist (p x) (q x) ≤ Finset.sup Finset.univ (fun x => nndist (p x) (q x)) := by
        exact Finset.le_sup
          (s := Finset.univ)
          (f := fun x : X => nndist (p x) (q x))
          (Finset.mem_univ x)
      exact mul_le_mul_of_nonneg_left
        hsup Kc.2

/--
Constructive contraction packaging:
`K < 1` plus a Lipschitz property for the BA step map yields `ContractingWith K`.
-/
theorem ibBlahutArimotoStep_contracting_of_lipschitz
    [EMetricSpace (X → FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : NNReal}
    (hK : Kc < 1)
    (hLip : LipschitzWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)) :
    ContractingWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob) := by
  exact ⟨hK, hLip⟩

end InfoGeometry.Canonical.IB
