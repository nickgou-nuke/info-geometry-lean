import Mathlib

/-!
# Split-octonion logit and Bayesian-odds bridge

This module isolates the theorem-honest core of the CMOS evidence construction.
A pair of real quaternions carries the split quadratic form

`N(O) = normSq(O.ref) - normSq(O.anom)`.

No multiplication or nonassociativity claim is needed for the results below.
The statistical statement is that, when admission is defined by the logistic
map of the scaled split norm, the split norm is the scaled logit.  A separate
Bayesian theorem identifies the same coordinate with prior log-odds plus a
log-likelihood ratio.
-/

namespace InfoGeometry.Physics.SplitOctonionLogitBridge

open scoped Quaternion

/-- Real quaternions supplied by Mathlib. -/
abbrev RealQuaternion := Quaternion ℝ

/-- Two quaternionic evidence sheets.  This is the carrier needed by the
split quadratic form; no multiplication law is asserted in this owner file. -/
@[ext]
structure SplitEvidence where
  ref : RealQuaternion
  anom : RealQuaternion

/-- Split evidence norm of signature `(4,4)`. -/
def splitNorm (O : SplitEvidence) : ℝ :=
  Quaternion.normSq O.ref - Quaternion.normSq O.anom

/-- Logistic map in the positive-exponential coordinate. -/
noncomputable def sigmoid (x : ℝ) : ℝ :=
  Real.exp x / (1 + Real.exp x)

/-- Log-odds coordinate. -/
noncomputable def logit (p : ℝ) : ℝ :=
  Real.log (p / (1 - p))

/-- Chemical potential associated with a Bernoulli prior. -/
noncomputable def chemicalPotential (prior epsilon : ℝ) : ℝ :=
  epsilon * logit prior

/-- Complement of the logistic map. -/
theorem one_sub_sigmoid (x : ℝ) :
    1 - sigmoid x = 1 / (1 + Real.exp x) := by
  unfold sigmoid
  have hden : 1 + Real.exp x ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- Logistic values are strictly positive. -/
theorem sigmoid_pos (x : ℝ) : 0 < sigmoid x := by
  unfold sigmoid
  positivity

/-- Logistic values are strictly below one. -/
theorem sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := by
  have hcomp : 0 < 1 - sigmoid x := by
    rw [one_sub_sigmoid]
    positivity
  linarith

/-- Exact odds of the logistic map. -/
theorem sigmoid_odds (x : ℝ) :
    sigmoid x / (1 - sigmoid x) = Real.exp x := by
  rw [one_sub_sigmoid]
  unfold sigmoid
  have hden : 1 + Real.exp x ≠ 0 := by positivity
  field_simp [hden]

/-- Logit is a left inverse of the logistic map. -/
theorem logit_sigmoid (x : ℝ) : logit (sigmoid x) = x := by
  unfold logit
  rw [sigmoid_odds, Real.log_exp]

/-- The split norm is exactly the scaled logit of its Gibbs-Fermi admission
probability.  This is an encoding identity, not an independent physical law. -/
theorem split_norm_is_logit
    (O : SplitEvidence) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    splitNorm O = epsilon * logit (sigmoid (splitNorm O / epsilon)) := by
  rw [logit_sigmoid]
  field_simp [ne_of_gt hepsilon]

/-- Version with an explicitly named admission probability. -/
theorem split_norm_is_logit_of_admission
    (O : SplitEvidence) (epsilon r : ℝ) (hepsilon : 0 < epsilon)
    (hr : r = sigmoid (splitNorm O / epsilon)) :
    splitNorm O = epsilon * logit r := by
  subst r
  exact split_norm_is_logit O epsilon hepsilon

/-- The logistic admission probability automatically lies in the open unit
interval; no external bounds hypothesis is necessary. -/
theorem admission_probability_bounds
    (O : SplitEvidence) (epsilon : ℝ) :
    0 < sigmoid (splitNorm O / epsilon) ∧
      sigmoid (splitNorm O / epsilon) < 1 := by
  exact ⟨sigmoid_pos _, sigmoid_lt_one _⟩

/-- The null cone is the balanced decision surface. -/
theorem null_cone_is_decision_boundary
    (O : SplitEvidence) (epsilon : ℝ)
    (hnull : splitNorm O = 0) :
    sigmoid (splitNorm O / epsilon) = 1 / 2 := by
  simp [sigmoid, hnull]
  norm_num

/-- Posterior probability of the admission hypothesis from a prior and two
strictly positive likelihoods. -/
noncomputable def bayesPosterior
    (prior likelihoodAdmission likelihoodRejection : ℝ) : ℝ :=
  prior * likelihoodAdmission /
    (prior * likelihoodAdmission +
      (1 - prior) * likelihoodRejection)

/-- Complementary posterior probability. -/
theorem one_sub_bayesPosterior
    {prior likelihoodAdmission likelihoodRejection : ℝ}
    (hprior0 : 0 < prior) (hprior1 : prior < 1)
    (hadm : 0 < likelihoodAdmission)
    (hrej : 0 < likelihoodRejection) :
    1 - bayesPosterior prior likelihoodAdmission likelihoodRejection =
      ((1 - prior) * likelihoodRejection) /
        (prior * likelihoodAdmission +
          (1 - prior) * likelihoodRejection) := by
  have hsum :
      prior * likelihoodAdmission +
          (1 - prior) * likelihoodRejection ≠ 0 := by
    apply ne_of_gt
    exact add_pos (mul_pos hprior0 hadm)
      (mul_pos (sub_pos.mpr hprior1) hrej)
  unfold bayesPosterior
  field_simp [hsum]
  ring

/-- Bayes' theorem in odds form. -/
theorem bayesPosterior_odds
    {prior likelihoodAdmission likelihoodRejection : ℝ}
    (hprior0 : 0 < prior) (hprior1 : prior < 1)
    (hadm : 0 < likelihoodAdmission)
    (hrej : 0 < likelihoodRejection) :
    bayesPosterior prior likelihoodAdmission likelihoodRejection /
        (1 - bayesPosterior prior likelihoodAdmission likelihoodRejection) =
      (prior / (1 - prior)) *
        (likelihoodAdmission / likelihoodRejection) := by
  rw [one_sub_bayesPosterior hprior0 hprior1 hadm hrej]
  unfold bayesPosterior
  have hsum :
      prior * likelihoodAdmission +
          (1 - prior) * likelihoodRejection ≠ 0 := by
    apply ne_of_gt
    exact add_pos (mul_pos hprior0 hadm)
      (mul_pos (sub_pos.mpr hprior1) hrej)
  have hpriorComp : 1 - prior ≠ 0 := ne_of_gt (sub_pos.mpr hprior1)
  have hadmNe : likelihoodAdmission ≠ 0 := ne_of_gt hadm
  have hrejNe : likelihoodRejection ≠ 0 := ne_of_gt hrej
  field_simp [hsum, hpriorComp, hadmNe, hrejNe]
  ring

/-- Bayes' theorem in natural log-odds coordinates: posterior logit equals
prior logit plus the log-likelihood ratio. -/
theorem logit_bayesPosterior
    {prior likelihoodAdmission likelihoodRejection : ℝ}
    (hprior0 : 0 < prior) (hprior1 : prior < 1)
    (hadm : 0 < likelihoodAdmission)
    (hrej : 0 < likelihoodRejection) :
    logit (bayesPosterior prior likelihoodAdmission likelihoodRejection) =
      logit prior +
        Real.log (likelihoodAdmission / likelihoodRejection) := by
  unfold logit
  rw [bayesPosterior_odds hprior0 hprior1 hadm hrej]
  rw [Real.log_mul]
  · rfl
  · exact ne_of_gt (div_pos hprior0 (sub_pos.mpr hprior1))
  · exact ne_of_gt (div_pos hadm hrej)

/-- Strong Bayesian bridge: if the split norm independently encodes prior
log-odds plus the log-likelihood ratio, then it is the scaled posterior logit. -/
theorem split_norm_eq_scaled_posterior_logit
    (O : SplitEvidence) (epsilon prior likelihoodAdmission likelihoodRejection : ℝ)
    (hprior0 : 0 < prior) (hprior1 : prior < 1)
    (hadm : 0 < likelihoodAdmission)
    (hrej : 0 < likelihoodRejection)
    (hencoding :
      splitNorm O = epsilon *
        (logit prior +
          Real.log (likelihoodAdmission / likelihoodRejection))) :
    splitNorm O = epsilon *
      logit (bayesPosterior prior likelihoodAdmission likelihoodRejection) := by
  rw [logit_bayesPosterior hprior0 hprior1 hadm hrej]
  exact hencoding

/-- Gibbs specialization with the rejection likelihood normalized to one. -/
noncomputable def gibbsPosterior
    (prior epsilon deviance : ℝ) : ℝ :=
  bayesPosterior prior (Real.exp (-deviance / epsilon)) 1

/-- The Gibbs posterior logit is prior logit minus scaled deviance. -/
theorem logit_gibbsPosterior
    {prior epsilon deviance : ℝ}
    (hprior0 : 0 < prior) (hprior1 : prior < 1) :
    logit (gibbsPosterior prior epsilon deviance) =
      logit prior - deviance / epsilon := by
  unfold gibbsPosterior
  rw [logit_bayesPosterior hprior0 hprior1 (Real.exp_pos _) zero_lt_one]
  simp
  ring

/-- Chemical-potential form of the Bayesian Gibbs identity. -/
theorem scaled_logit_gibbsPosterior
    {prior epsilon deviance : ℝ}
    (hprior0 : 0 < prior) (hprior1 : prior < 1)
    (hepsilon : 0 < epsilon) :
    epsilon * logit (gibbsPosterior prior epsilon deviance) =
      chemicalPotential prior epsilon - deviance := by
  rw [logit_gibbsPosterior hprior0 hprior1]
  unfold chemicalPotential
  field_simp [ne_of_gt hepsilon]
  ring

/-- Final CMOS interpretation: an independently established split-norm energy
gap `mu_c - deviance` equals the posterior log-odds energy. -/
theorem split_norm_eq_gibbs_posterior_logit
    (O : SplitEvidence) {prior epsilon deviance : ℝ}
    (hprior0 : 0 < prior) (hprior1 : prior < 1)
    (hepsilon : 0 < epsilon)
    (hencoding :
      splitNorm O = chemicalPotential prior epsilon - deviance) :
    splitNorm O =
      epsilon * logit (gibbsPosterior prior epsilon deviance) := by
  rw [scaled_logit_gibbsPosterior hprior0 hprior1 hepsilon]
  exact hencoding

end InfoGeometry.Physics.SplitOctonionLogitBridge
