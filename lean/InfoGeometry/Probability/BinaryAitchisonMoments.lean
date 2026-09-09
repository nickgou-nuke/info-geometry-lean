import InfoGeometry.Probability.AitchisonFinite
import InfoGeometry.Topology.FiniteGibbsFisherBridge
import InfoGeometry.Analysis.LogOddsSimplexGeometry

/-!
# Binary Aitchison geometry, centered moments, and entropy production

Instantiates the existing finite CLR owner on a positive binary distribution.
Its Euclidean squared distance is half the squared log-odds difference.
This is different from the Fisher metric and its probability-weighted moments.
The entropy production below is derived from the entropy derivative and a
specified Fisher-gradient field, not supplied as a nonnegativity assumption.
-/

noncomputable section
open scoped BigOperators
namespace InfoGeometry.Probability.BinaryAitchisonMoments

open InfoGeometry.Probability.AitchisonFinite
open InfoGeometry.Topology.FiniteGibbsFisherBridge
open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Analysis.LogOddsSimplexGeometry

def positiveBinary (p : Set.Ioo (0 : ℝ) 1) : PositiveSimplex 2 :=
  ⟨![p.val, 1 - p.val], by
    constructor
    · intro i
      fin_cases i
      · exact p.property.1
      · exact sub_pos.mpr p.property.2
    · simp⟩

theorem binary_clr (p : Set.Ioo (0 : ℝ) 1) :
    clr (positiveBinary p) (by decide) = ![logit p.val / 2, -logit p.val / 2] := by
  have hp0 := p.property.1.ne'
  have hq0 := (sub_pos.mpr p.property.2).ne'
  ext i
  fin_cases i <;>
    simp [clr, logMean, positiveBinary, logit, Real.log_div hp0 hq0, Fin.sum_univ_two] <;>
    ring

/-- Exact binary distance in the repository's CLR Euclidean convention. -/
theorem binary_clr_distance_sq (p q : Set.Ioo (0 : ℝ) 1) :
    (∑ i : Fin 2, (clr (positiveBinary p) (by decide) i -
      clr (positiveBinary q) (by decide) i) ^ 2) =
      (logit p.val - logit q.val) ^ 2 / 2 := by
  rw [binary_clr, binary_clr]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The Euclidean speed in the binary CLR chart is one half of the log-odds
metric times squared probability velocity. Both derivatives are genuine. -/
theorem binary_clr_speed (p : ℝ → ℝ) (u t : ℝ)
    (hd : HasDerivAt p u t) (hp : p t ∈ Set.Ioo (0 : ℝ) 1) :
    (deriv (fun s => logit (p s) / 2) t) ^ 2 +
      (deriv (fun s => -logit (p s) / 2) t) ^ 2 =
      InfoGeometry.Probability.SimplexQuadraticResponse.logOddsMetric (p t) * u ^ 2 / 2 := by
  have h := (hasDerivAt_logit hp).comp t hd
  have hplus : HasDerivAt (fun s => logit (p s) / 2)
      ((1 / (p t * (1 - p t)) * u) / 2) t := h.div_const 2
  have hminus : HasDerivAt (fun s => -logit (p s) / 2)
      (-(1 / (p t * (1 - p t)) * u) / 2) t := h.neg.div_const 2
  rw [hplus.deriv, hminus.deriv]
  unfold InfoGeometry.Probability.SimplexQuadraticResponse.logOddsMetric
  have hp0 := hp.1.ne'
  have hq0 := (sub_pos.mpr hp.2).ne'
  field_simp
  ring

/-- Centered moment of the binary observable taking values one and zero. -/
def centeredMoment (p : ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin 2, (![p, 1 - p] : Fin 2 → ℝ) i *
    ((![1, 0] : Fin 2 → ℝ) i - finiteGibbsMean ![p, 1 - p] ![1, 0]) ^ k

theorem centeredMoment_two (p : ℝ) : centeredMoment p 2 = p * (1 - p) := by
  simp [centeredMoment, finiteGibbsMean, Fin.sum_univ_two]
  ring

theorem centeredMoment_three (p : ℝ) :
    centeredMoment p 3 = p * (1 - p) * (1 - 2 * p) := by
  simp [centeredMoment, finiteGibbsMean, Fin.sum_univ_two]
  ring

/-- The fourth cumulant is not the fourth centered moment alone. -/
theorem fourth_cumulant (p : ℝ) :
    centeredMoment p 4 - 3 * centeredMoment p 2 ^ 2 =
      p * (1 - p) * (1 - 6 * p * (1 - p)) := by
  simp [centeredMoment, finiteGibbsMean, Fin.sum_univ_two]
  ring

/-- Differentiating the Fisher variance in natural coordinates gives the third
centered moment, as expected for the Bernoulli exponential family. -/
theorem hasDerivAt_fisherExp (θ : ℝ) :
    HasDerivAt fisherExp (centeredMoment (logistic θ) 3) θ := by
  have hd := hasDerivAt_logistic θ
  convert hd.mul ((hasDerivAt_const θ (1 : ℝ)).sub hd) using 1
  rw [centeredMoment_three]
  dsimp
  ring

/-- On the finite binary carrier, the existing Massieu Hessian is its actual
probability-weighted centered second moment. -/
theorem massieu_second_derivative (θ : ℝ) :
    deriv (deriv massieu) θ = centeredMoment (logistic θ) 2 := by
  rw [deriv2_massieu, centeredMoment_two]
  rfl

/-- A specified Fisher-gradient entropy field (a mathematical model choice). -/
def entropyGradientField (p : ℝ) : ℝ := -p * (1 - p) * logit p

/-- The Shannon entropy derivative paired with that field is a positive square. -/
theorem entropy_gradient_production {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun q => -negativeEntropy q) p * entropyGradientField p =
      p * (1 - p) * logit p ^ 2 := by
  change deriv (-negativeEntropy) p * _ = _
  rw [(hasDerivAt_negativeEntropy hp).neg.deriv]
  unfold entropyGradientField
  ring

theorem entropy_gradient_production_nonneg {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ deriv (fun q => -negativeEntropy q) p * entropyGradientField p := by
  rw [entropy_gradient_production hp]
  exact mul_nonneg (mul_pos hp.1 (sub_pos.mpr hp.2)).le (sq_nonneg _)

end InfoGeometry.Probability.BinaryAitchisonMoments
