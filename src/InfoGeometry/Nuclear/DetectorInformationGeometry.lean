import InfoGeometry.Nuclear.ApollonianBipolarField
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.QuadraticResponseSimplex
import InfoGeometry.Probability.BinaryAitchisonMoments
import InfoGeometry.Modular.FiniteSimplexModularTime
import InfoGeometry.Probability.DetectorEnsembleTransport

/-!
Connections between the existing detector coordinate, the Bernoulli variance,
and finite modular frequencies. An admissible loss fraction is explicit.
The spectral index and the acquisition index are different finite carriers.
No numerical nuclear-data evaluation or detector drawing is encoded here.
-/
noncomputable section
namespace InfoGeometry.Nuclear.DetectorInformationGeometry
open InfoGeometry.Nuclear.ApollonianBipolarField
open InfoGeometry.Probability.SimplexQuadraticResponse
open InfoGeometry.Probability.BinaryAitchisonMoments
open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Probability.FiniteLogTransport
open InfoGeometry.Probability.AitchisonFinite
open InfoGeometry.Modular.FiniteSimplexModularTime

/-- The geometric-coordinate response is the same center Bernoulli moment
used by the Massieu Hessian, when its loss fraction is in the open simplex. -/
theorem geometric_response_massieu (C K a d0 d : ℝ) (hC : C ≠ 0)
    (hp : K * (1 / (linearizer a d0 d)^2) / C ∈ Set.Ioo (0 : ℝ) 1) :
    K * response C K (1 / (linearizer a d0 d)^2) / C^2 =
      deriv (deriv massieu) (logit (K * (1 / (linearizer a d0 d)^2) / C)) := by
  rw [InfoGeometry.Analysis.QuadraticResponseSimplex.normalized_response C K _ hC,
    deriv2_massieu, fisherExp_logit hp]

/-- The loss state's actual matrix-unit phase is its log-odds frequency. -/
theorem loss_state_modular_phase (p : Set.Ioo (0 : ℝ) 1) (t : ℝ) :
    phase (positiveBinary p) t 0 1 =
      Complex.exp (Complex.I * (t : ℂ) * (logit p.val : ℂ)) := by
  rw [phase_from_clr (positiveBinary p) (by decide), binary_clr]
  have h : logit p.val / 2 - -logit p.val / 2 = logit p.val := by ring
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h]

/-- The ensemble scale composition and the center shift have the same
modular frequency differences, on the distance-index carrier. -/
theorem ensemble_modular_frequency {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (t : ℝ) (j k : Fin m) :
    phase (softmax m (center s) hm) t j k =
      Complex.exp (Complex.I * (t : ℂ) * ((s j - s k : ℝ) : ℂ)) := by
  rw [phase_from_clr _ hm, center_eq_clr hm]
  have h : center s j - center s k = s j - s k := by
    unfold center
    ring
  rw [h]

end InfoGeometry.Nuclear.DetectorInformationGeometry
