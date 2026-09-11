import InfoGeometry.Analysis.LieExponentialTraceDeterminant
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Analysis.MongeAmpereLieCongruence

open InfoGeometry.Analysis.LieExponentialTraceDeterminant

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Congruence orbit of a finite Hessian matrix under a constant Lie flow. -/
def mongeAmpereCongruencePath (A H₀ : Matrix n n ℝ) :
    ℝ → Matrix n n ℝ :=
  fun t =>
    (InfoGeometry.Analysis.LieExponentialTraceDeterminant.lieExponentialPath A t).transpose *
      H₀ * InfoGeometry.Analysis.LieExponentialTraceDeterminant.lieExponentialPath A t

/-- The determinant (Monge--Ampère density) along a congruence orbit. -/
def mongeAmpereDensityPath (A H₀ : Matrix n n ℝ) : ℝ → ℝ :=
  fun t => (mongeAmpereCongruencePath A H₀ t).det

theorem mongeAmpereDensity_lieCongruence
    (A H₀ : Matrix n n ℝ) (t : ℝ) :
    mongeAmpereDensityPath A H₀ t =
      Real.exp (2 * t * Matrix.trace A) * H₀.det := by
  unfold mongeAmpereDensityPath mongeAmpereCongruencePath
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_lieExponentialPath]
  calc
    Real.exp (t * Matrix.trace A) * H₀.det *
          Real.exp (t * Matrix.trace A) =
        Real.exp (t * Matrix.trace A) *
          Real.exp (t * Matrix.trace A) * H₀.det := by ring
    _ = Real.exp (t * Matrix.trace A + t * Matrix.trace A) * H₀.det := by
      rw [← Real.exp_add]
    _ = Real.exp (2 * t * Matrix.trace A) * H₀.det := by ring_nf

/-! The normalized half-log density is the same trace potential as the Gram
compression owner.  Positivity of `H₀.det` keeps this statement on the
nonsingular finite-density sector. -/
def relativeMongeAmpereCompression (A H₀ : Matrix n n ℝ) : ℝ → ℝ :=
  fun t => -(1 / 2 : ℝ) *
    Real.log (mongeAmpereDensityPath A H₀ t / H₀.det)

theorem relativeMongeAmpereCompression_eq_trace
    (A H₀ : Matrix n n ℝ) (hH₀ : 0 < H₀.det) :
    relativeMongeAmpereCompression A H₀ =
      fun t => -(t * Matrix.trace A) := by
  funext t
  unfold relativeMongeAmpereCompression
  rw [mongeAmpereDensity_lieCongruence]
  have hdet : H₀.det ≠ 0 := ne_of_gt hH₀
  have hratio :
      Real.exp (2 * t * Matrix.trace A) * H₀.det / H₀.det =
        Real.exp (2 * t * Matrix.trace A) := by
    field_simp
  rw [hratio, Real.log_exp]
  ring

theorem lieExponential_volume_preserving_of_trace_zero
    (A : Matrix n n ℝ) (hA : Matrix.trace A = 0) :
    ∀ t,
      (InfoGeometry.Analysis.LieExponentialTraceDeterminant.lieExponentialPath A t).det = 1 := by
  intro t
  rw [det_lieExponentialPath, hA, mul_zero, Real.exp_zero]

end InfoGeometry.Analysis.MongeAmpereLieCongruence
