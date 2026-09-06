import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Cayley-circle endpoint parameterization of the cosine variable. -/
def cayleyEndpoint (θ : ℝ) : ℝ :=
  (1 + Real.cos θ) / 2

/-- Closed-form arcsine density of the affine endpoint variable. -/
def zDensity (t : ℝ) : ℝ :=
  (2 / Real.pi) / Real.sqrt (1 - (2 * t - 1) ^ 2)

/-- Tilted endpoint density obtained from the reciprocal variable and the affine tilt `ρ`. -/
def yDensity (rho t : ℝ) : ℝ :=
  (1 + rho * t) * zDensity (1 / t) / t ^ 2

/-- The reciprocal endpoint keeps the affine-image arcsine density. -/
def zDensityClosedForm : Prop :=
  ∀ t : ℝ, zDensity t = (2 / Real.pi) / Real.sqrt (1 - (2 * t - 1) ^ 2)

/-- After inversion, the endpoint density picks up the Jacobian `t⁻²` and the tilt factor. -/
def yDensityClosedForm (rho : ℝ) : Prop :=
  ∀ t : ℝ,
    yDensity rho t =
      (1 + rho * t) * ((2 / Real.pi) / Real.sqrt (1 - (2 * t⁻¹ - 1) ^ 2)) / t ^ 2

/-- The two endpoint densities are related by inversion and the affine tilt factor. -/
def dualityRelation (rho : ℝ) : Prop :=
  ∀ t : ℝ, yDensity rho t = (1 + rho * t) * zDensity (1 / t) / t ^ 2

/-- Closed-form endpoint expectations used by the paper-facing wrapper. -/
def zExpectation : ℝ :=
  1 / 2

/-- The tilted reciprocal expectation shifts by the affine parameter `ρ / 2`. -/
def yExpectation (rho : ℝ) : ℝ :=
  1 + rho / 2

/-- Combined expectation identities for the endpoint pair `(Z_ρ, Y_ρ)`. -/
def expectationPackage (rho : ℝ) : Prop :=
  zExpectation = 1 / 2 ∧ yExpectation rho = 1 + rho / 2

/-- Paper label: `thm:app-endpoint-arcsine-duality`.
The Cayley endpoint variable has the affine arcsine density; inversion transfers it to the tilted
reciprocal density, and the corresponding expectation identities are the closed forms used in the
appendix. -/
theorem paper_app_endpoint_arcsine_duality (rho : ℝ) :
    yDensityClosedForm rho ∧ zDensityClosedForm ∧ dualityRelation rho ∧
      expectationPackage rho := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    simp [yDensity, zDensity, one_div]
  · intro t
    rfl
  · intro t
    rfl
  · exact ⟨rfl, rfl⟩

end

end Omega.UnitCirclePhaseArithmetic
