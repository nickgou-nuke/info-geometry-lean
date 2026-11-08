import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

namespace InfoGeometry

/-- Scalar partition function for the two-level spinor model with spectrum ±r. -/
def partitionQ (r β : ℝ) : ℝ := Real.exp (β * r) + Real.exp (-(β * r))

/-- Entropy potential S = log Q. -/
def entropyPotential (r β : ℝ) : ℝ := Real.log (partitionQ r β)

/-- β-response written in elementary exponential form. -/
def betaResponse (r β : ℝ) : ℝ :=
  r * (Real.exp (β * r) - Real.exp (-(β * r))) / partitionQ r β

theorem partitionQ_pos (r β : ℝ) : 0 < partitionQ r β := by
  have h1 : 0 < Real.exp (β * r) := Real.exp_pos (β * r)
  have h2 : 0 < Real.exp (-(β * r)) := Real.exp_pos (-(β * r))
  simpa [partitionQ] using add_pos h1 h2

theorem entropyPotential_wellDefined (r β : ℝ) :
    entropyPotential r β = Real.log (Real.exp (β * r) + Real.exp (-(β * r))) := by
  rfl

theorem betaResponse_def (r β : ℝ) :
    betaResponse r β =
      r * (Real.exp (β * r) - Real.exp (-(β * r))) /
        (Real.exp (β * r) + Real.exp (-(β * r))) := by
  rfl

end InfoGeometry
