import InfoGeometry.KL.Finite
import InfoGeometry.KL.Measure

namespace InfoGeometry.KL

open scoped BigOperators

/-- Rényi moment functional built from the empirical/model density ratio. -/
noncomputable def Phi
    {α : Type} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  ∑ x, empiricalDistribution N_func x * Real.rpow (densityRatio N_func Q x) τ

end InfoGeometry.KL
