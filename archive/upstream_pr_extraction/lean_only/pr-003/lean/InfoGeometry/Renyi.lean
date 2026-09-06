
import InfoGeometry.KL

namespace InfoGeometry

/-- Rényi section: D_τ = Φ(τ)/(τ-1). -/
noncomputable def RenyiD {α : Type} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  KL.Phi N_func Q τ / (τ - 1)

end InfoGeometry
