import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.OperatorAlgebra

/-- Affine operator exponential families.
    Models exponential families over a non-commutative algebra A. -/
structure AffineOperatorExpFamily (A : Type*) [Ring A] [Algebra ℝ A] where
  base : A
  tangent : A → A
  logPartition : A → ℝ
  /-- state represents the trace or a specific state (like the KMS state) -/
  state : A → ℝ

/-- Fréchet metric (Operator covariance) -/
def frechetMetric {A : Type*} [Ring A] [Algebra ℝ A]
    (F : AffineOperatorExpFamily A) (u v : A) : ℝ :=
  -- Tr[ ρ_θ (u - E[u]) (v - E[v]) ]
  -- Modeled bilinearly using the state.
  F.state (u * v) - (F.state u) * (F.state v)

/-- Fréchet cubic (Amari-Chentsov operator tensor) -/
def frechetCubic {A : Type*} [Ring A] [Algebra ℝ A]
    (F : AffineOperatorExpFamily A) (u v w : A) : ℝ :=
  F.state (u * v * w) - (F.state u) * (F.state (v * w)) - (F.state v) * (F.state (u * w)) - (F.state w) * (F.state (u * v)) + 2 * (F.state u) * (F.state v) * (F.state w)

end InfoGeometry.OperatorAlgebra
