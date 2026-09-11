import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.NormNum
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Canonical

/-- Linearized velocity field (Jacobian-level) on a real Hilbert carrier. -/
@[rep_depth krein]
abbrev VelocityField
    (E : Type _)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : Type _ :=
  E →L[ℝ] E

/--
  Core abstraction for fluid dynamics operators.
  Provides a unified interface for classical Navier‑Stokes and quantum Madelung systems.
-/
class FluidOperator (σ : Type _) [NormedAddCommGroup σ] [InnerProductSpace ℝ σ] [CompleteSpace σ] where
  /-- Divergence operator -/ divergence : σ →L[ℝ] σ
  /-- Gradient operator -/ gradient : σ →L[ℝ] σ
  /-- Laplacian operator -/ laplacian : σ →L[ℝ] σ
  /-- Time evolution map (parameter β) -/ timeEvolution : ℝ → σ → σ

end InfoGeometry.Canonical
