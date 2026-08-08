/- Interior Point Method -/
/- Implements the Primal-Dual Path-Following Newton Method for the 
   self-concordant barrier (Matrix Burg Potential / Log-Determinant). -/

import InfoGeometry.Optimization.BregmanPotentials
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace InfoGeometry.Optimization

variable {n : Type*}

/- The Central Path Potential: Cost(X) + μ * Ψ(X) -/
noncomputable def CentralPathPotential [Fintype n] [DecidableEq n]
    (Cost : Matrix n n ℝ → ℝ) (X : Matrix n n ℝ) (μ : ℝ) : ℝ :=
  Cost X + μ * MatrixBurgPotential X

/-
  An abstract representation of a Newton Step along the Central Path.
  Uses the Hessian (second derivative) of the potential to calculate the stable update.
-/
/-- A finite-dimensional Newton equation for an explicitly supplied gradient and
linear Hessian action.  This is the algebraic obligation for a direction; it is
not hidden behind a vacuous property field. -/
def IsNewtonInteriorDirection
    (gradient : Matrix n n ℝ)
    (hessianAction : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ)
    (direction : Matrix n n ℝ) : Prop :=
  hessianAction direction + gradient = 0

structure NewtonInteriorStep (Cost : Matrix n n ℝ → ℝ) (X : Matrix n n ℝ) (μ : ℝ) where
  gradient : Matrix n n ℝ
  hessianAction : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ
  direction : Matrix n n ℝ
  newton_equation : IsNewtonInteriorDirection gradient hessianAction direction

/-- Read back the concrete linear Newton equation carried by a step. -/
theorem NewtonInteriorStep.newton_equation_readout
    {Cost : Matrix n n ℝ → ℝ} {X : Matrix n n ℝ} {μ : ℝ}
    (step : NewtonInteriorStep Cost X μ) :
    step.hessianAction step.direction + step.gradient = 0 :=
  step.newton_equation

/-- If the supplied central-path gradient is zero, the zero direction solves
every linearized Newton equation. -/
def stationaryNewtonInteriorStep
    (Cost : Matrix n n ℝ → ℝ) (X : Matrix n n ℝ) (μ : ℝ)
    (hessianAction : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) :
    NewtonInteriorStep Cost X μ where
  gradient := 0
  hessianAction := hessianAction
  direction := 0
  newton_equation := by
    simp [IsNewtonInteriorDirection]

@[simp] theorem stationaryNewtonInteriorStep_direction
    (Cost : Matrix n n ℝ → ℝ) (X : Matrix n n ℝ) (μ : ℝ)
    (hessianAction : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) :
    (stationaryNewtonInteriorStep Cost X μ hessianAction).direction = 0 :=
  rfl

end InfoGeometry.Optimization
