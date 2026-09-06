import Mathlib

/-!
# Finite weighted-metric obstruction for an off-diagonal connection

This file is a small explicit `2 × 2` real-matrix calculation.  It does not
construct a manifold connection or identify this matrix model with a global
Krein or spin-connection structure.  It records only the stated obstruction:
the chosen off-diagonal matrix commutes with the chosen diagonal weight exactly
at zero chemical-potential parameter (when its off-diagonal coefficient is
nonzero).
-/

namespace InfoGeometry.Canonical

open Matrix

noncomputable section

abbrev RealBlock2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The off-diagonal connection used by the finite model. -/
def spinConnection (u : ℝ) : RealBlock2 :=
  !![0, u; u, 0]

/-- The positive diagonal weight associated with the parameter `mu`. -/
def kreinMetric (mu : ℝ) : RealBlock2 :=
  !![Real.exp (-2 * mu), 0; 0, Real.exp (2 * mu)]

/-- The commutator obstruction `[ω, η_mu]`. -/
def connectionMetricObstruction (u mu : ℝ) : RealBlock2 :=
  spinConnection u * kreinMetric mu - kreinMetric mu * spinConnection u

@[simp] theorem connection_obstruction_explicit (u mu : ℝ) :
    connectionMetricObstruction u mu =
      !![0, u * (Real.exp (2 * mu) - Real.exp (-2 * mu));
         u * (Real.exp (-2 * mu) - Real.exp (2 * mu)), 0] := by
  dsimp [connectionMetricObstruction, spinConnection, kreinMetric]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply] <;> ring

theorem connection_compatible_of_mu_zero (u : ℝ) :
    connectionMetricObstruction u 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connection_obstruction_explicit]

theorem compatibility_iff_mu_zero (u mu : ℝ) (hu : u ≠ 0) :
    connectionMetricObstruction u mu = 0 ↔ mu = 0 := by
  constructor
  · intro h
    have hcoord := congrArg (fun M : RealBlock2 => M 0 1) h
    rw [connection_obstruction_explicit] at hcoord
    simp only [Matrix.zero_apply] at hcoord
    have hdiff : Real.exp (2 * mu) - Real.exp (-2 * mu) = 0 := by
      rcases mul_eq_zero.mp hcoord with hu0 | hdiff
      · exact False.elim (hu hu0)
      · exact hdiff
    have hexp : Real.exp (2 * mu) = Real.exp (-2 * mu) := by
      linarith
    have harg : 2 * mu = -2 * mu := Real.exp_injective hexp
    linarith
  · intro hmu
    subst hmu
    exact connection_compatible_of_mu_zero u

end

end InfoGeometry.Canonical
