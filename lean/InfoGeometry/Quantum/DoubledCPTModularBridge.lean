import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge

namespace InfoGeometry.Quantum.DoubledCPTModularBridge

open InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge

/-- The structural algebraic origin of CPT symmetry and modular involution:
The determinant of the collision matrix is 1, which strictly forces the
expanding (unstable) and contracting (stable) Lyapunov roots to be perfect
inverses. This constitutes the physical "sheet" and "commutant sheet" balance. -/
theorem lambdaU_mul_lambdaS (u : ℝ) (hu : 0 ≤ u * (u + 4)) :
    lambdaU u * lambdaS u = 1 := by
  dsimp [lambdaU, lambdaS]
  have hsq : (Real.sqrt (u * (u + 4))) ^ 2 = u * (u + 4) := Real.sq_sqrt hu
  nlinarith

/-- The logarithmic form of the CPT balance establishes exactly zero net Lyapunov
drift. The thermodynamic entropy produced along the unstable direction is exactly
mirrored by the entropy consumed in the stable direction. -/
theorem net_lyapunov_drift_zero (u : ℝ) (hu : 0 ≤ u * (u + 4)) :
    Real.log |lambdaU u| + Real.log |lambdaS u| = 0 := by
  have h1 : lambdaU u * lambdaS u = 1 := lambdaU_mul_lambdaS u hu
  have h_ne_U : lambdaU u ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    linarith
  have h_ne_S : lambdaS u ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    linarith
  rw [← Real.log_mul (abs_ne_zero.mpr h_ne_U) (abs_ne_zero.mpr h_ne_S)]
  rw [← abs_mul, h1, abs_one, Real.log_one]

end InfoGeometry.Quantum.DoubledCPTModularBridge
