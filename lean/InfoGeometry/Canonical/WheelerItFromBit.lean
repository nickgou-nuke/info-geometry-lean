import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Physics.EmergentSpacetimeBilinear

namespace InfoGeometry.Canonical.WheelerItFromBit

open InfoGeometry.Physics.EmergentSpacetimeBilinear

abbrev Spinor32 := InfoGeometry.Physics.EmergentSpacetimeBilinear.Spinor32
abbrev Mat32 := InfoGeometry.Physics.EmergentSpacetimeBilinear.Mat32

structure QuantumBit where
  P : Mat32
  is_idempotent : P * P = P

def itFromBitCoordinate (psi : Spinor32) (A : Mat32) : ℝ :=
  spacetimeCoordinate psi A

theorem it_vanishes_for_zero_state (A : Mat32) :
    itFromBitCoordinate 0 A = 0 := by
  have hdensity : kreinDensity 0 = 0 := by
    ext i j
    simp [kreinDensity, InfoGeometry.Clifford.Clifford55.ketBra,
      InfoGeometry.Physics.EmergentSpacetimeBilinear.kreinBra]
  simp [itFromBitCoordinate, spacetimeCoordinate, hdensity]

def emergentGravitationalMetric (rho : Mat32) (A B : Mat32) : ℝ :=
  Matrix.trace (rho * A * B) - Matrix.trace (rho * A) * Matrix.trace (rho * B)

theorem emergentGravitationalMetric_comm_symm
    (rho A B : Mat32) (h_comm : A * B = B * A) :
    emergentGravitationalMetric rho A B =
      emergentGravitationalMetric rho B A := by
  dsimp [emergentGravitationalMetric]
  have hAB : rho * A * B = rho * B * A := by
    calc
      rho * A * B = rho * (A * B) := mul_assoc rho A B
      _ = rho * (B * A) := by rw [h_comm]
      _ = rho * B * A := (mul_assoc rho B A).symm
  rw [hAB, mul_comm (Matrix.trace (rho * A))]

end InfoGeometry.Canonical.WheelerItFromBit
