import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Projective.FiveGradedCentralizer
import InfoGeometry.Projective.NonIsoConf3RankIngestion

/-!
# Black Hole Unitarity Bridge

Finite algebraic interface for the black-hole unitarity lane.

This module does not prove the physical black-hole information theorem. It
records the finite premises currently available in the projective layer:

1. a rank-bound readback from explicit Betti data;
2. a real-matrix unitarity/isometry interface for the Möbius parity operator;
3. trace-zero readback of the stored Gromov-Witten scalar.
-/

namespace InfoGeometry.Projective.Unitarity

open InfoGeometry.Projective.Closure
open InfoGeometry.Projective.NonIsoConf3RankIngestion

/-- S-matrix interface defined by the 5-graded Möbius parity inversion. -/
structure HorizonSMatrix (n : ℕ) where
  closure : FiveGradedMobiusClosure n
  
  /-- Real unitarity/isometry constraint: `Sᵀ * S = I`. -/
  unitarity : closure.moebiusParity.transpose * closure.moebiusParity = closure.I

/-- Rank-bound readback from a spin-tiled rank-32 premise. -/
theorem microstate_entropy_bounded 
    (cert : ExternalBettiData)
    (_hAmbient : HasConf3AmbientDimension cert)
    (_hConsistent : RankDataConsistent cert)
    (h_rank : cert.totalRank * InfoGeometry.Projective.PenroseSpinTiling.spinTilingMultiplicity = 32) :
    cert.totalRank * InfoGeometry.Projective.PenroseSpinTiling.spinTilingMultiplicity ≤ 32 := by
  rw [h_rank]

/--
The stored horizon S-matrix premise gives the real isometry equation.
-/
theorem modular_flow_isometry (n : ℕ) (S : HorizonSMatrix n) :
    S.closure.moebiusParity.transpose * S.closure.moebiusParity = S.closure.I := 
  S.unitarity

/--
Finite readback combining the S-matrix isometry premise with the trace-zero
Gromov-Witten readout.
-/
theorem information_preservation (n : ℕ) (S : HorizonSMatrix n)
    (h_traceless : Matrix.trace S.closure.moebiusParity = 0) :
    (S.closure.moebiusParity.transpose * S.closure.moebiusParity = S.closure.I) ∧ 
    (S.closure.gromovWittenIndex = 0) := by
  constructor
  · exact S.unitarity
  · rw [S.closure.gw_eq_trace, h_traceless]

end InfoGeometry.Projective.Unitarity
