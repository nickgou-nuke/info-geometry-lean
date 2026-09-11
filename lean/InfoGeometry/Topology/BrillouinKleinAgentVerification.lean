import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.BrillouinKleinBottleManifold

open Matrix
open InfoGeometry.Topology.BrillouinKleinBottleManifold

theorem Tx_Ty_trace : Matrix.trace Tx = 0 ∧ Matrix.trace Ty = 0 := by
  constructor
  · simp [Tx, Matrix.trace, Matrix.diag]
  · simp [Ty, Matrix.trace, Matrix.diag]
