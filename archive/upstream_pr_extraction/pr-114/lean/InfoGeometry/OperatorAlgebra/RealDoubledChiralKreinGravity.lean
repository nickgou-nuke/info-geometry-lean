import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinDualConnection

/-!
# Finite Krein-metric gravity data

This is the algebraic core of the proposed doubled metric construction.  A
graph matrix `H` reconstructs the symmetric metric `H + Hᵀ`; a pair of dual
connection matrices satisfies the cross-sheet compatibility equation.  The
structure intentionally does not assert curvature, Einstein dynamics, or a
physical spacetime interpretation.
-/

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinGravity

open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinGraphSection
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinDualConnection

abbrev Index := Fin 4
abbrev Matrix4 := Matrix Index Index ℝ

structure KreinMetricGravityData where
  /-- Cross-sheet pairing matrix and a chosen inverse. -/
  eta : Matrix4
  etaInv : Matrix4
  eta_inverse : eta * etaInv = 1
  /-- Graph/gluing field selecting the physical section. -/
  H : Matrix4
  /-- Positive-sheet connection coefficients. -/
  omegaPlus : Matrix4

namespace KreinMetricGravityData

def metric (G : KreinMetricGravityData) : Matrix4 :=
  inducedMetric G.H

def omegaMinus (G : KreinMetricGravityData) : Matrix4 :=
  dualConnection G.eta G.etaInv G.omegaPlus

theorem metric_eq_symmetricPart (G : KreinMetricGravityData) :
    G.metric = G.H + G.H.transpose := by
  exact inducedMetric_eq_add_transpose G.H

theorem metric_symmetric (G : KreinMetricGravityData) :
    G.metric.transpose = G.metric := by
  exact inducedMetric_symmetric G.H

theorem connection_compatibility (G : KreinMetricGravityData) :
    G.omegaPlus.transpose * G.eta + G.eta * G.omegaMinus = 0 := by
  exact dualConnection_compatibility G.eta G.etaInv G.omegaPlus G.eta_inverse

end KreinMetricGravityData

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinGravity
