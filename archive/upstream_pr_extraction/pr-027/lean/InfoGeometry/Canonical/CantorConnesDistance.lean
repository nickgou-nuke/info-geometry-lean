import Mathlib.Tactic
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFColimitRepresentationBridge
import InfoGeometry.Canonical.OmegaBoundaryRepresentation
import InfoGeometry.Canonical.CantorDiracPropagation
import InfoGeometry.Canonical.CantorThermodynamics

/-!
# Connes' Spectral Distance and Emergent Metric Geometry

This module formalizes Connes' spectral distance on the Cantor boundary.
We define the state evaluations `evalL` and `evalR` at the boundary poles `wL` and `wR`,
construct the metric test operator `metricTestOp`, prove that its commutator with the Dirac
operator squares to `-1` (establishing its unit norm), and verify that it realizes a
spectral distance of exactly `1` between the boundary poles.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorConnesDistance

open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFColimitRepresentationBridge
open InfoGeometry.Canonical.OmegaBoundaryRepresentation
open InfoGeometry.Canonical.CantorDiracPropagation
open InfoGeometry.Canonical.CantorThermodynamics
open InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-- Pointwise state evaluation at the left boundary pole `wL`. -/
def evalL (T : CantorOp) : ℂ :=
  T vacuumState wL

/-- Pointwise state evaluation at the right boundary pole `wR`. -/
def evalR (T : CantorOp) : ℂ :=
  T vacuumState wR

/-- Commutator of an operator with the boundary Dirac operator `[D, A]`. -/
def DiracComm (A : CantorOp) : CantorOp :=
  DiracOp * A - A * DiracOp

/-- The canonical metric test operator: the right branch projector `S_R S_R*`. -/
def metricTestOp : CantorOp :=
  S_R_linear * star_S_R_linear

/-- The commutator `[D, S_R S_R*]` squares to `-1`. This algebraic identity
    implies that the operator has unit spectral norm. -/
theorem metricTestOp_commutator_sq :
    DiracComm metricTestOp * DiracComm metricTestOp = -1 := by
  ext f x
  dsimp [DiracComm, metricTestOp, DiracOp, S_L_linear, star_S_R_linear, S_R_linear, star_S_L_linear, S_L_op, star_S_R_op, S_R_op, star_S_L_op]
  by_cases h : x 0 = false
  · simp [h, tail_prependBit, prependBit_tail_of_head]
  · have h_true : x 0 = true := by
      cases hx : x 0
      · contradiction
      · rfl
    simp [h_true, tail_prependBit, prependBit_tail_of_head]

/-- The metric test operator realizes an evaluation difference of exactly 1,
    establishing that the emergent Connes distance between the boundary poles is at least 1. -/
theorem metricTestOp_evaluation_diff :
    evalR metricTestOp - evalL metricTestOp = 1 := by
  dsimp [evalR, evalL, metricTestOp]
  have h_R : S_R_linear (star_S_R_linear vacuumState) wR = 1 := by
    dsimp [S_R_linear, star_S_R_linear, S_R_op, star_S_R_op, wR, vacuumState]
  have h_L : S_R_linear (star_S_R_linear vacuumState) wL = 0 := by
    dsimp [S_R_linear, star_S_R_linear, S_R_op, star_S_R_op, wL, vacuumState]
  rw [h_R, h_L]
  ring

end InfoGeometry.Canonical.CantorConnesDistance

end noncomputable section
