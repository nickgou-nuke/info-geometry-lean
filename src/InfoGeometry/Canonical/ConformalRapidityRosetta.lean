/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Dynamics.RapiditySpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Dynamics.RindlerWedge
import InfoGeometry.Clifford.ConformalReflection55
import InfoGeometry.Clifford.DiscreteMoebiusGroup
import InfoGeometry.Clifford.MonodromyFlowAdapter
import InfoGeometry.Canonical.ConformalSL2GeneratorBridge
import Mathlib.Tactic.NoncommRing

/-!
# Rapidity, Rindler Flow, and Conformal Inversion

This owner proves compatibility statements between the finite real rapidity
model, its Rindler-coordinate realization, and the Clifford sandwich inversion.
The carriers remain the actual carriers of the source constructions: real
`2 × 2` matrices for rapidity, `Cl(5,5)` elements for inversion, and complex
numbers for the projective Möbius chart. These results do not identify those
carriers or assert a continuum/analytic limit.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConformalRapidityRosetta

open InfoGeometry.Dynamics.HyperbolicComponent
open InfoGeometry.Dynamics.RapiditySpace
open InfoGeometry.Dynamics.RindlerWedge
open InfoGeometry.Clifford.ConformalReflection55
open InfoGeometry.Clifford.DiscreteMoebiusGroup
open InfoGeometry.Clifford.MonodromyFlowAdapter
open InfoGeometry.Canonical.ConformalSL2GeneratorBridge

/-- Two successive real boost actions compose to the single summed-rapidity action. -/
theorem rindler_boost_composition (coords : RindlerCoordinates) (lam mu : ℝ) :
    componentAReal lam * (componentAReal mu * rindlerToMinkowski coords) =
      componentAReal (lam + mu) * rindlerToMinkowski coords := by
  rw [← Matrix.mul_assoc, rapidity_additive_composition]

/-- A boost followed by its inverse returns the original Rindler light-cone point. -/
theorem rindler_boost_round_trip (coords : RindlerCoordinates) (lam : ℝ) :
    componentAReal lam * (componentAReal (-lam) * rindlerToMinkowski coords) =
      rindlerToMinkowski coords := by
  rw [← Matrix.mul_assoc, rapidity_mul_neg, Matrix.one_mul]

/-- The Clifford origin/infinity sandwich is an involution on every algebra element. -/
theorem conformal_sandwich_involution (p : InfoGeometry.Clifford.ConformalLift55.ConformalNullPair)
    (x : InfoGeometry.Clifford.ConformalLift55.Cl55) :
    J p * (J p * x * J p) * J p = x := by
  have hJ : J p * J p = -1 := by
    simpa [pow_two] using J_sq p
  calc
    J p * (J p * x * J p) * J p = (J p * J p) * x * (J p * J p) := by
      noncomm_ring
    _ = (-1) * x * (-1) := by rw [hJ]
    _ = x := by noncomm_ring

/-- The modular Möbius shear translates by the sum of two successive parameters. -/
theorem moebius_shear_composition (s t z : ℂ) :
    moebiusAction (lcftParabolicFlowStep s * lcftParabolicFlowStep t) z = z + (s + t) := by
  rw [lcftParabolicFlow_composition]
  exact moebius_monodromy_flow_action (s + t) z

/-- The square of the dilation adjoint action fixes each nilpotent root generator. -/
theorem conformal_dilation_adjoint_square_on_roots :
    (D * (D * P - P * D) - (D * P - P * D) * D = P) ∧
      (D * (D * K - K * D) - (D * K - K * D) * D = K) := by
  constructor
  · calc
      D * (D * P - P * D) - (D * P - P * D) * D = D * P - P * D := by
        rw [comm_D_P]
        exact comm_D_P
      _ = P := comm_D_P
  · have hK := comm_D_K
    rw [hK]
    calc
      D * (-K) - (-K) * D = -(D * K - K * D) := by noncomm_ring
      _ = K := by rw [hK]; simp

end InfoGeometry.Canonical.ConformalRapidityRosetta
