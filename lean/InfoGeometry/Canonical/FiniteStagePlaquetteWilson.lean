/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Topology.WilsonLoopThermodynamics
import InfoGeometry.Topology.BostConnesWilsonLoop
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Finite-stage plaquette and Wilson readouts (Phase 5 first slice)

Instantiates the generic `[Ring Op]` Wilson-loop / causal-flow lens at the
finite-stage carrier `Stage n := InfoGeometry.Clifford.Cl11TensorTower.MatStage n
= InfoGeometry.Clifford.TowerMatrix.Mat n`, the real matrix algebra indexed by
the recursive binary tensor index.

The flow is built from an idempotent cut corner `P` with complementary corner
`1 - P`; detailed balance is *derived*, not assumed: both cross-products
vanish by the corner algebra, so the entropy-production commutator is zero
and the owned detailed-balance engine annihilates the curvature readout.

All statements are finite ring-and-word algebra.  No analytic thermodynamic
statement, continuum limit, or KMS assertion is made anywhere.
-/

namespace InfoGeometry.Canonical.FiniteStagePlaquetteWilson

open InfoGeometry.Topology.ThermodynamicGauge
open InfoGeometry.Topology.WilsonLoopThermodynamics
open InfoGeometry.Topology.BostConnesWilsonLoop
open InfoGeometry.Clifford.Cl11TensorTowerLimit

variable {n : ℕ}

/-- The staged cut-corner flow: the forward bond is the cut corner `P`, the
backward bond is the complementary corner `1 - P`, and the thermodynamic
markers `Q`, `d_ln_Q` are carried along untouched. -/
def cutFlow (P Q d : Stage n) : CausalNonequilibriumFlow (Stage n) :=
  ⟨Q, d, P, 1 - P⟩

variable (P : Stage n)

/-- Corner algebra of the idempotent cut: both cross-products vanish. -/
theorem cutProducts (hP : P * P = P) :
    P * (1 - P) = 0 ∧ (1 - P) * P = 0 := by
  refine ⟨?_, ?_⟩
  · rw [mul_sub, mul_one, hP, sub_self]
  · rw [sub_mul, one_mul, hP, sub_self]

/-- The staged cut-corner flow has vanishing entropy production: the
commutator is `0 - 0` because both cross-products vanish on the corner. -/
theorem cutFlow_entropy_production_zero (Q d : Stage n) (hP : P * P = P) :
    entropy_production (cutFlow P Q d) = 0 := by
  have ⟨h1, h2⟩ := cutProducts P hP
  show (cutFlow P Q d).P_forward * (cutFlow P Q d).P_backward -
      (cutFlow P Q d).P_backward * (cutFlow P Q d).P_forward = 0
  simp only [cutFlow]
  rw [h1, h2]
  simp

/-- The staged cut-corner flow satisfies the detailed-balance commutation,
discharged from the vanishing entropy production through the owned
characteristic. -/
theorem cutFlow_detailed_balance (Q d : Stage n) (hP : P * P = P) :
    (cutFlow P Q d).P_forward * (cutFlow P Q d).P_backward
      = (cutFlow P Q d).P_backward * (cutFlow P Q d).P_forward :=
  (entropy_production_eq_zero_iff_detailed_balance (cutFlow P Q d)).mp
    (cutFlow_entropy_production_zero P Q d hP)

/-- The flow-transported two-bond plaquette holonomy on the staged cut
corner, in explicit corner form:
`(1 + P·s₁·(1-P)) · (1 + P·s₂·(1-P))`. -/
theorem cutFlow_wilson_two_bond (Q d : Stage n) (hP : P * P = P)
    (s₁ s₂ : Stage n) :
    finite_flow_wilson_loop (cutFlow P Q d) [s₁, s₂]
      = (1 + P * s₁ * (1 - P)) * (1 + P * s₂ * (1 - P)) := by
  rw [show [s₁, s₂] = [s₁] ++ [s₂] by rfl,
    finite_flow_wilson_loop_append_singleton (cutFlow P Q d) [s₁] s₂,
    finite_flow_wilson_loop_singleton (cutFlow P Q d) s₁]
  simp [flowed_connection_step, cutFlow]

/-- The staged curvature readout collapses: the detailed-balance corner data
feeds the owned vanishing engine at the finite-stage carrier, so the readout
of the cut-corner flow is zero. -/
theorem cutFlow_curvature_readout_zero (τ : Stage n →ₗ[ℝ] ℝ)
    (Q d : Stage n) (hP : P * P = P) :
    curvatureReadout (cutFlow P Q d) τ = 0 :=
  curvatureReadout_eq_zero_of_detailed_balance (cutFlow P Q d) τ
    (cutFlow_entropy_production_zero P Q d hP)

end InfoGeometry.Canonical.FiniteStagePlaquetteWilson
