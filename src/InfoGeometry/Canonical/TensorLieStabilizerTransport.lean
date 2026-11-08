/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FrechetPeirceLieStabilizer

/-! # Stabilizer membership across the actual tensor tower

Faithful bonding maps and the faithful colimit inclusion both preserve and
reflect stabilization for represented inner derivations. The colimit
stabilizer is algebraic; no colimit topology is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorLieStabilizerTransport

open scoped Matrix Matrix.Norms.Operator
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Canonical.TensorStageFrechetConnection
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.OperatorFrechetDerivationJet.FrechetBridge
open InfoGeometry.Canonical.FrechetPeirceLieStabilizer

/-- The algebraic Lie stabilizer of a colimit cut. -/
def limitCutStabilizer (P : Limit) :
    LieSubalgebra ℝ (InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ Limit) where
  carrier := {D | D.1 P = 0}
  zero_mem' := by
    change (0 : Module.End ℝ Limit) P = 0
    simp
  add_mem' := by
    intro D E hD hE
    change D.1 P = 0 at hD
    change E.1 P = 0 at hE
    change D.1 P + E.1 P = 0
    rw [hD, hE, add_zero]
  smul_mem' := by
    intro r D hD
    change D.1 P = 0 at hD
    change r • D.1 P = 0
    rw [hD, smul_zero]
  lie_mem' := by
    intro D E hD hE
    change D.1 P = 0 at hD
    change E.1 P = 0 at hE
    change D.1 (E.1 P) - E.1 (D.1 P) = 0
    simp only [hD, hE, map_zero, sub_self]

/-- An iterated faithful bonding map preserves and reflects membership of
represented inner derivations in the cut stabilizers. -/
theorem bondMap_inner_mem_iff {n m : ℕ} (hnm : n ≤ m) (P H : Stage n) :
    toRealDerivation (stageInnerFrechet m (bondMap stageBond n m hnm H)) ∈
        cutStabilizer (bondMap stageBond n m hnm P) ↔
    toRealDerivation (stageInnerFrechet n H) ∈ cutStabilizer P := by
  change (bondMap stageBond n m hnm H * bondMap stageBond n m hnm P -
    bondMap stageBond n m hnm P * bondMap stageBond n m hnm H = 0) ↔
      H * P - P * H = 0
  rw [← map_mul, ← map_mul, ← map_sub]
  constructor
  · intro h
    apply bondMap_injective stageBond (fun k => matStageEmbed_injective k) n m hnm
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- The faithful canonical stage map preserves and reflects stabilization
for the corresponding inner direction on the algebraic colimit. -/
theorem ofStage_inner_mem_iff (n : ℕ) (P H : Stage n) :
    limitInnerLieHom (ofStage n H) ∈ limitCutStabilizer (ofStage n P) ↔
      toRealDerivation (stageInnerFrechet n H) ∈ cutStabilizer P := by
  change (ofStage n H * ofStage n P - ofStage n P * ofStage n H = 0) ↔
    H * P - P * H = 0
  rw [← map_mul, ← map_mul, ← map_sub, ofStage_eq_zero_iff]

open InfoGeometry.Canonical.FrechetPeirceStabilizerWitness
open InfoGeometry.Examples.RealMatrixModeWitness

/-- The original dense mode remains outside the colimit stabilizer, while
the cut's own inner derivation remains inside it. -/
theorem denseMode_limit_stabilizer_separation :
    limitInnerLieHom (ofStage 2 p) ∈ limitCutStabilizer (ofStage 2 p) ∧
      limitInnerLieHom (ofStage 2 x) ∉ limitCutStabilizer (ofStage 2 p) := by
  constructor
  · exact (ofStage_inner_mem_iff 2 p p).2 cut_inner_stabilizes_and_acts_nontrivially.1
  · intro h
    exact denseMode_not_mem_cutStabilizer ((ofStage_inner_mem_iff 2 p x).1 h)

/-- The stabilizing colimit inner derivation acts nontrivially on the
faithfully embedded dense mode. -/
theorem denseMode_limit_stabilizer_action_ne_zero :
    (limitInnerLieHom (ofStage 2 p) : Module.End ℝ Limit) (ofStage 2 x) ≠ 0 := by
  rw [limitInnerLieHom_apply, ← map_mul, ← map_mul, ← map_sub,
    p_mul_x, x_mul_p, sub_zero]
  exact fun h => denseMode_ne_zero ((ofStage_eq_zero_iff 2 x).mp h)

end InfoGeometry.Canonical.TensorLieStabilizerTransport

end
