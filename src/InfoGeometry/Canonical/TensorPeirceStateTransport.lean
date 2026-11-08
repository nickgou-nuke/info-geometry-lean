/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorPeirceDensityWitness
import InfoGeometry.Canonical.TensorFrechetPeirceGrading

/-! # Positive Peirce pinching along the finite tensor tower

The actual finite matrix pinching preserves positive semidefiniteness and
normalized trace. Its output is compatible with every tower bonding map.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorPeirceStateTransport

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Canonical.TensorPeirceTraceLoss
open InfoGeometry.Canonical.TensorPeirceDensityWitness
open InfoGeometry.Canonical.TensorFrechetPeirceGrading
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Examples.RealMatrixModeWitness

/-- Pinching by a self-adjoint matrix preserves positive semidefiniteness. -/
theorem stage_pinching_posSemidef (n : ℕ) (P X : Stage n)
    (hPs : star P = P) (hX : X.PosSemidef) : (evenGrade P X).PosSemidef := by
  unfold evenGrade
  have h₁ := hX.mul_mul_conjTranspose_same P
  have h₂ := hX.mul_mul_conjTranspose_same (1 - P)
  change (P * X * star P).PosSemidef at h₁
  change ((1 - P) * X * star (1 - P)).PosSemidef at h₂
  rw [hPs] at h₁
  rw [star_sub, star_one, hPs] at h₂
  exact h₁.add h₂

/-- The normalized finite-stage trace is preserved by idempotent pinching. -/
theorem stage_pinching_normalizedTrace (n : ℕ) (P X : Stage n)
    (hP : P * P = P) : normalizedTrace n (evenGrade P X) = normalizedTrace n X := by
  change normalizedTraceLimit (ofStage n (evenGrade P X)) = normalizedTraceLimit (ofStage n X)
  have hP' : ofStage n P * ofStage n P = ofStage n P := by rw [← map_mul, hP]
  have hodd := normalizedTraceLimit_oddGrade (ofStage n P) (ofStage n X) hP'
  have hsplit : ofStage n X = evenGrade (ofStage n P) (ofStage n X) +
      oddGrade (ofStage n P) (ofStage n X) := by
    unfold evenGrade oddGrade
    noncomm_ring
  have heven : ofStage n (evenGrade P X) = evenGrade (ofStage n P) (ofStage n X) := by
    simp only [evenGrade, map_add, map_mul, map_sub, map_one]
  rw [heven]
  have ht := congrArg normalizedTraceLimit hsplit
  rw [map_add, hodd, add_zero] at ht
  exact ht.symm

/-- A positive normalized input remains so after pinching. -/
theorem stage_pinching_normalized_state (n : ℕ) (P X : Stage n)
    (hP : P * P = P) (hPs : star P = P) (hX : X.PosSemidef)
    (htrace : normalizedTrace n X = 1) :
    (evenGrade P X).PosSemidef ∧ normalizedTrace n (evenGrade P X) = 1 :=
  ⟨stage_pinching_posSemidef n P X hPs hX,
    (stage_pinching_normalizedTrace n P X hP).trans htrace⟩

/-- The noncommuting positive witness remains a normalized positive state
under pinching at every finite refinement, with strict quadratic trace loss. -/
theorem dense_pinched_state_all_refinements (m : ℕ) (h : 2 ≤ m) :
    let P := bondMap stageBond 2 m h p
    let X := bondMap stageBond 2 m h denseDensity
    (evenGrade P X).PosSemidef ∧ normalizedTrace m (evenGrade P X) = 1 ∧
    normalizedTrace m (evenGrade P X * evenGrade P X) < normalizedTrace m (X * X) ∧
    bondMap stageBond 2 m h (evenGrade p denseDensity) = evenGrade P X := by
  dsimp only
  have hP : bondMap stageBond 2 m h p * bondMap stageBond 2 m h p =
      bondMap stageBond 2 m h p := by rw [← map_mul, p_isIdempotentElem.eq]
  have hPs : star (bondMap stageBond 2 m h p) = bondMap stageBond 2 m h p := by
    rw [← bondMap_star, p_isSelfAdjoint.star_eq]
  have hs := denseDensity_all_refinements m h
  exact ⟨stage_pinching_posSemidef m _ _ hPs hs.1,
    (stage_pinching_normalizedTrace m _ _ hP).trans hs.2.1,
    denseDensity_refinement_strict_trace_loss m h, bondMap_evenGrade h p denseDensity⟩

end InfoGeometry.Canonical.TensorPeirceStateTransport

end
