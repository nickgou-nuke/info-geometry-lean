/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Geometry.RelationalQuantumKinematics
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Geometry.RelationalQuantumKinematics.ProofDependency

inductive Archetype
  | equivariantFrame
  | particleNormalization
  | actionCocycle
  | cocyclicFrameTransport
  | circleNormPreservation
  | particleWaveCovariance
  deriving DecidableEq

instance : Fintype Archetype where
  elems := {Archetype.equivariantFrame, Archetype.particleNormalization,
    Archetype.actionCocycle, Archetype.cocyclicFrameTransport,
    Archetype.circleNormPreservation, Archetype.particleWaveCovariance}
  complete := by
    intro x
    cases x <;> simp

open Archetype

def prerequisites : Archetype → Finset Archetype
  | equivariantFrame => {equivariantFrame}
  | particleNormalization => {equivariantFrame, particleNormalization}
  | actionCocycle => {actionCocycle}
  | cocyclicFrameTransport => {equivariantFrame, actionCocycle, cocyclicFrameTransport}
  | circleNormPreservation =>
      {equivariantFrame, actionCocycle, cocyclicFrameTransport, circleNormPreservation}
  | particleWaveCovariance => Finset.univ

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem causal_branches :
    equivariantFrame < particleNormalization ∧
    equivariantFrame < cocyclicFrameTransport ∧
    actionCocycle < cocyclicFrameTransport ∧
    cocyclicFrameTransport < circleNormPreservation ∧
    particleNormalization < particleWaveCovariance ∧
    circleNormPreservation < particleWaveCovariance := by
  simp only [lt_iff_le_not_ge]
  decide

theorem normalization_and_cocycle_incomparable :
    ¬ particleNormalization ≤ actionCocycle ∧ ¬ actionCocycle ≤ particleNormalization := by
  decide

theorem no_dependency_cycle {earlier later : Archetype}
    (forward : earlier < later) : ¬ later < earlier := lt_asymm forward

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype 1 (`equivariantFrame`):**
Relational reference-frame involution `S_P = P - (1 - P)` satisfies `S_P² = 1` and splits
any operator `X` into frame-commuting (`evenGrade P X`) and frame-anticommuting (`oddGrade P X`)
sectors. -/
theorem archetype_equivariantFrame_relational_split
    {P : B} (hP : P * P = P) (X : B) :
    invS P * invS P = 1 ∧
    comm (invS P) (evenGrade P X) = 0 ∧
    anticomm (invS P) (oddGrade P X) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · peirce_nf hP
  · simp only [evenGrade]; peirce_nf hP
  · simp only [oddGrade]; peirce_nf hP

/-- **Archetype 2 (`particleNormalization`):**
Projector normalization `P + (1 - P) = 1` and diagonal Gram partition
`peirce11 P V + peirce00 P V = V`. -/
theorem archetype_particleNormalization_gram_partition
    {P : B} (hP : P * P = P) (A C : B) :
    P + (1 - P) = 1 ∧
    peirce11 P (genV P A C) + peirce00 P (genV P A C) = genV P A C := by
  refine ⟨by abel, ?_⟩
  simp only [peirce11, peirce00]; peirce_nf hP

/-- **Archetype 3 (`actionCocycle`):**
Relational action cocycle / three-point identity for the quadratic potential `X * X`:
`(X * X - Z * Z) - (X * X - Y * Y) - (Y * Y - Z * Z) = 0` and
`(X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) = anticomm (X - Y) (Y - Z)`. -/
theorem archetype_actionCocycle_noncommutative_three_point (X Y Z : B) :
    (X * X - Z * Z) - (X * X - Y * Y) - (Y * Y - Z * Z) = 0 ∧
    (X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) =
      anticomm (X - Y) (Y - Z) := by
  refine ⟨by abel, ?_⟩
  dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]
  noncomm_ring

/-- **Archetype 4 (`cocyclicFrameTransport`):**
Cocyclic frame transport along the axial generator `Σ = [N_+, N_-]`:
`comm Σ N_+ = 2 • (V * N_+)` and `comm Σ N_- = -2 • (V * N_-)`. -/
theorem archetype_cocyclicFrameTransport_axial_eigenmodes
    {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A) ∧
    comm (genSig P A C) (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C)) := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 5 (`circleNormPreservation`):**
Quadratic norm preservation on the `(Φ, J)` plane:
`Φ² = V`, `J² = -V`, `Φ² + J² = 0`, and `[Σ, Φ]² + [Σ, J]² = 0`. -/
theorem archetype_circleNormPreservation_quadratic_invariants
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
    comm (genSig P A C) (genPhi P A C) * comm (genSig P A C) (genPhi P A C) +
      comm (genSig P A C) (genJ P A C) * comm (genSig P A C) (genJ P A C) = 0 := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 6 (`particleWaveCovariance`):**
Particle–wave covariance identity uniting the diagonal particle density `V = {N_+, N_-}`,
axial current `Σ = [N_+, N_-]`, and off-diagonal wave amplitudes `(Φ, J)`:
`Σ = S_P * V = V * S_P`, `[Σ, Φ] = 2 • (V * J)`, and `[Σ, J] = 2 • (V * Φ)`. -/
theorem archetype_particleWaveCovariance_duality_identities
    {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C = invS P * genV P A C ∧
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Master Synthesis (`relational_quantum_dependency_master_synthesis`):**
Unites the partial-order branch theorems with all six non-commutative `[Ring B]`
relational quantum operator theorems. -/
theorem relational_quantum_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    (equivariantFrame < particleNormalization ∧
      equivariantFrame < cocyclicFrameTransport ∧
      actionCocycle < cocyclicFrameTransport ∧
      cocyclicFrameTransport < circleNormPreservation ∧
      particleNormalization < particleWaveCovariance ∧
      circleNormPreservation < particleWaveCovariance) ∧
    (invS P * invS P = 1) ∧
    (peirce11 P (genV P A C) + peirce00 P (genV P A C) = genV P A C) ∧
    ((X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) =
      anticomm (X - Y) (Y - Z)) ∧
    (comm (genSig P A C) (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A)) ∧
    (genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0) ∧
    (comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C)) := by
  have h1 := archetype_equivariantFrame_relational_split hP X
  have h2 := archetype_particleNormalization_gram_partition hP A C
  have h3 := archetype_actionCocycle_noncommutative_three_point X Y Z
  have h4 := archetype_cocyclicFrameTransport_axial_eigenmodes hP A C
  have h5 := archetype_circleNormPreservation_quadratic_invariants hP A C
  have h6 := archetype_particleWaveCovariance_duality_identities hP A C
  exact ⟨causal_branches, h1.1, h2.2, h3.2, h4.1, h5.1, h6.2.1⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Geometry.RelationalQuantumKinematics.ProofDependency
