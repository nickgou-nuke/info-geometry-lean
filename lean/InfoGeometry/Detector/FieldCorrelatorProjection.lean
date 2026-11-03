/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Real.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace DetectorGeometry.FieldCorrelatorProjection

section FieldCorrelator

structure FieldCorrelator where
  singleAmplitude : ℝ
  pairAmplitude : ℝ

structure DetectorProjector where
  singleEfficiency : ℝ
  pairEfficiency : ℝ

def projectSingle (detector : DetectorProjector) (field : FieldCorrelator) : ℝ :=
  detector.singleEfficiency * field.singleAmplitude

def projectPair (detector : DetectorProjector) (field : FieldCorrelator) : ℝ :=
  detector.pairEfficiency * field.pairAmplitude

theorem projector_single_linear (detector : DetectorProjector)
    (field₁ field₂ : FieldCorrelator) (r₁ r₂ : ℝ) :
    projectSingle detector
        ⟨r₁ * field₁.singleAmplitude + r₂ * field₂.singleAmplitude,
          r₁ * field₁.pairAmplitude + r₂ * field₂.pairAmplitude⟩ =
      r₁ * projectSingle detector field₁ + r₂ * projectSingle detector field₂ := by
  dsimp [projectSingle]
  rw [mul_add, mul_left_comm detector.singleEfficiency r₁, mul_left_comm detector.singleEfficiency r₂]

theorem projector_pair_bilinear_scale (ε₁ ε₂ a b : ℝ) :
    (ε₁ * ε₂) * (a * b) = (ε₁ * a) * (ε₂ * b) :=
  mul_mul_mul_comm ε₁ ε₂ a b

end FieldCorrelator

section ModeProjection

def modeTrace (monopole oscillatory : ℝ) : ℝ := monopole + 0 * oscillatory

theorem oscillatory_modes_annihilated (monopole oscillatory : ℝ) :
    modeTrace monopole oscillatory = monopole := by
  dsimp [modeTrace]
  rw [MulZeroClass.zero_mul, AddMonoid.add_zero]

theorem modeTrace_linear (m₁ o₁ m₂ o₂ r₁ r₂ : ℝ) :
    modeTrace (r₁ * m₁ + r₂ * m₂) (r₁ * o₁ + r₂ * o₂) =
      r₁ * modeTrace m₁ o₁ + r₂ * modeTrace m₂ o₂ := by
  dsimp [modeTrace]
  repeat rw [MulZeroClass.zero_mul, AddMonoid.add_zero]

end ModeProjection

section RankHierarchy

def singlesCount (N₀ ε X : ℝ) : ℝ := N₀ * ε * X

def coincidenceCount (N₀ K X : ℝ) : ℝ := N₀ * K * X ^ 2

theorem coincidence_is_rank_two (N₀ K X : ℝ) :
    coincidenceCount N₀ K X = (N₀ * K) * X ^ 2 :=
  rfl

theorem square_root_coordinate_is_linear (N₀ ε X : ℝ) :
    singlesCount N₀ ε X = (N₀ * ε) * X :=
  rfl

theorem detector_projection_parabola (N₀ K X : ℝ) :
    coincidenceCount N₀ K X = (N₀ * K) * X ^ 2 :=
  coincidence_is_rank_two N₀ K X

end RankHierarchy

section CausalPoset

inductive Archetype
  | fieldCorrelator
  | detectorProjector
  | modeNullspace
  | rankHierarchy
  | scaleInvariantObservable
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .fieldCorrelator => 195
  | .detectorProjector => 196
  | .modeNullspace => 197
  | .rankHierarchy => 198
  | .scaleInvariantObservable => 199

def causallyPrecedes (a b : Archetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c :=
  Nat.le_trans

theorem rank_inj : ∀ {a b : Archetype}, rank a = rank b → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

theorem causal_antisymm {a b : Archetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b :=
  fun hab hba => rank_inj (Nat.le_antisymm hab hba)

theorem canonical_chain :
    causallyPrecedes .fieldCorrelator .detectorProjector ∧
    causallyPrecedes .detectorProjector .modeNullspace ∧
    causallyPrecedes .modeNullspace .rankHierarchy ∧
    causallyPrecedes .rankHierarchy .scaleInvariantObservable :=
  ⟨Nat.le_succ 195, Nat.le_succ 196, Nat.le_succ 197, Nat.le_succ 198⟩

end CausalPoset

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `FieldCorrelatorProjection.Archetype`
node to its canonical Peirce operator in `[Ring B]`. -/
def fieldCorrelatorOperator (P A C X : B) : Archetype → B
  | .fieldCorrelator => X
  | .detectorProjector => evenGrade P X
  | .modeNullspace => evenGrade P (oddGrade P X)
  | .rankHierarchy => genPhi P A C * genPhi P A C
  | .scaleInvariantObservable => invS P * evenGrade P X * invS P

/-- **Theorem (Non-Commutative Operator Field-Correlator Projection over `[Ring B]`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the detector
projector `evenGrade P` annihilates oscillatory off-diagonal modes (`evenGrade P (oddGrade P X) = 0`),
is invariant under reflection conjugation (`S (evenGrade P X) S = evenGrade P X`), and maps
the quadratic rank-two square `Φ²` to `V`. -/
theorem fieldCorrelator_operator_identities {P : B} (hP : P * P = P) (A C X : B) :
    fieldCorrelatorOperator P A C X .detectorProjector + oddGrade P X =
      fieldCorrelatorOperator P A C X .fieldCorrelator ∧
    fieldCorrelatorOperator P A C X .modeNullspace = 0 ∧
    fieldCorrelatorOperator P A C X .rankHierarchy = genV P A C ∧
    fieldCorrelatorOperator P A C X .scaleInvariantObservable =
      fieldCorrelatorOperator P A C X .detectorProjector := by
  dsimp only [fieldCorrelatorOperator]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end DetectorGeometry.FieldCorrelatorProjection
