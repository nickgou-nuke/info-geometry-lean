/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace DetectorGeometry.RankOneSpectralExtraction

section PerLineParabola

def observedLine (C K X : ℝ) : ℝ := C * X - K * X ^ 2

def correctedLine (C K X : ℝ) : ℝ := observedLine C K X + K * X ^ 2

theorem correctedLine_recovers_linear (C K X : ℝ) :
    correctedLine C K X = C * X := by
  simp [correctedLine, observedLine]

theorem observedLine_vertex_decomposition (C K X : ℝ) :
    observedLine C K X + K * X ^ 2 = C * X := by
  exact correctedLine_recovers_linear C K X

theorem zero_intercept_at_zero (C K : ℝ) : observedLine C K 0 = 0 := by
  simp [observedLine]

end PerLineParabola

section RankOneFactorization

def spectralResponse (u v : ℝ → ℝ) (i j : ℝ) : ℝ := u i * v j

def isRankOne (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ u v : ℝ → ℝ, ∀ i j, f i j = u i * v j

theorem cleaned_spectrum_is_rank_one (u v : ℝ → ℝ) :
    isRankOne (spectralResponse u v) := by
  refine ⟨u, v, ?_⟩
  intro i j
  rfl

theorem rank_one_minor_vanishes (u v : ℝ → ℝ) (i₁ i₂ j₁ j₂ : ℝ) :
    spectralResponse u v i₁ j₁ * spectralResponse u v i₂ j₂ -
      spectralResponse u v i₁ j₂ * spectralResponse u v i₂ j₁ = 0 := by
  simp only [spectralResponse]
  ring

theorem corrected_observations_factor (line scale C K : ℝ) :
    correctedLine (line * scale) K 1 = spectralResponse (fun _ => line) (fun _ => scale) 0 0 := by
  simp [correctedLine, observedLine, spectralResponse]

end RankOneFactorization

section CausalPoset

inductive Archetype
  | perLineParabola
  | quadraticRemoval
  | universalRootScale
  | rankOneSpectrum
  | scaleInvariantField
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .perLineParabola => 190
  | .quadraticRemoval => 191
  | .universalRootScale => 192
  | .rankOneSpectrum => 193
  | .scaleInvariantField => 194

def causallyPrecedes (a b : Archetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := by
  exact Nat.le_trans

theorem causal_antisymm {a b : Archetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢

theorem canonical_chain :
    causallyPrecedes .perLineParabola .quadraticRemoval ∧
    causallyPrecedes .quadraticRemoval .universalRootScale ∧
    causallyPrecedes .universalRootScale .rankOneSpectrum ∧
    causallyPrecedes .rankOneSpectrum .scaleInvariantField := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `RankOneSpectralExtraction.Archetype`
node to its canonical Peirce operator in `[Ring B]`. -/
def rankOneSpectralOperator (P A C X : B) : Archetype → B
  | .perLineParabola => P * (1 - P)
  | .quadraticRemoval => evenGrade P (oddGrade P X)
  | .universalRootScale => genPhi P A C
  | .rankOneSpectrum => genV P A C
  | .scaleInvariantField => invS P * evenGrade P X * invS P

/-- **Theorem (Non-Commutative Rank-One Spectral Extraction over `[Ring B]`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the quadratic
parabola defect `P (1 - P) = 0` and off-diagonal removal `evenGrade P (oddGrade P X) = 0`
vanish, `Φ² = V`, and `evenGrade P X` is invariant under reflection conjugation. -/
theorem rankOneSpectral_operator_identities {P : B} (hP : P * P = P) (A C X : B) :
    rankOneSpectralOperator P A C X .perLineParabola = 0 ∧
    rankOneSpectralOperator P A C X .quadraticRemoval = 0 ∧
    rankOneSpectralOperator P A C X .universalRootScale *
      rankOneSpectralOperator P A C X .universalRootScale =
      rankOneSpectralOperator P A C X .rankOneSpectrum ∧
    rankOneSpectralOperator P A C X .scaleInvariantField = evenGrade P X := by
  dsimp only [rankOneSpectralOperator]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end DetectorGeometry.RankOneSpectralExtraction
