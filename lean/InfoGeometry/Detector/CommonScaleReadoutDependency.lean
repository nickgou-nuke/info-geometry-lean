/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Detector.CommonScaleReadout
import InfoGeometry.EmergentGeometry.HarmonicMeanValue
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Detector.CommonScaleReadout.ProofDependency

inductive Archetype
  | harmonicMeanValue
  | concentricMeans
  | quadraticScale
  | rootFactorization
  | quotientCancellation
  | inverseSquareModel
  | constantDerivative
  deriving DecidableEq

open Archetype

instance : Fintype Archetype where
  elems := [harmonicMeanValue, concentricMeans, quadraticScale, rootFactorization, quotientCancellation, inverseSquareModel, constantDerivative].toFinset
  complete := by
    intro x
    cases x <;> simp

def prerequisites : Archetype → Finset Archetype
  | harmonicMeanValue => {harmonicMeanValue}
  | concentricMeans => {harmonicMeanValue, concentricMeans}
  | quadraticScale => {quadraticScale}
  | rootFactorization => {quadraticScale, rootFactorization}
  | quotientCancellation => {quadraticScale, rootFactorization, quotientCancellation}
  | inverseSquareModel =>
      {quadraticScale, rootFactorization, quotientCancellation, inverseSquareModel}
  | constantDerivative =>
      {quadraticScale, rootFactorization, quotientCancellation, constantDerivative}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem dependency_edges :
    harmonicMeanValue < concentricMeans ∧ quadraticScale < rootFactorization ∧
      rootFactorization < quotientCancellation ∧
      quotientCancellation < inverseSquareModel ∧ quotientCancellation < constantDerivative := by
  simp only [lt_iff_le_not_ge]
  decide

theorem harmonic_and_algebraic_branches_incomparable :
    ¬ concentricMeans ≤ constantDerivative ∧ ¬ constantDerivative ≤ concentricMeans := by
  decide

theorem model_and_derivative_incomparable :
    ¬ inverseSquareModel ≤ constantDerivative ∧ ¬ constantDerivative ≤ inverseSquareModel := by
  decide

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetypes 1–2 (`harmonicMeanValue`, `concentricMeans`):**
Symmetric Jordan anticommutator mean `{X, Y} = X * Y + Y * X` and concentric Peirce
sandwich average `sandwichCross P A C X + sandwichSame P A C X = Φ * X * Φ`. -/
theorem archetype_harmonic_and_concentric_operator_means
    {P : B} (hP : P * P = P) (A C X Y : B) :
    anticomm X Y + comm X Y = (2 : ℤ) • (X * Y) ∧
    sandwichCross P A C X + sandwichSame P A C X = genPhi P A C * X * genPhi P A C ∧
    sandwichCross P A C X - sandwichSame P A C X = -(genJ P A C * X * genJ P A C) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]; noncomm_ring
  · simp only [sandwichCross, sandwichSame]; peirce_nf hP
  · simp only [sandwichCross, sandwichSame]; peirce_nf hP

/-- **Archetypes 3–5 (`quadraticScale`, `rootFactorization`, `quotientCancellation`):**
Quadratic scale operator `V = Φ² = -J²`, chiral root factorization `(Φ + J) * (Φ - J) = 2 • (V + Σ)`,
and square-sum cancellation `Φ² + J² = 0`. -/
theorem archetype_quadratic_scale_root_factorization_and_cancellation
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    (genPhi P A C + genJ P A C) * (genPhi P A C - genJ P A C) =
      (2 : ℤ) • (genV P A C + genSig P A C) ∧
    genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetypes 6–7 (`inverseSquareModel`, `constantDerivative`):**
Second-order derivation scale `derivSqPhi P A C (genJ P A C) = -4 • (V * J)` and constant
grading derivative `[S_P, Φ] = 2 • J`, `[S_P, J] = 2 • Φ`. -/
theorem archetype_second_order_scale_and_grading_derivative
    {P : B} (hP : P * P = P) (A C : B) :
    derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    comm (invS P) (genPhi P A C) = (2 : ℤ) • genJ P A C ∧
    comm (invS P) (genJ P A C) = (2 : ℤ) • genPhi P A C := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [derivSqPhi]; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- **Master Synthesis (`common_scale_readout_dependency_master_synthesis`):**
Unites the 7-stage partial-order branch theorems with the non-commutative `[Ring B]`
common-scale readout operator theorems. -/
theorem common_scale_readout_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C X Y : B) :
    (harmonicMeanValue < concentricMeans ∧ quadraticScale < rootFactorization ∧
      rootFactorization < quotientCancellation ∧
      quotientCancellation < inverseSquareModel ∧ quotientCancellation < constantDerivative) ∧
    (sandwichCross P A C X + sandwichSame P A C X = genPhi P A C * X * genPhi P A C) ∧
    (genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0) ∧
    (derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
      comm (invS P) (genPhi P A C) = (2 : ℤ) • genJ P A C) := by
  have h1 := archetype_harmonic_and_concentric_operator_means hP A C X Y
  have h2 := archetype_quadratic_scale_root_factorization_and_cancellation hP A C
  have h3 := archetype_second_order_scale_and_grading_derivative hP A C
  exact ⟨dependency_edges, h1.2.1, h2.2.2.2, ⟨h3.1, h3.2.1⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Detector.CommonScaleReadout.ProofDependency
