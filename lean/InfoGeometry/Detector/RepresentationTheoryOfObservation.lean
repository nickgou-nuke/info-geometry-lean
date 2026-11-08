/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace DetectorGeometry.RepresentationTheoryOfObservation

/-! The formal content extracted from the stream is algebraic. Statements about
physical systems are represented by explicit structures or hypotheses; no
physical identification is introduced as an axiom. -/

section Representations

structure Representation (G V : Type*) where
  act : G → V → V

def IsInvariant {G V Y : Type*} (representation : Representation G V)
    (observable : V → Y) : Prop :=
  ∀ g v, observable (representation.act g v) = observable v

theorem invariant_comp {G V Y Z : Type*} (representation : Representation G V)
    (observable : V → Y) (postprocess : Y → Z)
    (hinv : IsInvariant representation observable) :
    IsInvariant representation (postprocess ∘ observable) := by
  intro g v
  simp [Function.comp, hinv g v]

end Representations

section RankConstraint

def singleCount (ε : ℝ) : ℝ := ε

def coincidenceCount (k ε : ℝ) : ℝ := k * ε ^ 2

theorem coincidenceCount_eq_coefficient_mul_singleCount_sq (k ε : ℝ) :
    coincidenceCount k ε = k * (singleCount ε) ^ 2 := by
  rfl

theorem rank_two_is_quadratic (k ε : ℝ) :
    coincidenceCount k ε = coincidenceCount k (-ε) := by
  simp [coincidenceCount]

end RankConstraint

section PoissonMetric

noncomputable def poissonMetric (N dN : ℝ) : ℝ := dN ^ 2 / N

noncomputable def rootCoordinate (N : ℝ) : ℝ := Real.sqrt N

theorem rootCoordinate_sq (N : ℝ) (hN : 0 ≤ N) :
    rootCoordinate N ^ 2 = N := by
  simp [rootCoordinate, Real.sq_sqrt hN]

theorem poissonMetric_rootCoordinate (x dx : ℝ) (hx : 0 < x) :
    poissonMetric (x ^ 2) (2 * x * dx) = 4 * dx ^ 2 := by
  dsimp [poissonMetric]
  have hxne : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

end PoissonMetric

section BoundaryConstraint

def boundedCapacity (x : ℝ) : ℝ := x * (1 - x)

def complement (x : ℝ) : ℝ := 1 - x

theorem boundedCapacity_complement (x : ℝ) :
    boundedCapacity (complement x) = boundedCapacity x := by
  simp [boundedCapacity, complement]
  ring

theorem complement_fixed_iff (x : ℝ) : complement x = x ↔ x = 1 / 2 := by
  simp only [complement]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    norm_num

theorem boundedCapacity_nonnegative {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    0 ≤ boundedCapacity x := by
  exact mul_nonneg hx₀ (sub_nonneg.mpr hx₁)

end BoundaryConstraint

section CanonicalPeriod

noncomputable def normalizedPrimitive (x : ℝ) : ℝ := x ^ 2 / 2 - x ^ 3 / 3

theorem normalizedPeriod :
    normalizedPrimitive 1 - normalizedPrimitive 0 = 1 / 6 := by
  norm_num [normalizedPrimitive]

end CanonicalPeriod

section CausalPoset

inductive Archetype
  | rankRepresentation
  | poissonFlattening
  | boundaryReflection
  | selfDualMidpoint
  | canonicalPeriod
  | observationSynthesis
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .rankRepresentation => 180
  | .poissonFlattening => 181
  | .boundaryReflection => 182
  | .selfDualMidpoint => 183
  | .canonicalPeriod => 184
  | .observationSynthesis => 185

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
    causallyPrecedes .rankRepresentation .poissonFlattening ∧
    causallyPrecedes .poissonFlattening .boundaryReflection ∧
    causallyPrecedes .boundaryReflection .selfDualMidpoint ∧
    causallyPrecedes .selfDualMidpoint .canonicalPeriod ∧
    causallyPrecedes .canonicalPeriod .observationSynthesis := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `RepresentationTheoryOfObservation.Archetype`
node to its canonical Peirce operator in `[Ring B]`. -/
def observationRepresentationOperator (P A C X : B) : Archetype → B
  | .rankRepresentation => evenGrade P X + oddGrade P X
  | .poissonFlattening => genPhi P A C * genPhi P A C
  | .boundaryReflection => invS P
  | .selfDualMidpoint => invS P * evenGrade P X * invS P
  | .canonicalPeriod => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)
  | .observationSynthesis => projV P A C X + projPhi P A C X + projJ P A C X + projSig P A C X

/-- **Theorem (Non-Commutative Operator Representation Theory of Observation over `[Ring B]`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the six archetypes
satisfy Peirce completeness, quadratic flattening `Φ² = V`, involutive reflection `S² = 1`,
self-dual midpoint invariance `S (evenGrade P X) S = evenGrade P X`, commutator period
`[Φ, J] = 2 Σ`, and Fierz synthesis completeness. -/
theorem observationRepresentation_operator_identities {P : B} (hP : P * P = P) (A C X : B) :
    observationRepresentationOperator P A C X .rankRepresentation = X ∧
    observationRepresentationOperator P A C X .poissonFlattening = genV P A C ∧
    observationRepresentationOperator P A C X .boundaryReflection *
      observationRepresentationOperator P A C X .boundaryReflection = 1 ∧
    observationRepresentationOperator P A C X .selfDualMidpoint = evenGrade P X ∧
    observationRepresentationOperator P A C X .canonicalPeriod = -((2 : ℤ) • genSig P A C) ∧
    observationRepresentationOperator P A C X .observationSynthesis =
      (8 : ℤ) • X := by
  dsimp only [observationRepresentationOperator]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · exact (InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A5_klein_hadamard_spectra_and_partition
      (P := P) hP A C X).1

end NonCommutativeOperatorRealization

end DetectorGeometry.RepresentationTheoryOfObservation
