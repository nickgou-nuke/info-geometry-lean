/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Exact rational incidence data and its verification order

This file formalizes only the finite split-pairing computation specified by
the witness coordinates.  It does not identify that scalar pairing with a
regressive exterior product, an Albert-algebra associator, or a TKK Jacobi
identity; those require concrete maps and structure constants.

The verified dependency order is: split space, coordinate data, incidence
pairing, and finite certificate check.
-/

namespace InfoGeometry.OperatorAlgebra.AmbitwistorIncidenceWitness

/-- The four coordinates in either isotropic half of the split space. -/
abbrev HalfVector := Fin 4 → ℚ

/-- A vector in the split quadratic space `ℚ⁴ ⊕ ℚ⁴`. -/
abbrev SplitVector := HalfVector × HalfVector

/-- The coordinate bilinear form of signature `(4,4)`. -/
def dot4 (x y : HalfVector) : ℚ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

/-- The polarization of the split quadratic form `q(x₊,x₋)=‖x₊‖²-‖x₋‖²`. -/
def splitPairing (x y : SplitVector) : ℚ :=
  dot4 x.1 y.1 - dot4 x.2 y.2

private def zPlus : HalfVector := fun i =>
  if i.val = 0 then 1 else if i.val = 1 then 2 else
    if i.val = 2 then -1 else 3

private def wMinus : HalfVector := fun i =>
  if i.val = 0 then 3 else if i.val = 1 then 1 else
    if i.val = 2 then 2 else -1

/-- The supplied vector supported in the positive isotropic half. -/
def ambitwistorZ : SplitVector := (zPlus, 0)

/-- The supplied vector supported in the negative isotropic half. -/
def ambitwistorW : SplitVector := (0, wMinus)

/-- The stated split-bilinear incidence scalar is exactly zero. -/
theorem supplied_coordinates_are_incident :
    splitPairing ambitwistorZ ambitwistorW = 0 := by
  norm_num [splitPairing, dot4, ambitwistorZ, ambitwistorW,
    zPlus, wMinus]

/-- The five integer weights of a 5-graded Lie algebra. -/
inductive Grade5 where
  | minusTwo
  | minusOne
  | zero
  | plusOne
  | plusTwo
  deriving DecidableEq, Repr

/-- The integer degree represented by each grade label. -/
def Grade5.degree : Grade5 → ℤ
  | .minusTwo => -2
  | .minusOne => -1
  | .zero => 0
  | .plusOne => 1
  | .plusTwo => 2

/-- Every label lies in the declared five-grade support. -/
theorem grade5_degree_mem_support (g : Grade5) :
    -2 ≤ g.degree ∧ g.degree ≤ 2 := by
  cases g <;> simp [Grade5.degree]

/-- Archetypes supported by the formal content of this witness module. -/
inductive Archetype where
  | splitSpace
  | coordinatePair
  | incidenceEvaluation
  | gradingIndex
  deriving DecidableEq, Repr

/-- Rank in the causal order: space precedes coordinates, which precede the
pairing calculation, which precedes the independent grading convention. -/
def Archetype.rank : Archetype → ℕ
  | .splitSpace => 0
  | .coordinatePair => 1
  | .incidenceEvaluation => 2
  | .gradingIndex => 3

/-- The causal partial order on the verified archetypes. -/
def Archetype.precedes (a b : Archetype) : Prop := a.rank ≤ b.rank

theorem Archetype.precedes_refl (a : Archetype) : a.precedes a :=
  Nat.le_refl _

theorem Archetype.precedes_trans {a b c : Archetype}
    (hab : a.precedes b) (hbc : b.precedes c) : a.precedes c :=
  Nat.le_trans hab hbc

theorem Archetype.precedes_antisymm {a b : Archetype}
    (hab : a.precedes b) (hba : b.precedes a) : a = b := by
  cases a <;> cases b <;>
    simp [Archetype.precedes, Archetype.rank] at hab hba ⊢

theorem Archetype.incidence_follows_coordinates :
    Archetype.precedes .coordinatePair .incidenceEvaluation := by
  change (1 : ℕ) ≤ 2
  exact Nat.le_succ 1

theorem Archetype.grading_follows_incidence :
    Archetype.precedes .incidenceEvaluation .gradingIndex := by
  change (2 : ℕ) ≤ 3
  exact Nat.le_succ 2

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype 1 (`splitSpace`):**
In any non-commutative ring `[Ring B]` with idempotent `P * P = P`, the Peirce corners
`N_+ = P A (1 - P)` and `N_- = (1 - P) C P` form complementary isotropic (square-zero)
operator half-spaces. -/
theorem archetype_splitSpace_isotropic_peirce_halves
    {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    invS P * invS P = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 2 (`coordinatePair`):**
The split-signature operator pair `Φ = N_+ + N_-` and `J = N_+ - N_-` have opposite
operator squares `Φ² = V` and `J² = -V`, so `Φ² + J² = 0` and `Φ² - J² = 2 • V`. -/
theorem archetype_coordinatePair_split_quadratic_squares
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
    genPhi P A C * genPhi P A C - genJ P A C * genJ P A C = (2 : ℤ) • genV P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 3 (`incidenceEvaluation`):**
Non-commutative operator incidence evaluation: same-helicity corners annihilate
(`N_+ N_+' = 0`, `N_- N_-' = 0`), while `Φ` and `J` are Jordan-orthogonal (`{Φ, J} = 0`)
with symplectic commutator `[Φ, J] = -2 • Σ`. -/
theorem archetype_incidenceEvaluation_operator_orthogonality
    {P : B} (hP : P * P = P) (A A' C C' : B) :
    conePlus P A * conePlus P A' = 0 ∧
    coneMinus P C * coneMinus P C' = 0 ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 4 (`gradingIndex`):**
Grading derivation `ad_{S_P}(X) = [S_P, X]` assigns exact operator degree weights `-2, 0, +2`
to `N_-`, `evenGrade P X`, and `N_+` respectively:
`[S_P, N_-] = -2 • N_-`, `[S_P, evenGrade P X] = 0`, `[S_P, N_+] = 2 • N_+`, and
`[S_P, [S_P, oddGrade P X]] = 4 • oddGrade P X`. -/
theorem archetype_gradingIndex_derivation_weights
    {P : B} (hP : P * P = P) (A C X : B) :
    comm (invS P) (coneMinus P C) = -((2 : ℤ) • coneMinus P C) ∧
    comm (invS P) (evenGrade P X) = 0 ∧
    comm (invS P) (conePlus P A) = (2 : ℤ) • conePlus P A ∧
    comm (invS P) (comm (invS P) (oddGrade P X)) = (4 : ℤ) • oddGrade P X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · simp only [evenGrade]; peirce_nf hP
  · peirce_nf hP
  · simp only [oddGrade]; peirce_nf hP

/-- **Master Synthesis (`ambitwistor_incidence_operator_master_synthesis`):**
Combines the rational witness incidence, 5-grading bounds, causal archetype order,
and all four non-commutative `[Ring B]` operator theorems. -/
theorem ambitwistor_incidence_operator_master_synthesis
    {P : B} (hP : P * P = P) (A A' C C' X : B) :
    splitPairing ambitwistorZ ambitwistorW = 0 ∧
    (Archetype.precedes .coordinatePair .incidenceEvaluation ∧
      Archetype.precedes .incidenceEvaluation .gradingIndex) ∧
    (conePlus P A * conePlus P A = 0 ∧ coneMinus P C * coneMinus P C = 0) ∧
    (genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0) ∧
    (anticomm (genPhi P A C) (genJ P A C) = 0 ∧
      comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C)) ∧
    (comm (invS P) (coneMinus P C) = -((2 : ℤ) • coneMinus P C) ∧
      comm (invS P) (evenGrade P X) = 0 ∧
      comm (invS P) (conePlus P A) = (2 : ℤ) • conePlus P A) := by
  have h1 := archetype_splitSpace_isotropic_peirce_halves hP A C
  have h2 := archetype_coordinatePair_split_quadratic_squares hP A C
  have h3 := archetype_incidenceEvaluation_operator_orthogonality hP A A' C C'
  have h4 := archetype_gradingIndex_derivation_weights hP A C X
  exact ⟨supplied_coordinates_are_incident,
    ⟨Archetype.incidence_follows_coordinates, Archetype.grading_follows_incidence⟩,
    ⟨h1.1, h1.2.1⟩, h2.2.2.1, ⟨h3.2.2.1, h3.2.2.2⟩, ⟨h4.1, h4.2.1, h4.2.2.1⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.OperatorAlgebra.AmbitwistorIncidenceWitness
