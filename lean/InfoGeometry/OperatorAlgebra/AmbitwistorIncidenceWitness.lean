import Mathlib.Tactic

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

end InfoGeometry.OperatorAlgebra.AmbitwistorIncidenceWitness
