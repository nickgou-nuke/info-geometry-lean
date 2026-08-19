import Mathlib.LinearAlgebra.QuadraticForm.Basic

noncomputable section

namespace InfoGeometry.Canonical.NullConeConfinement

/-!
# Null Cone Confinement

\[
\mathrm{NullCone}(q)=\{x\mid q(x)=0\},
\qquad
\mathrm{KleinQuadricBoundary}(q)=\{(a,b)\mid q(a)=0\vee q(b)=0\vee q(a-b)=0\}.
\]

\[
\mathrm{ConfinementOperator}(q):V\to V,
\qquad
\mathrm{confines}(x)\in\mathrm{NullCone}(q).
\]
-/

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- `\mathrm{NullCone}(q):=\{x\mid q(x)=0\}`. -/
def NullCone (q : QuadraticForm K V) : Set V :=
  { x : V | q x = 0 }

/-- `\mathrm{KleinQuadricBoundary}(q)`. -/
def KleinQuadricBoundary (q : QuadraticForm K V) : Set (V × V) :=
  { p : V × V | q p.1 = 0 ∨ q p.2 = 0 ∨ q (p.1 - p.2) = 0 }

/-! A confined state is the Mathlib subtype of states satisfying the cone
constraint; no bespoke state-plus-proof wrapper is needed. -/
abbrev ConfinedState (q : QuadraticForm K V) :=
  { x : V // x ∈ NullCone q }

/-- `\mathrm{project}:V\to V` with image in `\mathrm{NullCone}(q)`. -/
structure ConfinementOperatorData (q : QuadraticForm K V) where
  /-- The abstract projection map -/
  project : V → V

def ConfinementOperatorLaws
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {q : QuadraticForm K V}
    (op : ConfinementOperatorData q) : Prop :=
  (∀ x, op.project x ∈ NullCone q) ∧
  (∀ x, x ∈ NullCone q → op.project x = x)

def ConfinementOperator
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) :=
  {op : ConfinementOperatorData q // ConfinementOperatorLaws op}

namespace ConfinementOperator

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {q : QuadraticForm K V}

abbrev project (op : ConfinementOperator q) : V → V := op.1.project

abbrev confines (op : ConfinementOperator q) :
    ∀ x, project op x ∈ NullCone q := op.2.1

abbrev idempotent_on_cone (op : ConfinementOperator q) :
    ∀ x, x ∈ NullCone q → project op x = x := op.2.2

end ConfinementOperator

/-- `\mathrm{enforce\_confinement}`. -/
def enforce_confinement {q : QuadraticForm K V} 
  (op : ConfinementOperator q) (x : V) : ConfinedState q :=
  ⟨ConfinementOperator.project op x, ConfinementOperator.confines op x⟩

/-- `x\in\mathrm{NullCone}(q) \to \mathrm{project}(x)=x`. -/
theorem confinement_preserves_valid_states {q : QuadraticForm K V}
  (op : ConfinementOperator q) (x : V) (hx : x ∈ NullCone q) :
  (enforce_confinement op x).1 = x := by
  dsimp [enforce_confinement]
  exact ConfinementOperator.idempotent_on_cone op x hx

end InfoGeometry.Canonical.NullConeConfinement
