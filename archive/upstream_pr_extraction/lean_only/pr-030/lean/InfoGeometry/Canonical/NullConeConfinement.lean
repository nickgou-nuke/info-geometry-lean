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
structure ConfinementOperator (q : QuadraticForm K V) where
  /-- The abstract projection map -/
  project : V → V
  /-- The projected state unconditionally satisfies the null cone constraint -/
  confines : ∀ (x : V), project x ∈ NullCone q
  /-- The operator acts as the identity on states already confined -/
  idempotent_on_cone : ∀ (x : V), x ∈ NullCone q → project x = x

/-- `\mathrm{enforce\_confinement}`. -/
def enforce_confinement {q : QuadraticForm K V} 
  (op : ConfinementOperator q) (x : V) : ConfinedState q :=
  ⟨op.project x, op.confines x⟩

/-- `x\in\mathrm{NullCone}(q) \to \mathrm{project}(x)=x`. -/
theorem confinement_preserves_valid_states {q : QuadraticForm K V}
  (op : ConfinementOperator q) (x : V) (hx : x ∈ NullCone q) :
  (enforce_confinement op x).1 = x := by
  dsimp [enforce_confinement]
  exact op.idempotent_on_cone x hx

end InfoGeometry.Canonical.NullConeConfinement
