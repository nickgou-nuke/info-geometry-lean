import InfoGeometry.Canonical.KleinBottleTopology
import InfoGeometry.Canonical.KleinBottleOrientifold

/-!
# Klein Bottle Boundary Action

Finite boundary action packet for the Klein-bottle/orientifold lane.

This module adds only the finite topological story requested here:

* a two-bit `Z₂` boundary cell;
* a sheet reflection, a deck translation, and their glide reflection;
* closed proofs that these maps square to the identity and commute in this
  finite boundary model;
* a conditional boundary-operator lemma connecting
  `KleinBottleTopology.klein_gluing` to the existing orientifold packet.

#### BUCKET 1: CLOSED FINITE THEOREMS
`sheetReflection_involutive`, `deckTranslation_involutive`,
`sheet_deck_commute`, `glideReflection_eq_deck_sheet`, and
`glideReflection_involutive` are closed finite `Z₂` action facts.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`orientifold_klein_gluing_trace_closure` depends on explicit orientifold
hypotheses and the existing `KleinBottleTopology.klein_topology_trace_closure`
operator lemma.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove that a global Klein bottle is realized by the analytic
prime gas, does not construct a topological quotient space, and does not derive
the orientifold propositions from geometry.
-/

noncomputable section

namespace KleinBottleBoundaryAction

open Matrix

/-- A finite two-bit boundary cell: deck coordinate and sheet coordinate. -/
structure KleinBoundaryCell where
  deck : Bool
  sheet : Bool
  deriving DecidableEq

namespace KleinBoundaryCell

@[ext] theorem ext {x y : KleinBoundaryCell}
    (hdeck : x.deck = y.deck) (hsheet : x.sheet = y.sheet) : x = y := by
  cases x
  cases y
  simp_all

/-- Reflection across the sheet coordinate. -/
def sheetReflection (x : KleinBoundaryCell) : KleinBoundaryCell :=
  { x with sheet := !x.sheet }

/-- Deck translation by the nontrivial `Z₂` element. -/
def deckTranslation (x : KleinBoundaryCell) : KleinBoundaryCell :=
  { x with deck := !x.deck }

/-- The finite glide reflection: translate along the deck and flip the sheet. -/
def glideReflection (x : KleinBoundaryCell) : KleinBoundaryCell :=
  deckTranslation (sheetReflection x)

@[simp] theorem sheetReflection_deck (x : KleinBoundaryCell) :
    (sheetReflection x).deck = x.deck := by
  rfl

@[simp] theorem sheetReflection_sheet (x : KleinBoundaryCell) :
    (sheetReflection x).sheet = !x.sheet := by
  rfl

@[simp] theorem deckTranslation_deck (x : KleinBoundaryCell) :
    (deckTranslation x).deck = !x.deck := by
  rfl

@[simp] theorem deckTranslation_sheet (x : KleinBoundaryCell) :
    (deckTranslation x).sheet = x.sheet := by
  rfl

/-- Sheet reflection is the nontrivial `Z₂` action on the sheet coordinate. -/
theorem sheetReflection_involutive :
    Function.Involutive sheetReflection := by
  intro x
  ext <;> simp [sheetReflection]

/-- Deck translation is the nontrivial `Z₂` action on the deck coordinate. -/
theorem deckTranslation_involutive :
    Function.Involutive deckTranslation := by
  intro x
  ext <;> simp [deckTranslation]

/-- The two finite `Z₂` generators commute in this boundary-cell model. -/
theorem sheet_deck_commute (x : KleinBoundaryCell) :
    sheetReflection (deckTranslation x) =
      deckTranslation (sheetReflection x) := by
  ext <;> simp [sheetReflection, deckTranslation]

/-- The glide reflection is the deck translation after sheet reflection. -/
theorem glideReflection_eq_deck_sheet (x : KleinBoundaryCell) :
    glideReflection x = deckTranslation (sheetReflection x) := by
  rfl

/-- The finite glide reflection is involutive. -/
theorem glideReflection_involutive :
    Function.Involutive glideReflection := by
  intro x
  ext <;> simp [glideReflection, deckTranslation, sheetReflection]

/-- Bundled finite action packet for the Klein-bottle boundary cell. -/
theorem finite_z2_glide_action_packet :
    Function.Involutive sheetReflection ∧
      Function.Involutive deckTranslation ∧
      (∀ x : KleinBoundaryCell,
        sheetReflection (deckTranslation x) =
          deckTranslation (sheetReflection x)) ∧
      Function.Involutive glideReflection :=
  ⟨sheetReflection_involutive,
    deckTranslation_involutive,
    sheet_deck_commute,
    glideReflection_involutive⟩

end KleinBoundaryCell

/--
Boundary-operator bridge from `KleinBottleTopology` to the existing
`KleinBottleOrientifold` packet.

The orientifold propositions remain explicit hypotheses.  The closed operator
content is exactly the existing trace-closure theorem for `klein_gluing`.
-/
theorem orientifold_klein_gluing_trace_closure
    (O : KleinBottleOrientifold.KleinBottleOrientifold)
    (M P_parity : Matrix (Fin 32) (Fin 32) ℝ)
    (h_orth : P_parityᵀ * P_parity = 1)
    (h_trace : Matrix.trace M = 0)
    (h_projection : O.orientationReversingProjection)
    (h_quotient : O.kleinBottleQuotient) :
    Matrix.trace (KleinBottleTopology.klein_gluing M P_parity) = 0 ∧
      O.orientationReversingProjection ∧
      O.kleinBottleQuotient := by
  exact ⟨KleinBottleTopology.klein_topology_trace_closure M P_parity h_orth h_trace,
    h_projection,
    h_quotient⟩

end KleinBottleBoundaryAction

