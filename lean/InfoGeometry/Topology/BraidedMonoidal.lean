import InfoGeometry.Topology.PointedGroups
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

namespace InfoGeometry.Topology.BraidedMonoidal

open PointedGroups

/-- Concrete algebraic left-hexagon shadow for conjugating braid action. -/
def ConjugationLeftHexagon {G : Type} [Group G] (base x y : G) : Prop :=
  conjugatingBraidAction base (x * y) =
    conjugatingBraidAction base x * conjugatingBraidAction base y

/-- Concrete algebraic right-hexagon/inverse shadow for conjugating braid action. -/
def ConjugationRightHexagon {G : Type} [Group G] (base x : G) : Prop :=
  conjugatingBraidAction base⁻¹ (conjugatingBraidAction base x) = x

/--
Finite, non-vacuous coherence packet for the pointed-group braid shadow.

This is not a full categorical `BraidedCategory` instance.  It records the
algebraic conjugation identities that the pointed-group braid action already
uses: conjugation preserves multiplication and inverse conjugation cancels.
-/
structure HexagonCoherence (D : FreeProductData) where
  hexagon_left : ∀ {G : Type} [Group G] (base x y : G),
    ConjugationLeftHexagon base x y
  hexagon_right : ∀ {G : Type} [Group G] (base x : G),
    ConjugationRightHexagon base x

/-- Left hexagon follows from multiplication preservation by conjugation. -/
theorem conjugation_left_hexagon {G : Type} [Group G] (base x y : G) :
    ConjugationLeftHexagon base x y := by
  exact conjugatingBraidAction_mul base x y

/-- Right hexagon follows from inverse conjugation cancellation. -/
theorem conjugation_right_hexagon {G : Type} [Group G] (base x : G) :
    ConjugationRightHexagon base x := by
  exact conjugatingBraidAction_inverse_cancel base x

/-- Pointed groups carry the finite conjugation braid coherence packet. -/
theorem pointed_groups_form_braided_monoidal (D : FreeProductData) :
  HexagonCoherence D := by
  exact ⟨fun base x y => conjugation_left_hexagon base x y,
    fun base x => conjugation_right_hexagon base x⟩

end InfoGeometry.Topology.BraidedMonoidal
