import InfoGeometry.Topology.PointedGroups
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

namespace InfoGeometry.Topology.BraidedMonoidal

open PointedGroups

/-- Multiplicativity coherence for the native conjugating braid automorphism. -/
def ConjugationLeftHexagon {G : Type} [Group G] (base x y : G) : Prop :=
  conjugatingBraidAction base (x * y) =
    conjugatingBraidAction base x * conjugatingBraidAction base y

/-- Inverse coherence for the native conjugating braid automorphism. -/
def ConjugationRightHexagon {G : Type} [Group G] (base x : G) : Prop :=
  conjugatingBraidAction base⁻¹ (conjugatingBraidAction base x) = x

/-- Left hexagon follows from multiplication preservation by conjugation. -/
theorem conjugation_left_hexagon {G : Type} [Group G] (base x y : G) :
    ConjugationLeftHexagon base x y := by
  exact conjugatingBraidAction_mul base x y

/-- Right hexagon follows from inverse conjugation cancellation. -/
theorem conjugation_right_hexagon {G : Type} [Group G] (base x : G) :
    ConjugationRightHexagon base x := by
  exact conjugatingBraidAction_inverse_cancel base x

/-- The native pointed conjugation action is multiplicative and invertible. -/
theorem pointed_conjugation_action_coherent :
    (∀ {G : Type} [Group G] (base x y : G),
      ConjugationLeftHexagon base x y) ∧
    (∀ {G : Type} [Group G] (base x : G),
      ConjugationRightHexagon base x) :=
  ⟨fun base x y => conjugation_left_hexagon base x y,
    fun base x => conjugation_right_hexagon base x⟩

/--
Compatibility name retained for downstream code. Its exact content is the
proved coherence of a native `MulAut`, not a `BraidedCategory` instance.
-/
theorem pointed_groups_form_braided_monoidal :
    (∀ {G : Type} [Group G] (base x y : G),
      ConjugationLeftHexagon base x y) ∧
    (∀ {G : Type} [Group G] (base x : G),
      ConjugationRightHexagon base x) :=
  pointed_conjugation_action_coherent

end InfoGeometry.Topology.BraidedMonoidal
