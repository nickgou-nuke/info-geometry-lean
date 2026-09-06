import Mathlib.CategoryTheory.Category.Preorder
import InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus

/-!
# Categorical bridge for thermodynamic chiral graph reduction

This file lifts the one-step and multi-step reduction relation on
`ThermoTerm` to the standard `Preorder`/category interface in Mathlib.
No diagonal shortcuts are used: all results are direct consequences of
`Step`, `Reduces`, and categorical primitives for preorder categories.
-/ 

namespace InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus

open ThermoTerm
open CategoryTheory

namespace Reduces

/-- `Reduces` is transitive, in the expected way for a reflexive-transitive closure. -/
theorem trans
    {a b c : ThermoTerm}
    (hab : Reduces a b)
    (hbc : Reduces b c) :
    Reduces a c := by
  induction hab with
  | refl =>
      simpa using hbc
  | tail h hrest ih =>
      exact ThermoTerm.Reduces.tail h (ih hbc)

end Reduces

/-- A native preorder on thermodynamic graph terms induced by reduction. -/
def reductionPreorder : Preorder ThermoTerm :=
  { le := Reduces
    le_refl := Reduces.refl
    le_trans := by
      intro a b c hab hbc
      exact Reduces.trans hab hbc
  }

/-- Multi-step reduction and preorder-category morphisms agree on existence. -/
theorem hom_iff_reduces
    (t u : ThermoTerm) :
    (letI : Preorder ThermoTerm := reductionPreorder
      ; Nonempty (t ⟶ u)) ↔
    Reduces t u := by
  letI : Preorder ThermoTerm := reductionPreorder
  constructor
  · rintro ⟨h⟩
    exact leOfHom h
  · intro h
    exact ⟨homOfLE h⟩

/-- Any one-step `Step` reduction gives a nonempty hom in the induced preorder category. -/
theorem hom_of_step
    {t u : ThermoTerm} (h : Step t u) :
    (letI : Preorder ThermoTerm := reductionPreorder
      ; Nonempty (t ⟶ u)) := by
  letI : Preorder ThermoTerm := reductionPreorder
  exact ⟨homOfLE (Reduces.single h)⟩

/-- A normal term has no outgoing nontrivial reduction, hence no non-identity codomain. -/
theorem normal_is_terminal
    {t u : ThermoTerm}
    (ht : IsNormal t)
    (h : Reduces t u) : t = u := by
  induction h with
  | refl => rfl
  | tail hstep htail ih =>
      exfalso
      exact ht ⟨_, hstep⟩

/-- In the induced reduction category, normality is equivalent to uniqueness of arrow target. -/
theorem normal_hom_eq_self
    {t u : ThermoTerm}
    (ht : IsNormal t)
    (h : (letI : Preorder ThermoTerm := reductionPreorder
      ; Nonempty (t ⟶ u))) :
    u = t := by
  have hred : Reduces t u := by
    letI : Preorder ThermoTerm := reductionPreorder
    rcases (show Nonempty (t ⟶ u) from h) with ⟨h'⟩
    exact leOfHom h'
  exact (normal_is_terminal ht hred).symm

end InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
