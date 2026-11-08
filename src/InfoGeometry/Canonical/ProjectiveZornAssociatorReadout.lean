import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Projective readout of a nonassociative associator

The Zorn product is evaluated before a scalar readout is taken.  A homogeneous
readout then gives a representative-independent observable after division by
a reference readout.  This is an algebraic projective statement; it does not
replace the native nonassociative carrier by a scalar model.
-/

namespace InfoGeometry.Canonical.ProjectiveZornAssociatorReadout

section

variable {A W : Type*} [NonUnitalNonAssocRing A] [AddCommMonoid W]
  [Module ℝ W]

/-- The associator with its two parenthesizations retained explicitly. -/
def associatorValue (X Y Z : A) : A :=
  (X * Y) * Z - X * (Y * Z)

/-- A homogeneous scalar readout of an explicitly parenthesized associator. -/
noncomputable def normalizedAssociatorReadout
    (E : W → A → ℝ) (w : W) (X Y Z R : A) : ℝ :=
  E w (associatorValue X Y Z) / E w R

theorem normalizedAssociatorReadout_scale_invariant
    (E : W → A → ℝ)
    (hE : ∀ (a : ℝ) (w : W) (X : A), E (a • w) X = a * E w X)
    (w : W) (a : ℝ) (ha : a ≠ 0)
    (X Y Z R : A) (hR : E w R ≠ 0) :
    normalizedAssociatorReadout E (a • w) X Y Z R =
      normalizedAssociatorReadout E w X Y Z R := by
  unfold normalizedAssociatorReadout
  rw [hE a w (associatorValue X Y Z), hE a w R]
  field_simp [hR, ha]

theorem normalizedAssociatorReadout_scale_invariant_pos
    (E : W → A → ℝ)
    (hE : ∀ (a : ℝ) (w : W) (X : A), E (a • w) X = a * E w X)
    (w : W) (a : ℝ) (ha : 0 < a)
    (X Y Z R : A) (hR : E w R ≠ 0) :
    normalizedAssociatorReadout E (a • w) X Y Z R =
      normalizedAssociatorReadout E w X Y Z R :=
  normalizedAssociatorReadout_scale_invariant E hE w a (ne_of_gt ha) X Y Z R hR

theorem associatorValue_zero_iff
    (X Y Z : A) :
    associatorValue X Y Z = 0 ↔ (X * Y) * Z = X * (Y * Z) := by
  unfold associatorValue
  exact sub_eq_zero

end

end InfoGeometry.Canonical.ProjectiveZornAssociatorReadout
