import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Algebra.AssociativityObstruction

A nonassociative multiplication cannot be represented by an injective
multiplicative map into an associative semigroup.

This is the formal obstruction preventing a split-octonion/Zorn algebra from
being identified with ordinary associative matrix multiplication.

Bektaş-style quaternion block matrices may be used as left/right multiplication
operator dictionaries or transported-product coordinate systems. They must not
be registered as ordinary multiplicative algebra equivalences into an
associative matrix algebra unless associativity of the source has first been
proved.
-/

namespace InfoGeometry.Algebra

/--
If a multiplication on `O` is represented injectively and multiplicatively
inside an associative semigroup `A`, then the multiplication on `O` is
associative.

This is the exact obstruction:

* ordinary matrix multiplication is associative;
* an injective multiplicative representation into it would force associativity
  of the source multiplication;
* therefore a genuinely nonassociative algebra cannot admit such a
  representation.
-/
theorem associative_of_injective_mul_map_to_semigroup
    {O A : Type*} [Mul O] [Semigroup A]
    (φ : O → A)
    (hinj : Function.Injective φ)
    (hmul : ∀ x y : O, φ (x * y) = φ x * φ y) :
    ∀ x y z : O, (x * y) * z = x * (y * z) := by
  intro x y z
  apply hinj
  calc
    φ ((x * y) * z)
        = φ (x * y) * φ z := hmul (x * y) z
    _ = (φ x * φ y) * φ z := by
        rw [hmul x y]
    _ = φ x * (φ y * φ z) := by
        rw [mul_assoc]
    _ = φ x * φ (y * z) := by
        rw [← hmul y z]
    _ = φ (x * (y * z)) := by
        rw [← hmul x (y * z)]

/--
Contrapositive form.

If `O` has a witnessed associator defect, then there is no injective
multiplicative map from `O` into any associative semigroup `A`.

This is the theorem to cite before rejecting any proposed ordinary
`AlgEquiv` from a nonassociative split-octonion/Zorn product into an
associative matrix algebra.
-/
theorem no_injective_mul_map_to_semigroup_of_nonassociative
    {O A : Type*} [Mul O] [Semigroup A]
    (hnonassoc : ∃ x y z : O, (x * y) * z ≠ x * (y * z)) :
    ¬ ∃ φ : O → A,
        Function.Injective φ ∧
          (∀ x y : O, φ (x * y) = φ x * φ y) := by
  rintro ⟨φ, hinj, hmul⟩
  rcases hnonassoc with ⟨x, y, z, hxyz⟩
  exact hxyz
    (associative_of_injective_mul_map_to_semigroup
      φ hinj hmul x y z)

end InfoGeometry.Algebra

