import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# No faithful associative model for a genuinely nonassociative product

A faithful product-preserving map from a magma into an associative algebra
forces the source product to be associative.

This is the firewall needed for split-octonions/Zorn cells:

* Zorn split-octonions may be represented by coordinates or by multiplication
  operators;
* they may have norm/determinant models;
* but a faithful product-preserving embedding into an associative algebra would
  collapse the Zorn product to an associative one.

No wrappers. No structures. No `sorry`.
-/

namespace InfoGeometry.Algebra

/--
If a product-preserving map into an associative target is injective, then the
source product is associative.

This is the basic obstruction to treating a genuinely nonassociative algebra
as an associative matrix algebra with the same product.
-/
theorem associativity_forced_by_injective_mul_preserving_map_to_semigroup
    {O A : Type*}
    [Mul O] [Semigroup A]
    (f : O → A)
    (hf_mul : ∀ x y : O, f (x * y) = f x * f y)
    (hf_inj : Function.Injective f)
    (x y z : O) :
    (x * y) * z = x * (y * z) := by
  apply hf_inj
  calc
    f ((x * y) * z)
        = f (x * y) * f z := hf_mul (x * y) z
    _   = (f x * f y) * f z := by
            rw [hf_mul x y]
    _   = f x * (f y * f z) := by
            rw [mul_assoc]
    _   = f x * f (y * z) := by
            rw [hf_mul y z]
    _   = f (x * (y * z)) := by
            rw [hf_mul x (y * z)]

/--
Contrapositive form.

If the source product has one nonzero associator, then there is no injective
product-preserving map from it into any associative target.
-/
theorem no_faithful_mul_rep_to_associative_of_nonassoc
    {O A : Type*}
    [Mul O] [Semigroup A]
    (hnonassoc :
      ∃ x y z : O, (x * y) * z ≠ x * (y * z)) :
    ¬ ∃ f : O → A,
        (∀ x y : O, f (x * y) = f x * f y) ∧
        Function.Injective f := by
  rintro ⟨f, hf_mul, hf_inj⟩
  rcases hnonassoc with ⟨x, y, z, hneq⟩
  exact hneq
    (associativity_forced_by_injective_mul_preserving_map_to_semigroup
      f hf_mul hf_inj x y z)

end InfoGeometry.Algebra

