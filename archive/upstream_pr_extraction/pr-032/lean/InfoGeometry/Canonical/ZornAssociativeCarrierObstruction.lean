import InfoGeometry.Algebra.AssociativityObstruction
import InfoGeometry.Canonical.SplitOctonionCircularChiralClosure

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.ZornAssociativeCarrierObstruction

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionCircularChiralClosure

/-!
The native Zorn product cannot be represented injectively and
multiplicatively in an associative semigroup.  This is a direct
specialization of the generic associativity obstruction to the repository's
actual split-octonion/Zorn carrier and its explicit circular associator.
-/

theorem no_injective_mul_map_zorn_to_associative_semigroup
    {A : Type*} [Semigroup A] :
    ¬ ∃ φ : ZornMatrix ℝ → A,
        Function.Injective φ ∧
          (∀ x y : ZornMatrix ℝ, φ (x * y) = φ x * φ y) := by
  apply no_injective_mul_map_to_semigroup_of_nonassociative
  exact ⟨sigmaPlus 0, sigmaPlus 1, sigmaPlus 2,
    nonassociative_circular_property⟩

end InfoGeometry.Canonical.ZornAssociativeCarrierObstruction
