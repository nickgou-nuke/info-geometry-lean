import InfoGeometry.Orthogonal.O55RealWittForm
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.O55MultigradedTwoBoundaryPristineChain

/-!
# Real `O(5,5)` / complex `D₅` multigraded closure

This owner records the exact relation between the real split form and the
complex root-space machinery used by the projective two-boundary readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.O55RealComplexClosure

open InfoGeometry.Orthogonal.O55D5
open InfoGeometry.Orthogonal.O55Witt
open InfoGeometry.Orthogonal.O55Real

/-- The real root belongs to `so(5,5)`, has the same contact degree, and
complexifies to the corresponding `D₅` root operator. -/
theorem real_complex_root_closure (r : Root) :
    IsRealSplitOrthogonal (realRootMatrix r) ∧
    realContactGradingMatrix * realRootMatrix r -
        realRootMatrix r * realContactGradingMatrix =
      (r.contactDegree : ℝ) • realRootMatrix r ∧
    complexifyMatrix (realRootMatrix r) = rootMatrix r ∧
    complexifyMatrix realContactGradingMatrix = contactGradingMatrix :=
  real_o55_complexification_packet r

/-- The real split form, complex root count, and collapsed five-grade
cardinalities in one theorem. -/
theorem real_o55_multigraded_dimension_packet :
    Fintype.card Root = 40 ∧
    contactGradeDimension (-2) = 1 ∧
    contactGradeDimension (-1) = 12 ∧
    contactGradeDimension 0 = 19 ∧
    contactGradeDimension 1 = 12 ∧
    contactGradeDimension 2 = 1 ∧
    contactGradeDimension (-2) + contactGradeDimension (-1) +
        contactGradeDimension 0 + contactGradeDimension 1 +
          contactGradeDimension 2 = 45 := by
  exact ⟨root_card,
    contactGradeDimension_neg_two,
    contactGradeDimension_neg_one,
    contactGradeDimension_zero,
    contactGradeDimension_one,
    contactGradeDimension_two,
    contact_five_grade_total_dimension⟩

end InfoGeometry.Canonical.O55RealComplexClosure

end noncomputable section

