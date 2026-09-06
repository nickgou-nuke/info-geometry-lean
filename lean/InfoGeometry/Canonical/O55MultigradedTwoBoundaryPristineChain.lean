import InfoGeometry.Orthogonal.O55D5RootMultigrading
import InfoGeometry.Orthogonal.O55WittRootRepresentation
import InfoGeometry.Orthogonal.O55WittCoordinateEquiv
import InfoGeometry.Orthogonal.O55ContactFiveGrading
import InfoGeometry.Orthogonal.O55ContactDirectSum
import InfoGeometry.Orthogonal.O55NativeTwoBoundaryReadout
import InfoGeometry.Orthogonal.O55ExistingPinGlideBridge

/-!
# `O(5,5)` multigraded two-boundary pristine chain

This capstone combines only proved mathematical layers:

* the forty `D₅` roots with their full `ℤ⁵` multidegrees;
* the contact collapse with dimensions `(1,12,19,12,1)`;
* the native Witt-skew Lie algebra and its `25+10+10` block coordinates;
* five spectral grade projectors whose sum is the identity;
* bracket-degree addition;
* exact two-boundary weight-selection rules;
* internal sheet exchange and its projective readout covariance;
* the separately existing `Pin(5,5)` null-pair and Klein-glide readouts.

The capstone does not identify a normalized matrix coefficient with a current,
identify the internal sheet exchange with an affine quotient generator, or
infer an antiunitary structure without an inner-product theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.O55MultigradedTwoBoundary

open InfoGeometry.Orthogonal.O55D5
open InfoGeometry.Orthogonal.O55Witt
open InfoGeometry.Orthogonal.O55WittCoordinates
open InfoGeometry.Orthogonal.O55Contact
open InfoGeometry.Orthogonal.O55ContactDirectSum
open InfoGeometry.Orthogonal.O55TwoBoundary
open InfoGeometry.Orthogonal.O55ExistingBridge
open InfoGeometry.Streaming.MultigradedTwoBoundarySelection
open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
open InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence
open InfoGeometry.Clifford.Clifford55

/-- Full algebraic closure packet for one pair of roots, one split-orthogonal
element, and one regular pair of boundary weights. -/
theorem o55_multigraded_two_boundary_pristine_chain
    (X : splitO55Lie)
    (B : O55BoundaryPair) (α β : Axis → ℂ)
    (hpre : IsRightWeight gradingOperator α B.pre)
    (hpost : IsLeftWeight gradingOperator β B.post)
    (r s : Root) :
    Fintype.card Root = 40 ∧
    contactGradeDimension (-2) = 1 ∧
    contactGradeDimension (-1) = 12 ∧
    contactGradeDimension 0 = 19 ∧
    contactGradeDimension 1 = 12 ∧
    contactGradeDimension 2 = 1 ∧
    Function.Bijective encode ∧
    IsSplitOrthogonal (rootMatrix r) ∧
    rootMatrix r ∈ multiWeightSpace
      (fun a => (r.multiDegree a : ℂ)) ∧
    rootMatrix r ∈ contactGradeSpace (r.contactDegree : ℂ) ∧
    rootMatrix r * rootMatrix s - rootMatrix s * rootMatrix r ∈
      contactGradeSpace ((r.contactDegree + s.contactDegree : ℤ) : ℂ) ∧
    (∀ k : ℤ, o55GradeProjection k X ∈ splitO55GradeSpace (k : ℂ)) ∧
    (∑ k ∈ contactDegrees, o55GradeProjection k X = X) ∧
    (rootReadout B r ≠ 0 →
      (fun a => (r.multiDegree a : ℂ)) =
        boundaryWeightDifference α β) ∧
    weakValue (exchangeBoundary B)
      (sheetConjugate (rootOperator r)) = rootReadout B r := by
  exact ⟨root_card,
    contactGradeDimension_neg_two,
    contactGradeDimension_neg_one,
    contactGradeDimension_zero,
    contactGradeDimension_one,
    contactGradeDimension_two,
    ⟨encode_injective, encode_surjective⟩,
    wittAdjoint_rootMatrix r,
    rootMatrix_mem_multiWeightSpace r,
    rootMatrix_mem_contactGradeSpace r,
    rootBracket_contactDegree r s,
    fun k => o55GradeProjection_mem k X,
    sum_o55GradeProjection X,
    fun hread => rootReadout_ne_zero_implies_multidegree
      B α β hpre hpost r hread,
    weakValue_exchangeBoundary B (rootOperator r)⟩

/-- Global finite-structure packet independent of a chosen boundary pair. -/
theorem o55_full_five_grade_structure_packet :
    Fintype.card Index = 10 ∧
    Fintype.card Root = 40 ∧
    contactGradeDimension (-2) = 1 ∧
    contactGradeDimension (-1) = 12 ∧
    contactGradeDimension 0 = 19 ∧
    contactGradeDimension 1 = 12 ∧
    contactGradeDimension 2 = 1 ∧
    contactGradeDimension (-2) + contactGradeDimension (-1) +
      contactGradeDimension 0 + contactGradeDimension 1 +
    contactGradeDimension 2 = 45 ∧
    Function.Bijective encode ∧
    (realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nPairProjective crosscapIndex) =
      nbarPairProjective crosscapIndex) := by
  exact ⟨by native_decide,
    root_card,
    contactGradeDimension_neg_two,
    contactGradeDimension_neg_one,
    contactGradeDimension_zero,
    contactGradeDimension_one,
    contactGradeDimension_two,
    contact_five_grade_total_dimension,
    ⟨encode_injective, encode_surjective⟩,
    native_pin_null_pair_swap⟩

/-- The full direct-sum, bracket, and root-selection mechanisms remain
separate but compatible theorem surfaces. -/
theorem o55_direct_sum_and_selection_packet
    (X : splitO55Lie)
    (B : O55BoundaryPair) (α β : Axis → ℂ)
    (hpre : IsRightWeight gradingOperator α B.pre)
    (hpost : IsLeftWeight gradingOperator β B.post)
    (r : Root) :
    (∑ k ∈ contactDegrees, o55GradeProjection k X = X) ∧
    (∀ k l, k ≠ l →
      o55GradeProjection k * o55GradeProjection l = 0) ∧
    (rootReadout B r ≠ 0 →
      (fun a => (r.multiDegree a : ℂ)) =
        boundaryWeightDifference α β) ∧
    (rootReadout B r ≠ 0 →
      (r.contactDegree : ℂ) =
        (β 0 - α 0) + (β 1 - α 1)) := by
  exact ⟨sum_o55GradeProjection X,
    fun k l h => o55GradeProjection_orthogonal h,
    fun h => rootReadout_ne_zero_implies_multidegree
      B α β hpre hpost r h,
    fun h => rootReadout_contact_degree_selection
      B α β hpre hpost r h⟩

end InfoGeometry.Canonical.O55MultigradedTwoBoundary

end noncomputable section
