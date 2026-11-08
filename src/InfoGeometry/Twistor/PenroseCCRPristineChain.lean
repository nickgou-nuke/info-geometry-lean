import InfoGeometry.Twistor.PenroseWittCompositionCompletion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.PenroseLegacyProductAudit

/-!
# Source-derived CCR triple, tested proposal, and explicit composition completion

The polynomial representation realizes the chapter's CCR. Their literal
alternating triple closes on signed real bi-twistors. The proposed cross
product then fails alternativity. A distinct multiplication transported
through the existing norm-compatible Witt map is genuinely alternative and
compositional. These are three different assertions, joined but not conflated.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseCCRPristineChain

open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PenrosePolynomialCCR
open InfoGeometry.Twistor.PenroseSignedCCRGeometry
open InfoGeometry.Twistor.PenroseLiteralCrossObstruction
open InfoGeometry.Twistor.PenroseWittCompositionCompletion

/-- Literal operator closure and the precise subsequent alternativity obstruction. -/
theorem source_triple_and_obstruction (x y z : TwistorCarrier) :
    operatorTriple (quantize 1 (signedPair x)) (quantize 1 (signedPair y))
        (quantize 1 (signedPair z)) = quantize 1 (signedPair (realTriple x y z)) ∧
      candidateProduct (1/2) testX (candidateProduct (1/2) testX testY) ≠
        candidateProduct (1/2) (candidateProduct (1/2) testX testX) testY := by
  exact ⟨realTriple_operator_closure x y z,
    candidate_not_left_alternative (1/2) (by norm_num)⟩

/-- A genuine chosen composition algebra on the same native quadratic carrier. -/
theorem chosen_composition_packet (x y : TwistorCarrier) :
    selectedMul chosenUnit x = x ∧ selectedMul x chosenUnit = x ∧
      selectedMul (selectedMul x x) y = selectedMul x (selectedMul x y) ∧
      selectedMul (selectedMul y x) x = selectedMul y (selectedMul x x) ∧
      twistorRealQuadraticForm (selectedMul x y) =
        twistorRealQuadraticForm x * twistorRealQuadraticForm y := by
  exact ⟨selectedMul_unit_left x, selectedMul_unit_right x,
    selectedMul_left_alternative x y, selectedMul_right_alternative x y,
    selectedMul_norm x y⟩

/-- The native completion is not a silent reinterpretation of the literal formula. -/
theorem source_candidate_and_completion_distinct (k : ℝ) :
    selectedMul testX testY ≠ candidateProduct k testX testY :=
  selectedMul_ne_literal_candidate k

end InfoGeometry.Twistor.PenroseCCRPristineChain

