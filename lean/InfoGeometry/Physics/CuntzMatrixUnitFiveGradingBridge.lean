import InfoGeometry.Algebra.CuntzMatrixUnits
import InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge
import InfoGeometry.Canonical.KantorPeirceFiveGrading
import Mathlib.Tactic

/-!
# Cuntz matrix-unit five-grade bridge

This owner is concrete: it works in the finite matrix-unit sector
`E_{ij} = S_i S_j†` of `CuntzAlg 3`.

The bridge proves the matrix-unit law, the induced commutator grading, and the
resulting five-grade weights on the hopping operators. It does not claim a
global TKK decomposition of the whole Cuntz algebra.
-/

namespace InfoGeometry.Physics.CuntzMatrixUnitFiveGrading

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzMatrixUnits

abbrev Cuntz3 := CuntzAlg 3

noncomputable abbrev hop := InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop
abbrev commutator := InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.commutator
abbrev colourWeight := InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.colourWeight
noncomputable abbrev gradingOp := InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.gradingOp
abbrev IsGradedComponent :=
  InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.IsGradedComponent

theorem hop_mul_hop (i j k l : Fin 3) :
    hop i j * hop k l = if j = k then hop i l else 0 := by
  exact InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_mul_hop i j k l

theorem gradingOp_comm_hop (i j : Fin 3) :
    commutator gradingOp (hop i j) =
      ((colourWeight i - colourWeight j : ℤ) : ℂ) • hop i j := by
  simpa using
    InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.gradingOp_comm_hop
      (i := i) (j := j)

theorem hop_zero_one_mem_grade_two :
    IsGradedComponent gradingOp 2 (hop 0 1) := by
  exact InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_zero_one_mem_grade_two

theorem hop_one_zero_mem_grade_neg_two :
    IsGradedComponent gradingOp (-2) (hop 1 0) := by
  exact InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_one_zero_mem_grade_neg_two

theorem hop_zero_two_mem_grade_one :
    IsGradedComponent gradingOp 1 (hop 0 2) := by
  exact InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_zero_two_mem_grade_one

theorem hop_two_zero_mem_grade_neg_one :
    IsGradedComponent gradingOp (-1) (hop 2 0) := by
  exact InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_two_zero_mem_grade_neg_one

theorem hop_two_two_mem_grade_zero :
    IsGradedComponent gradingOp 0 (hop 2 2) := by
  exact InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.hop_two_two_mem_grade_zero

theorem gradingOp_sq :
    gradingOp * gradingOp = hop 0 0 + hop 1 1 := by
  simpa using
    InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.gradingOp_sq

theorem gradingOp_cube :
    gradingOp * gradingOp * gradingOp = gradingOp := by
  simpa using
    InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.gradingOp_cube

end InfoGeometry.Physics.CuntzMatrixUnitFiveGrading
